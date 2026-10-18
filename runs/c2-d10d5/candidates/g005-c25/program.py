import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts over small groups.
#
# Vertices: A_{i,g} and B_{j,h} for i, j < P and g, h in G (|G| = GN).
# Slot l (0 <= l < d) is a perfect matching between all A and all B vertices:
#     A_{i,g} -- B_{SIG[l][i], g * VOL[l][i]}.
# SIG[l] is a permutation of the P orbits, so every vertex has degree d.
# Left multiplication by G is an automorphism that fixes each orbit, so
# the diameter check only needs BFS from A_{i,1} (i < P) and B_{j,1} (j < P).
#
# P = 1 is the single-orbit bi-Cayley family. P >= 2 gives a different family
# with 2PG vertices. The annealer minimises the number of (representative,
# vertex) pairs at distance > D. Each success raises the target order.
# Safe baselines are kept as fallbacks and every output is checked by lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXD 40
#define MAXP 6
#define ITERS 60000L
#define PATIENCE 9000L

#define VA(i, g) ((i) * GN + (g))
#define VB(j, h) (((P) + (j)) * GN + (h))

static double g_budget = 1.0;
static clock_t g_t0;
static uint64_t g_rs = 88172645463325252ULL;

static int DEG = 1, DIAM = 1, P = 1;
static int GM = 1, GK = 1, GN = 1, NV = 2;
static int64_t PW[MAXK];

static int SIG[MAXD][MAXP];   /* SIG[l][i]: B-orbit matched to A-orbit i in slot l */
static int VOL[MAXD][MAXP];   /* VOL[l][i]: voltage of that matching */
static int *adj = NULL;       /* adj[v*DEG + l]: neighbour of v in slot l */
static int *dist = NULL;      /* size NV, all -1 between BFS runs */
static int *queue = NULL;     /* size NV */

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_out = NULL;
static int g_have = 0;

static const int KCH[21] = {2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 30, 40, 50, 60};

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_GM x| Z_GK, element a*GK+b, (a,b)(c,e) = (a + r^b c, b+e). Identity is 0. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (-(PW[nb] * (int64_t)a)) % GM;
    if (t < 0) t += GM;
    return (int)(t * GK + nb);
}

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GN = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = (p * r) % m;
    }
}

/* Sample Z_m x| Z_k2 with m*k2 >= target. */
static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 400; tries++) {
        int k2 = (rndf() < 0.03) ? 1 : KCH[rnd(21)];
        int64_t m = (target + k2 - 1) / k2 + (int64_t)rnd(3);
        if (m < 4) m = 4;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.5) {
            r = m - 1;
        } else {
            int found = 0;
            for (int t = 0; t < 80; t++) {
                int64_t c = 2 + (int64_t)rnd((uint64_t)(m - 3));
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static void alloc_trial(void) {
    adj = malloc(sizeof(int) * (size_t)NV * (size_t)DEG);
    dist = malloc(sizeof(int) * (size_t)NV);
    queue = malloc(sizeof(int) * (size_t)NV);
    memset(dist, 0xff, sizeof(int) * (size_t)NV);
}

static void free_trial(void) {
    free(adj);
    free(dist);
    free(queue);
    adj = NULL;
    dist = NULL;
    queue = NULL;
}

/* Random permutation of B-orbits for each slot. */
static void sample_perms(void) {
    for (int l = 0; l < DEG; l++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int k = (int)rnd((uint64_t)(i + 1));
            int t = perm[i];
            perm[i] = perm[k];
            perm[k] = t;
        }
        for (int i = 0; i < P; i++) SIG[l][i] = perm[i];
    }
}

/* Voltage x is allowed at (l, i) if no other slot with the same B-orbit uses x. */
static int ok_val(int l, int i, int x) {
    for (int l2 = 0; l2 < DEG; l2++) {
        if (l2 == l) continue;
        if (SIG[l2][i] == SIG[l][i] && VOL[l2][i] == x) return 0;
    }
    return 1;
}

/* Write the perfect matching of slot l between A-orbit i and B-orbit SIG[l][i]. */
static void set_match(int l, int i) {
    int s = VOL[l][i];
    int j = SIG[l][i];
    for (int g = 0; g < GN; g++) {
        int a = VA(i, g);
        int b = VB(j, gmul(g, s));
        adj[(size_t)a * DEG + l] = b;
        adj[(size_t)b * DEG + l] = a;
    }
}

static void build_all(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < P; i++)
            set_match(l, i);
}

/* BFS from start up to DIAM. Returns the number of vertices reached. */
static int bfs_count(int start) {
    int head = 0, tail = 0;
    queue[tail++] = start;
    dist[start] = 0;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        const int *nb = adj + (size_t)v * DEG;
        for (int l = 0; l < DEG; l++) {
            int w = nb[l];
            if (dist[w] < 0) {
                dist[w] = dv + 1;
                queue[tail++] = w;
            }
        }
    }
    for (int k = 0; k < tail; k++) dist[queue[k]] = -1;
    return tail;
}

/* Zero iff diameter <= DIAM (by vertex-transitivity within each orbit). */
static long evaluate(void) {
    long cost = 0;
    for (int i = 0; i < P; i++) cost += (long)(NV - bfs_count(VA(i, 0)));
    for (int j = 0; j < P; j++) cost += (long)(NV - bfs_count(VB(j, 0)));
    return cost;
}

static long sa_run(long iters, long patience) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < P; i++)
            VOL[l][i] = -1;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < P; i++) {
            int x;
            do {
                x = (int)rnd((uint64_t)GN);
            } while (!ok_val(l, i, x));
            VOL[l][i] = x;
        }
    }
    build_all();
    long cost = evaluate();
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > g_budget) break;
        double frac = (double)t / (double)iters;
        double temp = 0.3 + 0.03 * (double)cost * (1.0 - frac);
        int l = (int)rnd((uint64_t)DEG);
        int i = (int)rnd((uint64_t)P);
        int old = VOL[l][i];
        int x;
        do {
            x = (int)rnd((uint64_t)GN);
        } while (x == old || !ok_val(l, i, x));
        VOL[l][i] = x;
        set_match(l, i);
        long c2 = evaluate();
        if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            VOL[l][i] = old;
            set_match(l, i);
        }
    }
    return cost;
}

static void store_result(void) {
    long M = (long)P * GN * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)M);
    if (!e) return;
    long c = 0;
    for (int v = 0; v < P * GN; v++) {
        for (int l = 0; l < DEG; l++) {
            e[2 * c] = v;
            e[2 * c + 1] = adj[(size_t)v * DEG + l];
            c++;
        }
    }
    free(g_out);
    g_out = e;
    g_best_m = M;
    g_best_n = (long)NV;
    g_have = 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    g_rs ^= sd * 0x9E3779B97F4A7C15ULL;
    if (!g_rs) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    long min_n = atol(argv[5]);
    g_t0 = clock();

    if (DEG < 1 || DIAM < 1 || DEG > MAXD) {
        printf("0 0\n");
        return 0;
    }

    g_best_n = min_n;
    while (elapsed() < g_budget) {
        double u = rndf();
        int p = u < 0.35 ? 1 : (u < 0.6 ? 2 : (u < 0.8 ? 3 : (u < 0.92 ? 4 : 5)));
        if (p > MAXP) p = MAXP;
        /* Need 2*p*GN > min_n. */
        long need = min_n / (2L * p) + 1;
        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(need, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (GN <= DEG) continue;
        P = p;
        NV = 2 * P * GN;
        alloc_trial();
        sample_perms();
        long cost = sa_run(ITERS, PATIENCE);
        if (cost == 0) {
            store_result();
            min_n = (long)NV;
        }
        free_trial();
    }

    if (!g_have) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_best_n, g_best_m);
    for (long c = 0; c < g_best_m; c++) {
        printf("%d %d\n", g_out[2 * c], g_out[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _c_multilift(d, D, seed, budget, min_n, timeout):
    """Run the multi-orbit lift engine; returns (n, edges), or (0, []) if nothing beat min_n."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n], timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: multi-orbit voltage lifts, started above the best order so far.
    c_budget = deadline - time.monotonic()
    if c_budget > 0.5:
        timeout = max(1.0, min(c_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
        try:
            n, e = _c_multilift(d, D, seed, c_budget, best_n, timeout)
            consider(n, e)
        except Exception:
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
