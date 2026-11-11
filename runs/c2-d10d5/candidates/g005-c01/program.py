import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction family: multi-orbit bi-Cayley graphs (circulant base).
#
# Vertices: A_{i,g} and B_{j,h} for i, j in 0..NA-1 and g, h in G, where
# G = Z_m x| Z_k2. A_{i,g} is joined to B_{j,g*s} for each slot s of A-orbit i
# whose target orbit is j = (i + off) mod NA. The offsets form a circulant
# pattern: the number of slots with offset o is CVC[o], with sum(CVC) = d.
# Every A-orbit and every B-orbit then has degree exactly d.
#
# Left multiplication by G is an automorphism that fixes each orbit, so the
# diameter is at most D iff BFS from one representative of each orbit reaches
# everything within D steps. The cost is the total number of unreached
# (representative, vertex) pairs over the 2*NA representatives. Simulated
# annealing moves one connection element at a time. The order is 2*NA*|G|.
# NA = 1 is the single-orbit bi-Cayley search, so it stays a special case.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXA 3
#define MAXD 128
#define ITERS 30000
#define PATIENCE 4000

static double g_budget = 1.0;
static clock_t g_t0;
static uint64_t g_rs = 88172645463325252ULL;

static int DEG = 1, DIAM = 1;
static int NA = 1;
static int CVC[MAXA];
static int OFF[MAXD];
static int GM = 1, GK = 1, GN = 1;
static int64_t PW[MAXK];
static int V = 0;

static int *Sel = NULL;   /* Sel[i*DEG+q]: connection element of slot q of A-orbit i */
static int *adj = NULL;   /* adj[v*DEG+r]: r-th neighbour of vertex v */
static int *cnt = NULL;
static int *dist = NULL;
static int *queue = NULL;

static int g_have = 0;
static long g_out_n = 0;
static long g_out_m = 0;
static int *g_out = NULL;

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

/* element a*GK+b of Z_GM x| Z_GK, (a,b)(c,e) = (a + r^b c, b+e) */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
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

static const int KCH[21] = {2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 30, 40, 50, 60};

/* Sample Z_m x| Z_k2 with m*k2 >= target. */
static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 400; tries++) {
        int k2 = (rndf() < 0.03) ? 1 : KCH[rnd(21)];
        int64_t m = (target + k2 - 1) / k2 + (int64_t)rnd(3);
        if (m < 4) m = 4;
        if (m > 1000000) continue;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.5) {
            r = m - 1;
        } else {
            int found = 0;
            for (int t = 0; t < 80; t++) {
                int64_t c = 1 + (int64_t)rnd((uint64_t)(m - 2));
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
    Sel = malloc(sizeof(int) * (size_t)NA * (size_t)DEG);
    adj = malloc(sizeof(int) * (size_t)V * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)V);
    dist = malloc(sizeof(int) * (size_t)V);
    queue = malloc(sizeof(int) * (size_t)V);
    memset(dist, 0xff, sizeof(int) * (size_t)V);
}

static void free_trial(void) {
    free(Sel);
    free(adj);
    free(cnt);
    free(dist);
    free(queue);
    Sel = NULL;
    adj = NULL;
    cnt = NULL;
    dist = NULL;
    queue = NULL;
}

/* A-vertex ids: i*GN+g. B-vertex ids: NA*GN + j*GN + h. */
static void rebuild(void) {
    int NB = NA * GN;
    memset(cnt, 0, sizeof(int) * (size_t)V);
    for (int i = 0; i < NA; i++) {
        for (int g = 0; g < GN; g++) {
            int v = i * GN + g;
            for (int q = 0; q < DEG; q++) {
                int j = (i + OFF[q]) % NA;
                int h = gmul(g, Sel[i * DEG + q]);
                int w = NB + j * GN + h;
                adj[(size_t)v * DEG + q] = w;
                adj[(size_t)w * DEG + cnt[w]] = v;
                cnt[w]++;
            }
        }
    }
}

/* BFS from start up to DIAM; returns the number of vertices reached. */
static int bfs(int start) {
    int head = 0, tail = 0;
    queue[tail++] = start;
    dist[start] = 0;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        const int *row = adj + (size_t)v * DEG;
        for (int r = 0; r < DEG; r++) {
            int w = row[r];
            if (dist[w] < 0) {
                dist[w] = dv + 1;
                queue[tail++] = w;
            }
        }
    }
    for (int i = 0; i < tail; i++) dist[queue[i]] = -1;
    return tail;
}

/* Sum over orbit representatives of unreached vertices; 0 iff diameter <= DIAM. */
static long evaluate(void) {
    long cost = 0;
    for (int i = 0; i < NA; i++) cost += (long)(V - bfs(i * GN));
    for (int j = 0; j < NA; j++) cost += (long)(V - bfs(NA * GN + j * GN));
    return cost;
}

/* True if x clashes with another slot of the same offset (same target orbit) in row i,
   among slots q2 < upto, q2 != q. */
static int clash(int i, int q, int x, int upto) {
    for (int q2 = 0; q2 < upto; q2++) {
        if (q2 != q && OFF[q2] == OFF[q] && Sel[i * DEG + q2] == x) return 1;
    }
    return 0;
}

static long sa_run(long iters, long patience) {
    for (int i = 0; i < NA; i++) {
        for (int q = 0; q < DEG; q++) {
            int x;
            do {
                x = (int)rnd((uint64_t)GN);
            } while (clash(i, q, x, q));
            Sel[i * DEG + q] = x;
        }
    }
    rebuild();
    long cost = evaluate();
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && elapsed() > g_budget) break;
        double frac = (double)t / (double)iters;
        double temp = 0.5 + 0.02 * (double)cost * (1.0 - frac);
        int i = (int)rnd((uint64_t)NA);
        int q = (int)rnd((uint64_t)DEG);
        int idx = i * DEG + q;
        int old = Sel[idx];
        int x;
        do {
            x = (int)rnd((uint64_t)GN);
        } while (clash(i, q, x, DEG));
        Sel[idx] = x;
        rebuild();
        long c2 = evaluate();
        if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            Sel[idx] = old;
            rebuild();
        }
    }
    return cost;
}

static void store_result(void) {
    long M = (long)NA * GN * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)M);
    if (!e) return;
    long c = 0;
    for (int i = 0; i < NA; i++) {
        for (int g = 0; g < GN; g++) {
            int v = i * GN + g;
            for (int q = 0; q < DEG; q++) {
                e[2 * c] = v;
                e[2 * c + 1] = adj[(size_t)v * DEG + q];
                c++;
            }
        }
    }
    free(g_out);
    g_out = e;
    g_out_m = M;
    g_out_n = V;
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

    long best_total = min_n;
    while (elapsed() < g_budget) {
        NA = 1 + (int)rnd((uint64_t)MAXA);
        for (int o = 0; o < MAXA; o++) CVC[o] = 0;
        for (int k = 0; k < DEG; k++) CVC[rnd((uint64_t)NA)]++;
        int qq = 0;
        for (int o = 0; o < NA; o++)
            for (int t = 0; t < CVC[o]; t++) OFF[qq++] = o;

        /* need 2*NA*GN > best_total */
        long need = best_total / (2L * NA) + 1;
        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(need, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (GN <= DEG + 1) continue;
        V = 2 * NA * GN;
        alloc_trial();
        long cost = sa_run(ITERS, PATIENCE);
        if (cost == 0) {
            store_result();
            best_total = V;
        }
        free_trial();
    }

    if (!g_have) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_out_n, g_out_m);
    for (long c = 0; c < g_out_m; c++) {
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

def _c_multiorbit(d, D, seed, budget, min_n, timeout):
    """Run the multi-orbit bi-Cayley engine; returns (n, edges), or (0, []) if nothing beat min_n."""
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

    # Main search: multi-orbit bi-Cayley graphs, started above the best order so far.
    c_budget = deadline - time.monotonic()
    if c_budget > 0.5:
        timeout = max(1.0, min(c_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
        try:
            n, e = _c_multiorbit(d, D, seed, c_budget, best_n, timeout)
            consider(n, e)
        except Exception:
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
