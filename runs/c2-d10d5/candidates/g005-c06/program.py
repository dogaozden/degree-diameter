import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined search engine.
#
# Vertices: A_{i,g} = i*G + g and B_{p,h} = (KB+p)*G + h, for base blocks
# i, p < KB and g, h in G = Z_m x| Z_k2. Layer l (0 <= l < DEG) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each layer is a perfect matching, so the
# graph is bipartite and d-regular when no duplicate edges occur.
#
# Left multiplication by G is an automorphism, so the diameter check needs
# only one BFS per block representative (2*KB BFS runs). Cost = unreached
# (representative, vertex) pairs + PEN * duplicate darts. Cost 0 means valid.
#
# Moves: voltage change and layer swap (for KB >= 2). A bandit over KB
# decides the budget per base size. Every success raises the target order.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXD 64
#define MAXB 4
#define PEN 1000L
#define ITERS 30000L
#define PATIENCE 5000L

static double g_budget = 1.0;
static clock_t g_t0;
static uint64_t g_rs = 88172645463325252ULL;

static int DEG = 1, DIAM = 1;
static int GM = 1, GK = 1, GN = 1;
static int KB = 1, NV = 2;
static int64_t PW[MAXK];

static int P[MAXD][MAXB];
static int S[MAXD][MAXB];
static int SI[MAXD][MAXB];
static int *NB = NULL;
static int *stamp = NULL;
static int *dist = NULL;
static int *queue = NULL;
static int curstamp = 0;

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_out = NULL;
static int g_have = 0;
static long trials_[MAXB + 1];
static long wins_[MAXB + 1];

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

/* element a*GK+b of Z_GM x| Z_GK, (a,b)(c,e) = (a + r^b c, b+e) */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = ((int64_t)a + PW[b] * (int64_t)c) % GM;
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

static int sample_group(long gmin, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 400; tries++) {
        int k2 = (rndf() < 0.03) ? 1 : KCH[rnd(21)];
        int64_t m = (gmin + k2 - 1) / k2 + (int64_t)rnd(3);
        if (m < 3) m = 3;
        if (m * (int64_t)k2 > 4000000LL) return 0;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.4) {
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

static void build_trial(int kb) {
    KB = kb;
    NV = 2 * KB * GN;
    NB = malloc(sizeof(int) * (size_t)DEG * (size_t)NV);
    stamp = calloc((size_t)NV, sizeof(int));
    dist = malloc(sizeof(int) * (size_t)NV);
    queue = malloc(sizeof(int) * (size_t)NV);
    curstamp = 0;
}

static void free_trial(void) {
    free(NB);
    free(stamp);
    free(dist);
    free(queue);
    NB = NULL;
    stamp = NULL;
    dist = NULL;
    queue = NULL;
}

/* Rewrite the neighbour entries touched by dart (l, i): A-block i and B-block P[l][i]. */
static void set_dart(int l, int i) {
    int p = P[l][i], s = S[l][i], si = SI[l][i];
    int *nb = NB + (size_t)l * NV;
    int ai = i * GN, bp = (KB + p) * GN;
    for (int g = 0; g < GN; g++) {
        nb[ai + g] = bp + gmul(g, s);
        nb[bp + g] = ai + gmul(g, si);
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (P[l][i] == P[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static int bfs_count(int start) {
    if (curstamp >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)NV);
        curstamp = 0;
    }
    curstamp++;
    int head = 0, tail = 0;
    queue[tail++] = start;
    stamp[start] = curstamp;
    dist[start] = 0;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        for (int l = 0; l < DEG; l++) {
            int w = NB[(size_t)l * NV + v];
            if (stamp[w] != curstamp) {
                stamp[w] = curstamp;
                dist[w] = dv + 1;
                queue[tail++] = w;
            }
        }
    }
    return tail;
}

static long evaluate(void) {
    long cost = 0;
    for (int b = 0; b < 2 * KB; b++) {
        int reached = bfs_count(b * GN);
        cost += (long)(NV - reached);
    }
    cost += PEN * dupcount();
    return cost;
}

static void random_init(void) {
    int tmp[MAXB];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < KB; i++) tmp[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = (int)rnd((uint64_t)(i + 1));
            int t = tmp[i];
            tmp[i] = tmp[j];
            tmp[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            P[l][i] = tmp[i];
            S[l][i] = (int)rnd((uint64_t)GN);
            SI[l][i] = ginv(S[l][i]);
        }
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < KB; i++)
            set_dart(l, i);
}

static long sa_run(long iters, long patience) {
    random_init();
    long cost = evaluate();
    long c0 = cost > 1 ? cost : 1;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && elapsed() > g_budget) break;
        double frac = (double)t / (double)iters;
        double temp = 0.3 + 0.01 * (double)c0 * (1.0 - frac);

        if (KB >= 2 && rndf() < 0.25) {
            int l = (int)rnd((uint64_t)DEG);
            int i1 = (int)rnd((uint64_t)KB);
            int i2 = (int)rnd((uint64_t)(KB - 1));
            if (i2 >= i1) i2++;
            int tp = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = tp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = evaluate();
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                tp = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = tp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = (int)rnd((uint64_t)DEG);
            int i = (int)rnd((uint64_t)KB);
            int old = S[l][i], oldi = SI[l][i];
            int x;
            do {
                x = (int)rnd((uint64_t)GN);
            } while (x == old);
            S[l][i] = x;
            SI[l][i] = ginv(x);
            set_dart(l, i);
            long c2 = evaluate();
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                S[l][i] = old;
                SI[l][i] = oldi;
                set_dart(l, i);
            }
        }
    }
    return cost;
}

static void store_result(void) {
    long M = (long)KB * GN * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)M);
    if (!e) return;
    long c = 0;
    for (int u = 0; u < KB * GN; u++) {
        for (int l = 0; l < DEG; l++) {
            e[2 * c] = u;
            e[2 * c + 1] = NB[(size_t)l * NV + u];
            c++;
        }
    }
    free(g_out);
    g_out = e;
    g_best_m = M;
    g_best_n = NV;
    g_have = 1;
}

static int pick_kb(void) {
    if (rndf() < 0.2) return 1 + (int)rnd((uint64_t)MAXB);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXB; k++) {
        double s = ((double)wins_[k] + 1.0) / ((double)trials_[k] + 2.0) + 0.02 * rndf();
        if (s > bs) {
            bs = s;
            bk = k;
        }
    }
    return bk;
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

    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    g_best_n = min_n;
    while (elapsed() < g_budget) {
        int kb = pick_kb();
        long base = g_best_n / (2L * kb);
        long gmin = base + 1 + (long)rnd((uint64_t)(base / 8 + 2));
        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(gmin, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (GN < 3) continue;
        if (2L * kb * GN <= g_best_n) continue;
        trials_[kb]++;
        build_trial(kb);
        long cost = sa_run(ITERS, PATIENCE);
        if (cost == 0) {
            wins_[kb]++;
            store_result();
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

def _c_search(d, D, seed, budget, min_n, timeout):
    """Run the combined lift engine; returns (n, edges), or (0, []) if nothing beat min_n."""
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

    # Main search: lifts over semidirect products, started above the best order so far.
    c_budget = deadline - time.monotonic()
    if c_budget > 0.5 and d <= 60:
        remaining = time_limit - (time.monotonic() - start)
        timeout = max(1.0, min(c_budget + 4.0, remaining - 2.0))
        try:
            n, e = _c_search(d, D, seed, c_budget, best_n, timeout)
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
