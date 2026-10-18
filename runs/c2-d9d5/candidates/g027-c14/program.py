"""Affine-group lifts with two base fibres (bi-Cayley family) for the bipartite degree-diameter problem.

Parent idea kept: the affine group F_q x| H (H = subgroup of F_q^* of order c, c | q-1, c >= 1),
used as a Haar-type voltage lift.

New idea in this version: a two-fibre base graph. Each side gets K = 2 base vertices,
L_0, L_1 on the left and R_0, R_1 on the right. The base multigraph is d-regular with
multiplicities [[a, d-a], [d-a, a]] for 1 <= a <= d/2, so it has 2d darts. Each dart carries
a group element g, and the lift joins L_i(x) to R_j(x*g) for every x in G. Distinct darts
in the same block (i, j) must carry distinct g, which keeps the graph simple. The result is
d-regular, bipartite, and has 4|G| vertices. The left translations x -> h*x are automorphisms
that act transitively on each fibre, so diameter <= D is checked with four BFS runs, from
L_0(e), L_1(e), R_0(e), R_1(e). The K = 1 Haar family from the parent is kept as well.

Search flow in C: stage A binary-searches the K = 1 candidates, so the parent's family
still gets its share of time. Stage B then searches the K = 2 candidates above the best
order found so far. Leftover time in each stage goes to the next few orders above the best.

Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d}
fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Affine-group lift search with K = 1 (Haar) and K = 2 (two-fibre bi-Cayley) families.
 * Usage: prog d D seed time_limit Vlo Vhi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 8192
#define MAXD 32
#define MAXE 64
#define MAXV (4 * MAXN)
#define MAXCAND 20000

typedef struct { int q, p, k, c, K, a, N, V; } Cand;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ dart state */

/* K fibres per side, E darts. Dart e joins L_{pI[e]}(x) to R_{pJ[e]}(x * Gd[e]). */
static int K, E;
static int pI[MAXE], pJ[MAXE], Gd[MAXE], Gi[MAXE];
static int bestGd[MAXE];
static int fwdE[MAXE][MAXN], bwdE[MAXE][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* K = 1: d darts in one block (Haar lift).
 * K = 2: block multiplicities [[a, d-a], [d-a, a]], 2d darts in total. */
static void set_pattern(int Kk, int a) {
    K = Kk;
    E = 0;
    if (Kk == 1) {
        for (int t = 0; t < d; t++) { pI[E] = 0; pJ[E] = 0; E++; }
    } else {
        for (int t = 0; t < a; t++)     { pI[E] = 0; pJ[E] = 0; E++; }
        for (int t = 0; t < d - a; t++) { pI[E] = 0; pJ[E] = 1; E++; }
        for (int t = 0; t < d - a; t++) { pI[E] = 1; pJ[E] = 0; E++; }
        for (int t = 0; t < a; t++)     { pI[E] = 1; pJ[E] = 1; E++; }
    }
    for (int e = 0; e < E; e++) Gd[e] = -1;
}

static void set_dart(int e, int x) {
    Gd[e] = x;
    Gi[e] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdE[e][g] = gmul(g, x);
        bwdE[e][g] = gmul(g, Gi[e]);
    }
}

/* 1 if assigning x to dart e would duplicate an edge: another dart in the same block has x. */
static int conflict(int e, int x) {
    for (int f = 0; f < E; f++)
        if (f != e && Gd[f] == x && pI[f] == pI[e] && pJ[f] == pJ[e]) return 1;
    return 0;
}

/* Vertices: L_i(x) = i*N + x, R_j(y) = K*N + j*N + y. */
static int bfs_count(int src) {
    int N = GN, VK = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < VK) {
                int i = v / N, x = v - i * N;
                for (int e = 0; e < E; e++) {
                    if (pI[e] != i) continue;
                    int u = VK + pJ[e] * N + fwdE[e][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - VK;
                int j = w / N, y = w - j * N;
                for (int e = 0; e < E; e++) {
                    if (pJ[e] != j) continue;
                    int u = pI[e] * N + bwdE[e][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Fibre transitivity: one BFS per base vertex, from the identity of that fibre. */
static long cover_cost(void) {
    int N = GN, V = 2 * K * N;
    long c = 0;
    for (int i = 0; i < K; i++) {
        c += (long)(V - bfs_count(i * N));
        c += (long)(V - bfs_count(K * N + i * N));
    }
    return c;
}

static int random_init(void) {
    for (int e = 0; e < E; e++) Gd[e] = -1;
    for (int e = 0; e < E; e++) {
        int x, tries = 0;
        do { x = rndint(GN); tries++; } while (conflict(e, x) && tries < 100000);
        if (tries >= 100000) return 0;
        set_dart(e, x);
    }
    return 1;
}

/* Simulated annealing over the dart labels. Returns 1 at cost 0 (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    const int iters = 8000;
    int N = GN;
    while (now() < until) {
        if (!random_init()) return 0;
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(E);
            int x;
            do { x = rndint(N); } while (conflict(e, x));
            int old = Gd[e];
            set_dart(e, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(e, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best-so-far bookkeeping */

static int bestV = 0;
static Cand bestC;
static int bestE;

static void record(const Cand *cd) {
    if (cd->V > bestV) {
        bestV = cd->V;
        bestC = *cd;
        bestE = E;
        memcpy(bestGd, Gd, sizeof(int) * (size_t)E);
    }
}

static int probe(const Cand *cd, double until) {
    setup_group(cd->q, cd->p, cd->k, cd->c);
    set_pattern(cd->K, cd->a);
    return search_group(until);
}

/* Binary search over list[lo..hi] (sorted by V), then leftover time above the last success. */
static void stage(Cand *list, int lo, int hi, double until) {
    int a = lo, b = hi, bi = -1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = until - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (probe(&list[mid], now() + slice)) {
            record(&list[mid]);
            bi = mid;
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    int idx = bi < 0 ? lo : bi + 1;
    int fails = 0;
    while (idx <= hi && now() < until && fails < 2) {
        if (list[idx].V <= bestV) { idx++; continue; }
        double rem = until - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (probe(&list[idx], now() + slice)) {
            record(&list[idx]);
            bi = idx;
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }
}

static void print_result(void) {
    int N = GN, VK = K * N;
    printf("%d %d\n", 2 * VK, E * N);
    for (int e = 0; e < E; e++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", pI[e] * N + x, VK + pJ[e] * N + fwdE[e][x]);
}

static int cmpc(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    return (a->V > b->V) - (a->V < b->V);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    static Cand candA[MAXCAND], candB[MAXCAND];
    int nA = 0, nB = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N > MAXN || N < d) continue;
            int V1 = 2 * N;
            if (V1 >= vlo && V1 <= vhi && nA < MAXCAND) {
                Cand cd = {q, p, k, c, 1, 0, N, V1};
                candA[nA++] = cd;
            }
            int V2 = 4 * N;
            if (V2 >= vlo && V2 <= vhi) {
                for (int a = 1; a <= d / 2; a++) {
                    if (nB >= MAXCAND) break;
                    Cand cd = {q, p, k, c, 2, a, N, V2};
                    candB[nB++] = cd;
                }
            }
        }
    }
    if (nA + nB == 0) { printf("0 0\n"); return 0; }
    qsort(candA, (size_t)nA, sizeof(Cand), cmpc);
    qsort(candB, (size_t)nB, sizeof(Cand), cmpc);

    /* Stage A: K = 1 (parent's Haar family), about 45% of the time. */
    if (nA > 0) {
        double untilA = now() + 0.45 * (t_end - now());
        stage(candA, 0, nA - 1, untilA);
    }

    /* Stage B: K = 2 two-fibre lifts, only orders above the best so far, using the rest. */
    if (nB > 0) {
        int lo = 0;
        while (lo < nB && candB[lo].V <= bestV) lo++;
        if (lo < nB) stage(candB, lo, nB - 1, t_end);
    }

    if (bestV <= 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestC.q, bestC.p, bestC.k, bestC.c);
    set_pattern(bestC.K, bestC.a);
    for (int e = 0; e < bestE; e++) set_dart(e, bestGd[e]);
    print_result();
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Affine-group lifts (K = 1 Haar and K = 2 two-fibre). Search over vertex counts V.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        vlo = max(best[0] + 1, mb // 8)
        vhi = mb
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
