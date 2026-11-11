"""Voltage-lift search over small groups for the bipartite degree-diameter problem.

Change from the parent: the parent searched only Haar graphs (one base edge
class) over Z_M x| Z_K and affine groups F_q x| H. This version searches
general base-graph voltage lifts. The base is a d-regular bipartite multigraph
on T + T vertices (T = 1..4), each dart carries a voltage in a finite group G
of order N, and the lift has 2*T*N vertices. Left multiplication by G is an
automorphism, so the diameter check needs only 2T BFS runs, one from each
fibre identity. Simulated annealing moves voltages and switches dart endpoints
to minimise the number of unreached (vertex, source) pairs. Candidates are
tried in ascending order of order n, starting near the record, with random
order inside each n level and repeated passes while time remains.

Fallbacks: projective-plane incidence graphs, the Araujo-Lopez graph, the
generalized quadrangle for D = 4, and K_{d,d}. Every result is checked with
lib.is_valid before it is returned.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite voltage-lift search over groups of order N = M*K (semidirect
 * Z_M x| Z_K) and affine groups F_q x| H.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the vertex count n = 2*T*N of the lift.
 * Output: "n m" then m lines "u v", or "0 0".
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
#define MAXG 2048
#define MAXT 4
#define MAXDD 32
#define MAXNR (MAXT * MAXDD)
#define MAXV (2 * MAXT * MAXG)
#define MAXCAND 150000
#define MAXK 40

typedef struct {
    int n, N, t, type;
    int M, K, r;
    int q, p, k, c;
    unsigned key;
} Cand;

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

/* ------------------------------------------------------------ group tables */

static int GN, GC;
static unsigned short GT[MAXG * MAXG];   /* GT[x*GN + y] = x*y, identity = 0 */
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int PWK[MAXK + 1];

static inline int gmul_aff(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

/* Affine group F_q x| H, H = subgroup of order c in F_q^*. Element (a, h_j) = a*c + j. */
static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
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
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            GT[x * GN + y] = (unsigned short)gmul_aff(x, y);
}

/* Semidirect Z_M x| Z_K with multiplier r (r^K = 1 mod M). Element (a, b) = a*K + b,
 * product (a, b)(c, e) = (a + r^b c, b + e). Identity = 0. */
static void setup_semi(int M, int K, int r) {
    GN = M * K;
    GC = 0;
    PWK[0] = 1 % M;
    for (int b = 1; b < K; b++) PWK[b] = (int)(((long)PWK[b - 1] * r) % M);
    for (int x = 0; x < GN; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < GN; y++) {
            int c = y / K, e = y % K;
            int na = (int)((a + (long)PWK[b] * c) % M);
            int ne = (b + e) % K;
            GT[x * GN + y] = (unsigned short)(na * K + ne);
        }
    }
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void add_cand(int N, int t, int type, int M, int K, int r,
                     int q, int p, int k, int c) {
    if (nc >= MAXCAND) return;
    Cand *x = &cand[nc++];
    x->n = 2 * t * N;
    x->N = N;
    x->t = t;
    x->type = type;
    x->M = M;
    x->K = K;
    x->r = r;
    x->q = q;
    x->p = p;
    x->k = k;
    x->c = c;
    x->key = (unsigned)rnd();
}

static void enumerate_cands(int lo, int hi) {
    int Nlo = (lo + 2 * MAXT - 1) / (2 * MAXT);
    if (Nlo < d) Nlo = d;
    int Nhi = hi / 2;
    if (Nhi > MAXG) Nhi = MAXG;
    for (int N = Nlo; N <= Nhi; N++) {
        for (int K = 1; K <= MAXK && K <= N; K++) {
            if (N % K) continue;
            int M = N / K;
            for (int r = 0; r < M; r++) {
                if (gcd_i(r, M) != 1) continue;
                if (pw_mod(r, K, M) != 1 % M) continue;
                for (int t = 1; t <= MAXT; t++) {
                    int n = 2 * t * N;
                    if (n >= lo && n <= hi) add_cand(N, t, 0, M, K, r, 0, 0, 0, 0);
                }
            }
        }
    }
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N < Nlo || N > Nhi) continue;
            for (int t = 1; t <= MAXT; t++) {
                int n = 2 * t * N;
                if (n >= lo && n <= hi) add_cand(N, t, 1, 0, 0, 0, q, p, k, c);
            }
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->n != y->n) return x->n < y->n ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ lift state */

static int BT, NDART;
static int du[MAXNR], dv[MAXNR], dg[MAXNR];      /* dart k: left u, right v, voltage g */
static int su[MAXNR], sv[MAXNR], sg[MAXNR];      /* backup */
static int Bu[MAXNR], Bv[MAXNR], Bg[MAXNR];      /* best found */
static int adj[MAXV][MAXDD], acnt[MAXV];
static int vis[MAXV], que[MAXV], vstamp = 0;

static void setup_cand(const Cand *c) {
    BT = c->t;
    NDART = BT * d;
    if (c->type == 0) setup_semi(c->M, c->K, c->r);
    else setup_affine(c->q, c->p, c->k, c->c);
}

static int valid_state(void) {
    for (int i = 0; i < NDART; i++)
        for (int j = i + 1; j < NDART; j++)
            if (du[i] == du[j] && dv[i] == dv[j] && dg[i] == dg[j]) return 0;
    return 1;
}

/* Random start: each right vertex used d times, row sums d, parallel darts
 * with distinct voltages (repaired by re-drawing voltages). */
static int init_state(void) {
    int slots[MAXNR], s = 0;
    for (int v = 0; v < BT; v++)
        for (int i = 0; i < d; i++) slots[s++] = v;
    for (int i = NDART - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = slots[i];
        slots[i] = slots[j];
        slots[j] = tmp;
    }
    for (int k = 0; k < NDART; k++) {
        du[k] = k / d;
        dv[k] = slots[k];
        dg[k] = rndint(GN);
    }
    for (long it = 0; it < 200000; it++) {
        int bad = -1;
        for (int i = 0; i < NDART && bad < 0; i++)
            for (int j = i + 1; j < NDART; j++)
                if (du[i] == du[j] && dv[i] == dv[j] && dg[i] == dg[j]) { bad = j; break; }
        if (bad < 0) return 1;
        dg[bad] = rndint(GN);
    }
    return 0;
}

static void backup_state(void) {
    memcpy(su, du, sizeof(int) * NDART);
    memcpy(sv, dv, sizeof(int) * NDART);
    memcpy(sg, dg, sizeof(int) * NDART);
}

static void restore_state(void) {
    memcpy(du, su, sizeof(int) * NDART);
    memcpy(dv, sv, sizeof(int) * NDART);
    memcpy(dg, sg, sizeof(int) * NDART);
}

/* Lift adjacency. A-fibre vertex u*GN + x joins B-fibre vertex (BT+v)*GN + x*g. */
static void build_lift(void) {
    int V = 2 * BT * GN;
    for (int v = 0; v < V; v++) acnt[v] = 0;
    for (int k = 0; k < NDART; k++) {
        int u = du[k], v = dv[k], g = dg[k];
        for (int x = 0; x < GN; x++) {
            int a = u * GN + x;
            int b = (BT + v) * GN + GT[x * GN + g];
            adj[a][acnt[a]++] = b;
            adj[b][acnt[b]++] = a;
        }
    }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    vstamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = vstamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int i = 0; i < acnt[v]; i++) {
                int u = adj[v][i];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    que[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Left multiplication is an automorphism and fibres are transitive, so one
 * source per fibre (its identity) decides the diameter. */
static long cover_cost(void) {
    int V = 2 * BT * GN;
    long c = 0;
    for (int u = 0; u < BT; u++) {
        c += (long)(V - bfs_reach(u * GN));
        c += (long)(V - bfs_reach((BT + u) * GN));
    }
    return c;
}

/* Simulated annealing over darts. Returns 1 with the solution in du/dv/dg,
 * or 0 at the deadline. */
static int search_cand(double until) {
    const int iters = 4000;
    while (now() < until) {
        if (!init_state()) continue;
        build_lift();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tt = Ts * pow(Te / Ts, (double)it / iters);
            backup_state();
            if (BT > 1 && rnd01() < 0.5) {
                int k1 = rndint(NDART), k2 = rndint(NDART);
                if (dv[k1] == dv[k2]) continue;
                int tmp = dv[k1];
                dv[k1] = dv[k2];
                dv[k2] = tmp;
            } else {
                dg[rndint(NDART)] = rndint(GN);
            }
            if (!valid_state()) { restore_state(); continue; }
            build_lift();
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tt)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                restore_state();
            }
        }
    }
    return 0;
}

static void print_best(const Cand *c, const int *bu, const int *bv, const int *bg) {
    setup_cand(c);
    int nd = c->t * d;
    int n = 2 * c->t * GN, m = nd * GN;
    printf("%d %d\n", n, m);
    for (int k = 0; k < nd; k++)
        for (int x = 0; x < GN; x++) {
            int a = bu[k] * GN + x;
            int b = (c->t + bv[k]) * GN + GT[x * GN + bg[k]];
            printf("%d %d\n", a, b);
        }
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 1) lo = 1;
    if (hi < lo) {
        printf("0 0\n");
        return 0;
    }

    enumerate_cands(lo, hi);
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestN = 0, bi = -1, found = 0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].n <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.1 * rem;
            if (slice < 0.5) slice = 0.5;
            if (slice > 5.0) slice = 5.0;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (search_cand(now() + slice)) {
                bestN = cand[ci].n;
                bi = ci;
                found = 1;
                memcpy(Bu, du, sizeof(int) * NDART);
                memcpy(Bv, dv, sizeof(int) * NDART);
                memcpy(Bg, dg, sizeof(int) * NDART);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    print_best(&cand[bi], Bu, Bv, Bg);
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

    # Search: voltage lifts with 1-4 base vertices per side over small groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 4)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
