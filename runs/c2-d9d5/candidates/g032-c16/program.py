"""Multi-orbit bi-Cayley lifts for the bipartite degree-diameter problem.

New idea in this version: a k-orbit bi-Cayley graph. Over a group G of order N, the
left vertices are L_{i,g} and the right vertices are R_{j,h} (i, j < k). Block (i, j)
carries a set S_ij of s elements, and L_{i,g} ~ R_{j,g*s} for s in S_ij. Every row
and column of the size matrix sz[i][j] sums to d, so the graph is d-regular, bipartite
and simple (distinct s in each block). Left translation by G preserves the graph, so
the diameter only needs BFS from the 2k orbit representatives L_{i,e} and R_{j,e}.
The parent's Haar graphs are the k = 1 case.

C search: candidates (group, k) are chosen from a window just above the best order
found so far. The window is picked at random each step, so a candidate that failed can
be retried with fresh random sizes and sets. Each attempt is a simulated-annealing
search over the block sets, with cost = total uncovered (vertex, orbit) pairs.
Groups: cyclic Z_N, and affine F_q x| H_c (H_c the subgroup of order c in F_q^*).
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search.
 * Usage: prog d D seed time_limit lo hi      (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
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
#define MAXD 16
#define MAXK 3
#define MAXV 10000
#define MAXCAND 60000

typedef struct { int V, N, K, typ, q, p, kk, cc; } Cand;

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

/* ------------------------------------------------------------ groups */

/* GTYPE 0: cyclic Z_N (x + y mod N).
 * GTYPE 1: F_q x| H_c, element (a, h_j) coded as a*GC + j, h_j = g^(j*(q-1)/c). */
static int GTYPE = 0, GN = 0, GC = 1;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_cyc(int N) {
    GTYPE = 0;
    GN = N;
    GC = 1;
}

static void setup_aff(int q, int p, int kk, int cc) {
    build_field(q, p, kk);
    GTYPE = 1;
    GC = cc;
    GN = q * cc;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / cc;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < cc; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < cc; j++)
        for (int t = 0; t < cc; t++)
            HM[j * cc + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    if (GTYPE == 0) {
        int r = x + y;
        if (r >= GN) r -= GN;
        return r;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    if (GTYPE == 0) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ bi-Cayley state */

/* Vertices: L_{i,g} = i*N + g, R_{j,h} = K*N + j*N + h.
 * Block (i,j) holds sz[i][j] distinct elements Sel[i][j][t]; L_{i,g} ~ R_{j, g*s}. */
static int K = 1, V = 0;
static int sz[MAXK][MAXK];
static int Sel[MAXK][MAXK][MAXD], Sinv[MAXK][MAXK][MAXD];
static int adj[MAXV][MAXD];
static int vis[MAXV], que[MAXV], vstamp = 0;

static void rebuild(void) {
    int N = GN;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < N; g++) {
            int v = i * N + g, idx = 0;
            for (int j = 0; j < K; j++)
                for (int t = 0; t < sz[i][j]; t++)
                    adj[v][idx++] = K * N + j * N + gmul(g, Sel[i][j][t]);
        }
    for (int j = 0; j < K; j++)
        for (int h = 0; h < N; h++) {
            int v = K * N + j * N + h, idx = 0;
            for (int i = 0; i < K; i++)
                for (int t = 0; t < sz[i][j]; t++)
                    adj[v][idx++] = i * N + gmul(h, Sinv[i][j][t]);
        }
}

static int bfs_count(int src) {
    vstamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = vstamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int e = 0; e < d; e++) {
                int u = adj[v][e];
                if (vis[u] != vstamp) { vis[u] = vstamp; que[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Orbit representatives: L_{i,e} and R_{j,e}. Left translation is an automorphism. */
static long cover_cost(void) {
    long c = 0;
    for (int i = 0; i < K; i++) c += (long)(V - bfs_count(i * GN));
    for (int j = 0; j < K; j++) c += (long)(V - bfs_count(K * GN + j * GN));
    return c;
}

static int in_block(int i, int j, int x, int upto) {
    for (int t = 0; t < upto; t++)
        if (Sel[i][j][t] == x) return 1;
    return 0;
}

/* Random size matrix with all row and column sums equal to d. */
static void random_sizes(void) {
    int rsum[MAXK] = {0}, csum[MAXK] = {0};
    memset(sz, 0, sizeof sz);
    for (;;) {
        int rows[MAXK], nr = 0;
        for (int i = 0; i < K; i++) if (rsum[i] < d) rows[nr++] = i;
        if (!nr) break;
        int i = rows[rndint(nr)];
        int cols[MAXK], nq = 0;
        for (int j = 0; j < K; j++) if (csum[j] < d) cols[nq++] = j;
        int j = cols[rndint(nq)];
        sz[i][j]++;
        rsum[i]++;
        csum[j]++;
    }
}

static void random_init(void) {
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < sz[i][j]; t++) {
                int x;
                do { x = rndint(GN); } while (in_block(i, j, x, t));
                Sel[i][j][t] = x;
                Sinv[i][j][t] = ginv(x);
            }
    rebuild();
}

/* Annealing over sizes and block sets. Returns 1 with a valid state, 0 on timeout. */
static int search_cand(double until) {
    while (now() < until) {
        random_sizes();
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 12000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(K), j = rndint(K);
            if (!sz[i][j]) continue;
            int t = rndint(sz[i][j]);
            int old = Sel[i][j][t];
            int x;
            do { x = rndint(GN); } while (in_block(i, j, x, sz[i][j]));
            Sel[i][j][t] = x;
            Sinv[i][j][t] = ginv(x);
            rebuild();
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                Sel[i][j][t] = old;
                Sinv[i][j][t] = ginv(old);
                rebuild();
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void setup_cand(const Cand *c) {
    K = c->K;
    if (c->typ == 0) setup_cyc(c->N);
    else setup_aff(c->q, c->p, c->kk, c->cc);
    V = 2 * K * GN;
}

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->V > y->V) - (x->V < y->V);
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

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > 9000) hi = 9000;
    if (lo < 2 * d) lo = 2 * d;
    if (hi < lo) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    static int lst[MAXCAND];
    int nc = 0;
    for (int kk = 1; kk <= MAXK; kk++) {
        int Nmin = (lo + 2 * kk - 1) / (2 * kk);
        if (Nmin < 2 * d) Nmin = 2 * d;
        int Nmax = hi / (2 * kk);
        if (Nmax < Nmin) continue;
        for (int N = Nmin; N <= Nmax && nc < MAXCAND; N++) {
            Cand cd = {2 * kk * N, N, kk, 0, 0, 0, 0, 0};
            cand[nc++] = cd;
        }
        for (int q = 3; q < MAXQ; q++) {
            int p, e;
            if (!factor_pp(q, &p, &e)) continue;
            for (int cc = 1; cc <= q - 1; cc++) {
                if ((q - 1) % cc) continue;
                if (cc == 1 && e == 1) continue;   /* same as cyclic Z_q */
                int N = q * cc;
                if (N < Nmin || N > Nmax || nc >= MAXCAND) continue;
                Cand cd = {2 * kk * N, N, kk, 1, q, p, e, cc};
                cand[nc++] = cd;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);

    /* Window climb: attempt a random candidate in a window just above the best
     * order so far. Failed candidates can be retried with fresh random starts. */
    int curbest = lo - 1, bestFound = 0;
    static Cand bestC;
    static int bsz[MAXK][MAXK], bSel[MAXK][MAXK][MAXD];
    while (1) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        int vmin = 0;
        for (int ci = 0; ci < nc; ci++)
            if (cand[ci].V > curbest && (!vmin || cand[ci].V < vmin)) vmin = cand[ci].V;
        if (!vmin) break;
        int W = curbest / 10;
        if (W < 100) W = 100;
        int cntw = 0;
        for (int ci = 0; ci < nc; ci++)
            if (cand[ci].V > curbest && cand[ci].V <= vmin + W) lst[cntw++] = ci;
        int pick = lst[rndint(cntw)];
        double slice = 0.12 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > 6.0) slice = 6.0;
        if (slice > rem) slice = rem;
        setup_cand(&cand[pick]);
        if (search_cand(now() + slice)) {
            curbest = cand[pick].V;
            bestFound = 1;
            bestC = cand[pick];
            memcpy(bsz, sz, sizeof sz);
            memcpy(bSel, Sel, sizeof Sel);
        }
    }

    if (!bestFound) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&bestC);
    memcpy(sz, bsz, sizeof sz);
    memcpy(Sel, bSel, sizeof Sel);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < sz[i][j]; t++)
                Sinv[i][j][t] = ginv(Sel[i][j][t]);
    rebuild();
    if (cover_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int N = GN;
    printf("%d %d\n", V, K * N * d);
    for (int v = 0; v < K * N; v++)
        for (int e = 0; e < d; e++)
            printf("%d %d\n", v, adj[v][e]);
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

    # Search: multi-orbit bi-Cayley lifts (k = 1 gives the Haar lifts).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8, 2 * d)
        hi = min(mb // 2, 9000)
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
