"""Mixed affine and metacyclic Haar-lift search for the bipartite degree-diameter problem.

New in this version: the C engine searches two families of groups of order N.
(a) Affine groups F_q x| H, as before (H the order-c subgroup of F_q^*).
(b) Metacyclic groups Z_m x| Z_k with r^k = 1 mod m and gcd(r, m) = 1, where r is
    drawn at random per attempt. Taking k = 1 gives cyclic groups, and r = 1 gives
    abelian products. This widens the set of available orders, so N can take every
    value in the window, not only q*c.

Haar graph H(G, S): vertices L_g and R_h, with L_g ~ R_{g s} for s in S. It is
d-regular and bipartite, and simple when the elements of S are distinct.

Correctness fix: left translations are automorphisms, so every L vertex has the
same eccentricity as L_e. Right translations are not automorphisms for a
non-abelian group, so the old cost (BFS from L_e and R_e only) could accept a graph
with a bad R vertex. Now any zero-cost state is confirmed by BFS from every R vertex
before it is accepted.

Scheduling: attempts are capped at about budget/10 seconds each, and the caller
passes lo just above the current best order, so the time goes to orders that can
beat the record.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Mixed affine / metacyclic Haar-lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
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
#define MAXK 12
#define MAXCAND 40000

/* type 0: affine, a = q, b = c.   type 1: metacyclic, a = m, b = k (N = m*k). */
typedef struct { int type, N, a, b; } Cand;

static int d, D;
static double t_end, t_start;
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

/* mode 0: affine F_q x| H, element (a, h_j) coded a*GC + j.
 * mode 1: metacyclic Z_MM x| Z_MK, element (a, b) coded a*MK + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int mode = 0;
static int GN;
static int GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int MM, MK, PW[MAXK];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    mode = 0;
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

static void setup_meta(int m, int k, int r) {
    mode = 1;
    MM = m;
    MK = k;
    GN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)(((long)PW[b - 1] * r) % m);
}

static inline int gmul(int x, int y) {
    if (mode == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    }
    int a = x / MK, b = x % MK, c = y / MK, e = y % MK;
    int na = (a + PW[b] * c) % MM;
    int nb = (b + e) % MK;
    return na * MK + nb;
}

static int ginv(int x) {
    if (mode == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    }
    int a = x / MK, b = x % MK;
    int nb = (MK - b) % MK;
    int t = (PW[nb] * a) % MM;
    int na = (MM - t) % MM;
    return na * MK + nb;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Choose r for a metacyclic candidate uniformly among valid r != 1 (or 1 if none). */
static int pick_r(const Cand *c) {
    if (c->type == 0) return 0;
    int m = c->a, k = c->b;
    if (k == 1) return 1 % m;
    int pick = 1 % m, cnt = 0;
    for (int r = 2; r < m; r++) {
        if (gcd_i(r, m) != 1) continue;
        if (powmod_i(r, k, m) != 1 % m) continue;
        cnt++;
        if (rndint(cnt) == 0) pick = r;
    }
    return pick;
}

static void setup_cand(const Cand *c, int r) {
    if (c->type == 0) {
        int p, kk;
        factor_pp(c->a, &p, &kk);
        setup_affine(c->a, p, kk, c->b);
    } else {
        setup_meta(c->a, c->b, r);
    }
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Heuristic cost: BFS from L_e and R_e only. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

/* Exact check: L side is transitive (left translations are automorphisms), so the
 * BFS from L_e covers all L vertices. Every R vertex needs its own BFS, because
 * right translations need not be automorphisms for a non-abelian group. */
static int full_check(void) {
    int N = GN, V = 2 * N;
    if (bfs_count(0) != V) return 0;
    for (int x = 0; x < N; x++)
        if (bfs_count(N + x) != V) return 0;
    return 1;
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over S (size d) in the current group.
 * Returns 1 when the graph is fully valid (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            set_s(i, x);
        }
        long cost = cover_cost();
        if (cost == 0) {
            if (full_check()) return 1;
            cost = 1;
        }
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 == 0 && !full_check()) c2 = 1;
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_s(i, old);
            }
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = x, *q = y;
    if (p->N != q->N) return p->N < q->N ? -1 : 1;
    return p->type - q->type;
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
    t_start = now();
    t_end = t_start + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    /* Affine candidates. */
    for (int q = 3; q < MAXQ; q++) {
        int p, kk;
        if (!factor_pp(q, &p, &kk)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                cand[nc].type = 0; cand[nc].N = (int)N; cand[nc].a = q; cand[nc].b = c;
                nc++;
            }
        }
    }
    /* Metacyclic candidates Z_m x| Z_k with N = m*k, k <= MAXK (k = 1 is cyclic). */
    for (int N = lo; N <= hi; N++)
        for (int k = 1; k <= MAXK; k++) {
            if (N % k) continue;
            int m = N / k;
            if (m < 3) continue;
            if (nc < MAXCAND) {
                cand[nc].type = 1; cand[nc].N = N; cand[nc].a = m; cand[nc].b = k;
                nc++;
            }
        }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Repeated ascending passes. Each attempt gets at most budget/10 seconds
     * (at least 1 s, at most 20% of the remaining time). Later passes restart
     * with fresh random starts and fresh random r for metacyclic candidates. */
    int best = -1, bestN = 0, best_r = 0;
    double budget = t_end - t_start;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0, stop = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) { stop = 1; break; }
            tried = 1;
            double slice = 0.2 * rem;
            double cap = budget / 10.0;
            if (slice > cap) slice = cap;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            int r = pick_r(&cand[ci]);
            setup_cand(&cand[ci], r);
            if (search_group(now() + slice)) {
                bestN = GN;
                best = ci;
                best_r = r;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!tried || stop) break;
    }

    if (best < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&cand[best], best_r);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
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

    # Search: Haar graphs over affine and metacyclic groups, with orders just above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 3
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
