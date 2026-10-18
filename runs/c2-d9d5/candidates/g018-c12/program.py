"""Two-orbit affine-group voltage lifts for the bipartite degree-diameter problem.

New idea: the parent uses one orbit per side (a single Haar graph on G = F_q x| H).
This version uses a base graph with two vertex orbits per side. Each side has
B = 2 orbits of the group G, and the block (a, b) has a connection set S_ab with
|S_ab| = n_ab. Here n_00 = n_11 = x and n_01 = n_10 = d - x, so every vertex keeps
degree d. The lifted graph has 4|G| vertices. Left translations still act as
automorphisms, so diameter <= D reduces to 4 BFS runs, from L^0_e, L^1_e, R^0_e
and R^1_e, where L^a_g ~ R^b_{g s} for s in S_ab.

The orbit count B is a parameter of the C engine. B = 1 reproduces the parent's
single-orbit search, which the program runs after the two-orbit stage with the
remaining budget. The annealing is the parent's iterated scheme, generalized to
the block structure.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine voltage lift search.
 * Usage: prog d D seed time_limit lo hi B x
 *   B in {1,2}: number of vertex orbits per side.
 *   x: for B=2, block sizes are n00=n11=x, n01=n10=d-x. Ignored for B=1.
 *   lo..hi: range of group orders N = |G|; the graph has 2*B*N vertices.
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
#define MAXN 4096
#define MAXD 32
#define MAXCAND 8192
#define MAXV (4 * MAXN)

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, B, XS;
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

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). */
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

/* ------------------------------------------------------------ block lift state */

/* Orbits: L^a_g = a*N + g (a < B); R^b_h = B*N + b*N + h.
 * Block (a, b) has connection set Sb[a][b][0..nb[a][b]-1];
 * L^a_g ~ R^b_{g s}, equivalently R^b_h ~ L^a_{h s^-1}. */
static int nb[2][2];
static int Sb[2][2][MAXD], incB[2][2][MAXD], bestB[2][2][MAXD];
static int fwd[2][2][MAXD][MAXN], bwd[2][2][MAXD][MAXN];
static int SA[64], SBk[64], SI[64], nslot;
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_s(int a, int b, int i, int x) {
    Sb[a][b][i] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[a][b][i][g] = gmul(g, x);
        bwd[a][b][i][g] = gmul(g, xi);
    }
}

/* True if x already occurs in block (a, b) at an index other than skip. */
static int in_block(int a, int b, int x, int skip) {
    for (int i = 0; i < nb[a][b]; i++)
        if (i != skip && Sb[a][b][i] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int a = v / N, g = v % N;
                for (int b = 0; b < B; b++) {
                    int cnt = nb[a][b];
                    for (int i = 0; i < cnt; i++) {
                        int u = BN + b * N + fwd[a][b][i][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            } else {
                int w = v - BN, b = w / N, h = w % N;
                for (int a = 0; a < B; a++) {
                    int cnt = nb[a][b];
                    for (int i = 0; i < cnt; i++) {
                        int u = a * N + bwd[a][b][i][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

/* One BFS per orbit representative suffices, since G acts by left translation. */
static long cover_cost(void) {
    int N = GN, BN = B * N, V = 2 * BN;
    long c = 0;
    for (int a = 0; a < B; a++) c += (long)(V - bfs_count(a * N));
    for (int b = 0; b < B; b++) c += (long)(V - bfs_count(BN + b * N));
    return c;
}

/* Iterated annealing over all block connection sets in the current group.
 * The first round starts from a random assignment. Later rounds start from the
 * incumbent with two slots replaced, at a lower starting temperature.
 * Returns 1 when cost 0 is reached, 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            for (int t = 0; t < nslot; t++) {
                int a = SA[t], b = SBk[t], i = SI[t], x;
                do { x = rndint(N); } while (in_block(a, b, x, i));
                set_s(a, b, i, x);
            }
        } else {
            for (int a = 0; a < B; a++)
                for (int b = 0; b < B; b++)
                    for (int i = 0; i < nb[a][b]; i++)
                        set_s(a, b, i, incB[a][b][i]);
            for (int t2 = 0; t2 < 2; t2++) {
                int t = rndint(nslot);
                int a = SA[t], b = SBk[t], i = SI[t], x;
                do { x = rndint(N); } while (in_block(a, b, x, i));
                set_s(a, b, i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(nslot);
            int a = SA[t], b = SBk[t], i = SI[t], x;
            do { x = rndint(N); } while (in_block(a, b, x, i));
            int old = Sb[a][b][i];
            set_s(a, b, i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(a, b, i, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incB, Sb, sizeof(Sb));
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN, BN = B * N;
    printf("%d %d\n", 2 * BN, B * d * N);
    for (int a = 0; a < B; a++)
        for (int g = 0; g < N; g++)
            for (int b = 0; b < B; b++)
                for (int i = 0; i < nb[a][b]; i++)
                    printf("%d %d\n", a * N + g, BN + b * N + fwd[a][b][i][g]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    B = atoi(argv[7]);
    XS = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || (B != 1 && B != 2)) { printf("0 0\n"); return 0; }
    if (B == 1) {
        nb[0][0] = d;
    } else {
        if (XS < 0 || XS > d) { printf("0 0\n"); return 0; }
        nb[0][0] = XS;
        nb[0][1] = d - XS;
        nb[1][0] = d - XS;
        nb[1][1] = XS;
    }
    nslot = 0;
    for (int a = 0; a < B; a++)
        for (int b = 0; b < B; b++)
            for (int i = 0; i < nb[a][b]; i++) {
                SA[nslot] = a;
                SBk[nslot] = b;
                SI[nslot] = i;
                nslot++;
            }

    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Ascending group orders; each attempt gets 20% of the remaining time (min 1 s). */
    int best_idx = -1, bestN = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].N <= bestN) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        if (search_group(now() + slice)) {
            bestN = GN;
            best_idx = ci;
            memcpy(bestB, Sb, sizeof(Sb));
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    for (int a = 0; a < B; a++)
        for (int b = 0; b < B; b++)
            for (int i = 0; i < nb[a][b]; i++)
                set_s(a, b, i, bestB[a][b][i]);
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

    def left():
        return 0.88 * time_limit - (time.monotonic() - t0) - 2.0

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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Stage 1: two orbits per side (B = 2), so the graph has 4N vertices.
        # Orders with 4N <= best are skipped, so the search starts near the record.
        lo2 = max(best[0] // 4 + 1, mb // 15 + 1, 2 * d)
        hi2 = min(mb // 4, lo2 * 3 // 2)
        if left() > 2.0 and lo2 <= hi2:
            b1 = round(left() * 0.6, 2)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, b1, lo2, hi2, 2, d // 2],
                                 stdin_graph=None, timeout=b1 + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

        # Stage 2: one orbit per side (B = 1), the parent's single Haar lift, with the rest of the budget.
        budget = left()
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 3
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, 1, 0],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
