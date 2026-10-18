"""Multi-orbit affine Haar lifts for the bipartite degree-diameter problem.

New idea in this version: the parent searches one-orbit lifts, where the graph is
the Haar graph of a group G (order N) with left vertices L_g ~ R_{g s}, s in S, and
|S| = d. This version also searches two-orbit lifts (B = 2). Vertices are
L_{i,g} and R_{j,h} for i, j in {0, 1} and g, h in G, so there are 4N vertices.
Each orbit pair (i, j) gets a connection set S_ij with L_{i,g} ~ R_{j,g s} for s in
S_ij. Degrees are balanced by the pattern counts [[a, d-a], [d-a, a]], so every
vertex has degree d. Left and right translations keep each orbit transitive, so
the diameter test needs only four BFS runs, one from each orbit representative.

The group family is G = F_q x| H, where H is the subgroup of F_q^* of order c, and
c = 1 gives the additive group. The engine walks candidate orders in ascending
order with repeated passes, as in the parent.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count V = 2*B*N.
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
#define MAXB 2
#define MAXV (2 * MAXB * MAXN)
#define MAXEDGE (MAXV * MAXD / 2)
#define MAXCAND 16384
#define ITERS 2500

typedef struct { int q, p, k, c, B, N, V; } Cand;

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

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). c = 1 gives F_q additive. */
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
    if (q == 2) g = 1;
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

static int gmul(int x, int y) {
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

/* ------------------------------------------------------------ multi-orbit lift state
 * Vertices: L_{i,g} = i*N + g (i < B), R_{j,h} = (B+j)*N + h.
 * Edge L_{i,g} ~ R_{j,g*s} for s in S_ij (|S_ij| = ncnt[i][j]).
 * Each vertex has exactly d neighbours; NB holds them, stride MAXD.
 */

static int B, N, V;
static int ncnt[MAXB][MAXB];
static int E[MAXB][MAXB][MAXD], EI[MAXB][MAXB][MAXD];
static int NB[MAXV * MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestV = 0;
static long bestE = 0;
static int BU[MAXEDGE], BW[MAXEDGE];

static void set_pattern(int a) {
    if (B == 1) {
        ncnt[0][0] = d;
    } else {
        ncnt[0][0] = a;
        ncnt[0][1] = d - a;
        ncnt[1][0] = d - a;
        ncnt[1][1] = a;
    }
}

static int slotL(int i, int j, int t) {
    int k = 0;
    for (int jj = 0; jj < j; jj++) k += ncnt[i][jj];
    return k + t;
}

static int slotR(int i, int j, int t) {
    int k = 0;
    for (int ii = 0; ii < i; ii++) k += ncnt[ii][j];
    return k + t;
}

static void set_elem(int i, int j, int t, int s) {
    E[i][j][t] = s;
    int si = ginv(s);
    EI[i][j][t] = si;
    int kl = slotL(i, j, t), kr = slotR(i, j, t);
    for (int g = 0; g < N; g++)
        NB[(i * N + g) * MAXD + kl] = (B + j) * N + gmul(g, s);
    for (int h = 0; h < N; h++)
        NB[((B + j) * N + h) * MAXD + kr] = i * N + gmul(h, si);
}

static int in_set(int i, int j, int upto, int s) {
    for (int t = 0; t < upto; t++)
        if (E[i][j][t] == s) return 1;
    return 0;
}

static void random_fill(void) {
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int t = 0; t < ncnt[i][j]; t++) {
                int s;
                do { s = rndint(N); } while (in_set(i, j, t, s));
                set_elem(i, j, t, s);
            }
}

/* Vertices within distance D of src. */
static int bfs_reach(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            const int *row = NB + v * MAXD;
            for (int k = 0; k < d; k++) {
                int u = row[k];
                if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Orbit representatives: vertex k*N (group identity) for k < 2B. */
static long cost_all(void) {
    long c = 0;
    for (int k = 0; k < 2 * B; k++)
        c += (long)(V - bfs_reach(k * N));
    return c;
}

static void record(void) {
    long m = 0;
    for (int v = 0; v < B * N; v++)
        for (int k = 0; k < d; k++) {
            BU[m] = v;
            BW[m] = NB[v * MAXD + k];
            m++;
        }
    bestE = m;
}

/* Annealing over the connection sets for one (group, B) candidate.
 * Returns 1 on diameter <= D, 0 on timeout. */
static int search_cand(double until) {
    while (now() < until) {
        int a = (B == 2) ? 1 + rndint(d - 1) : 0;
        set_pattern(a);
        random_fill();
        long cost = cost_all();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int i = rndint(B), j = rndint(B);
            int t = rndint(ncnt[i][j]);
            int old = E[i][j][t];
            int s;
            do { s = rndint(N); } while (in_set(i, j, ncnt[i][j], s));
            set_elem(i, j, t, s);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_elem(i, j, t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long Nn = (long)q * c;
            if (Nn > MAXN || Nn < 2 * d) continue;
            for (int b = 1; b <= MAXB; b++) {
                long Vv = 2L * b * Nn;
                if (Vv < lo || Vv > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, b, (int)Nn, (int)Vv};
                    cand[nc++] = cd;
                }
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].V > t.V) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Ascending passes. Each attempt gets 20% of the remaining time (at least 1 s).
     * Candidates that failed earlier are retried with fresh random starts. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            Cand cd = cand[ci];
            setup_group(cd.q, cd.p, cd.k, cd.c);
            B = cd.B;
            N = GN;
            V = 2 * B * N;
            if (search_cand(now() + slice)) {
                bestV = V;
                record();
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestV, bestE);
    for (long e = 0; e < bestE; e++)
        printf("%d %d\n", BU[e], BW[e]);
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

    # Search: one-orbit and two-orbit affine Haar lifts with a wide vertex range.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 5)
        hi = (2 * mb) // 3
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
