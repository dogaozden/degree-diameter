"""Affine-group Haar lifts with scaling-orbit connection sets.

Idea: for a prime power q and c | q-1, let G = F_q x| H (|G| = q*c), with H the
order-c subgroup of F_q^*. The Haar graph uses L_g ~ R_{g*s} for s in a d-element set S.

New in this version: the scaling map (a, h) -> (t*a, h), with t of order m dividing
both q-1 and d, is a group automorphism of G. The search restricts S to be a union of
full m-orbits under this map (k = d/m orbits) plus r = d mod m fixed points with a = 0.
Orbit-restricted sets are much rarer than arbitrary sets, so the annealing searches
a smaller space that is rich in symmetric graphs. The unrestricted search (m = 1) is
kept as one mode. Every candidate is still checked exactly by BFS in C, so the
restriction can only affect which sets are tried, never validity.

The iterated annealing from the parent is kept: each round perturbs the incumbent
selection (two slots replaced) and anneals from a lower starting temperature.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Affine-group Haar lift search with scaling-orbit connection sets.
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
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

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
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;   /* zero divisor: reducible */
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

/* Vertex-transitivity on each side means two BFS runs (from L_e and R_e) decide diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

/* ------------------------------------------------------------ scaling-orbit slots
 *
 * For m > 1 (m | d, m | q-1), the scaling map a -> t*a with t of order m is an
 * automorphism of G. S is built from KF full orbits of size m (a != 0) and RF fixed
 * points with a = 0, where KF*m + RF = d. Full slot s occupies positions s*m..s*m+m-1;
 * singleton slot s occupies position KF*m + (s - KF). For m = 1, all d slots are
 * singletons drawn from the whole group, which is the unrestricted search.
 */

static int M_, KF, RF, KT;
static int fullN, singN;
static int fullMem[MAXN][MAXD];
static int singEl[MAXN];
static int sel[MAXD], incSel[MAXD];

static void build_orbits(int q, int c, int m) {
    M_ = m;
    singN = 0;
    fullN = 0;
    if (m == 1) {
        for (int x = 0; x < GN; x++) singEl[singN++] = x;
        return;
    }
    for (int j = 0; j < c; j++) singEl[singN++] = j;   /* a = 0: code 0*c + j */
    int t = PWG[(q - 1) / m];                          /* element of order m */
    static int seen[MAXQ];
    memset(seen, 0, sizeof(seen));
    for (int a = 1; a < q; a++) {
        if (seen[a]) continue;
        int orb[MAXD];
        int x = a;
        for (int i = 0; i < m; i++) { orb[i] = x; seen[x] = 1; x = MULT[t][x]; }
        for (int j = 0; j < c; j++) {
            for (int i = 0; i < m; i++) fullMem[fullN][i] = orb[i] * c + j;
            fullN++;
        }
    }
}

static int is_dup(int s, int idx) {
    for (int u = 0; u < KT; u++) {
        if (u == s) continue;
        if ((u < KF) != (s < KF)) continue;
        if (sel[u] == idx) return 1;
    }
    return 0;
}

/* Random unused pool index for slot s, or -1 if none is found. */
static int fresh_index(int s) {
    int ps = (s < KF) ? fullN : singN;
    if (ps <= 0) return -1;
    for (int tries = 0; tries < 400; tries++) {
        int idx = rndint(ps);
        if (!is_dup(s, idx)) return idx;
    }
    for (int idx = 0; idx < ps; idx++)
        if (!is_dup(s, idx)) return idx;
    return -1;
}

static void load_slot(int s, int idx) {
    if (s < KF) {
        for (int i = 0; i < M_; i++) set_s(s * M_ + i, fullMem[idx][i]);
    } else {
        set_s(KF * M_ + (s - KF), singEl[idx]);
    }
    sel[s] = idx;
}

/* Iterated annealing over slot selections for the current orbit mode.
 * The first round starts from a random selection. Later rounds start from the
 * incumbent with two slots replaced, at a lower starting temperature.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout or failure. */
static int search_mode(double until) {
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            for (int s = 0; s < KT; s++) sel[s] = -1;
            for (int s = 0; s < KT; s++) {
                int idx = fresh_index(s);
                if (idx < 0) return 0;
                load_slot(s, idx);
            }
        } else {
            for (int s = 0; s < KT; s++) load_slot(s, incSel[s]);
            for (int t = 0; t < 2; t++) {
                int s = rndint(KT);
                int idx = fresh_index(s);
                if (idx >= 0) load_slot(s, idx);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int s = rndint(KT);
            int idx = fresh_index(s);
            if (idx < 0) continue;
            int old = sel[s];
            load_slot(s, idx);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                load_slot(s, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            for (int s = 0; s < KT; s++) incSel[s] = sel[s];
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

    /* Ascending order from lo. For each group, try the unrestricted mode (m = 1)
     * and each orbit mode m >= 2 with m | d and m | q-1, sharing a 25% slice of the
     * remaining time. The first mode that reaches diameter <= D wins. */
    int best_ci = -1, bestN = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].N <= bestN) continue;
        int q = cand[ci].q, c = cand[ci].c;
        setup_group(q, cand[ci].p, cand[ci].k, c);

        int modes[MAXD + 1], nm = 0;
        modes[nm++] = 1;
        for (int m = 2; m <= d; m++)
            if (d % m == 0 && (q - 1) % m == 0) modes[nm++] = m;

        int won = 0;
        for (int mi = 0; mi < nm && !won; mi++) {
            double rem2 = t_end - now();
            if (rem2 < 0.3) break;
            double slice = 0.25 * rem2 / nm;
            if (slice < 0.5) slice = 0.5;
            if (slice > rem2) slice = rem2;

            build_orbits(q, c, modes[mi]);
            if (M_ == 1) { KF = 0; RF = d; }
            else { KF = d / M_; RF = d % M_; }
            KT = KF + RF;
            if (singN < RF || (KF > 0 && fullN < KF)) continue;

            if (search_mode(now() + slice)) {
                won = 1;
                bestN = GN;
                best_ci = ci;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
    }

    if (best_ci < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_ci].q, cand[best_ci].p, cand[best_ci].k, cand[best_ci].c);
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

    # Search: Haar graphs over F_q x| H, with scaling-orbit connection sets.
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
