"""Group-family Haar lift search for the bipartite degree-diameter problem.

Idea: the bipartite Haar graph H(G, S) has parts L_g and R_h, with L_g ~ R_{g s} for
s in S, where |S| = d. It is d-regular and simple when S has distinct elements. The
parent searched only the affine groups F_q x| H. This version adds two new families
that the parent does not search:

  fam 1 (abelian):  Z_m x Z_k with m <= k. Cyclic groups are the case m = 1. Abelian
                    Haar graphs are vertex-transitive, since translations and the
                    side-swap L_g -> R_{-g}, R_h -> L_{-h} are automorphisms.
  fam 2 (semidirect): Z_m x| Z_k with (a,b)(c,d) = (a + r^b c, b + d), r != 1,
                    gcd(r,m) = 1 and r^k = 1 mod m. At most three values of r are
                    kept per (m,k).

All candidate groups with order in [lo, hi] are merged into one list sorted by order.
The C engine binary-searches that list for the largest feasible order. Each probe gets
an equal share of the remaining time, sized by the number of probes still expected.
Leftover time goes to the next few orders above the best. Feasibility is checked by
cover cost (BFS from L_e and R_e), and Python re-checks every returned graph with
lib.is_valid. The projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d}
fallback are kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Group-family Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Families: 0 = affine F_q x| H, 1 = abelian Z_m x Z_k (m=1 gives cyclic),
 *           2 = semidirect Z_m x| Z_k with action r.
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
#define MAXCAND 200000

enum { FAM_AFF = 0, FAM_ABE = 1, FAM_SEMI = 2 };

typedef struct { int fam, N, x1, x2, x3; } Cand;

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

/* ------------------------------------------------------------ group state */

static int GFAM, GN, GC, GM, GK, GR;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int PWR[MAXN];

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void setup_group(const Cand *cd) {
    GFAM = cd->fam;
    GN = cd->N;
    if (GFAM == FAM_AFF) {
        int q = cd->x1, c = cd->x2, p, k;
        factor_pp(q, &p, &k);
        build_field(q, p, k);
        GC = c;
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
    } else {
        GM = cd->x1;
        GK = cd->x2;
        if (GFAM == FAM_SEMI) {
            GR = cd->x3;
            PWR[0] = 1 % GM;
            for (int i = 1; i < GK; i++)
                PWR[i] = (int)((long)PWR[i - 1] * GR % GM);
        }
    }
}

static inline int gmul(int x, int y) {
    if (GFAM == FAM_AFF) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    }
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    if (GFAM == FAM_ABE) {
        int na = (a + c) % GM;
        int nb = (b + e) % GK;
        return na * GK + nb;
    }
    int na = (a + (int)((long)PWR[b] * c % GM)) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static int ginv(int x) {
    if (GFAM == FAM_AFF) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    }
    int a = x / GK, b = x % GK;
    if (GFAM == FAM_ABE) {
        return ((GM - a) % GM) * GK + (GK - b) % GK;
    }
    int nb = (GK - b) % GK;
    int na = (int)((long)PWR[nb] * a % GM);
    na = (GM - na) % GM;
    return na * GK + nb;
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

static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over the d-element connection set in the current group.
 * Returns 1 when cost 0 is reached, 0 on timeout. S then holds the solution. */
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
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
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

/* ------------------------------------------------------------ candidates */

static int addc(Cand *cand, int *nc, int fam, int N, int x1, int x2, int x3) {
    if (*nc >= MAXCAND) return 0;
    cand[*nc].fam = fam;
    cand[*nc].N = N;
    cand[*nc].x1 = x1;
    cand[*nc].x2 = x2;
    cand[*nc].x3 = x3;
    (*nc)++;
    return 1;
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->N != b->N) return a->N < b->N ? -1 : 1;
    if (a->fam != b->fam) return a->fam - b->fam;
    if (a->x1 != b->x1) return a->x1 - b->x1;
    if (a->x2 != b->x2) return a->x2 - b->x2;
    return a->x3 - b->x3;
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
    if (lo > hi) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;

    /* Affine F_q x| H, order q*c. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            addc(cand, &nc, FAM_AFF, (int)N, q, c, 0);
        }
    }

    /* Abelian Z_m x Z_k with m <= k (m = 1 is cyclic). */
    for (int m = 1; m <= hi; m++) {
        int kmin = (m == 1) ? 2 : m;
        int kst = (lo + m - 1) / m;
        if (kst < kmin) kst = kmin;
        for (int k = kst; m * k <= hi; k++)
            addc(cand, &nc, FAM_ABE, m * k, m, k, 0);
    }

    /* Semidirect Z_m x| Z_k, action r != 1 with r^k = 1 mod m, gcd(r, m) = 1. */
    for (int m = 3; m <= hi / 2; m++) {
        for (int k = 2; m * k <= hi; k++) {
            if (m * k < lo) continue;
            int taken = 0;
            for (int r = 2; r < m && taken < 3; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                addc(cand, &nc, FAM_SEMI, m * k, m, k, r);
                taken++;
            }
        }
    }

    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search for the largest feasible order. Each probe gets an
     * equal share of the remaining time, sized by the probes still expected. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        double rem = t_end - now();
        int steps = 0;
        for (int w = b - a + 1; w > 0; w >>= 1) steps++;
        double slice = rem / (steps + 1.0);
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        setup_group(&cand[mid]);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        setup_group(&cand[idx]);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&cand[best_idx]);
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

    # Group-family Haar graphs (affine, abelian, semidirect). A graph on 2N vertices
    # needs N <= moore_bound / 2.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
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
