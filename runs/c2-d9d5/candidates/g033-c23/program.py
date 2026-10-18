"""Single-orbit Cayley-lift search over two group families for the bipartite degree-diameter problem.

Change in this version: the two-orbit (B = 2) search is removed. In the parent run, every
winning graph came from the single-orbit (B = 1) search, so that time is now used for a
different construction. A B = 1 graph on 2N vertices is a voltage lift of the bipartite
pair (L_g, R_g): dart t joins L_g to R_(g * x_t), with d distinct voltages x_t in a group G
of order N.

Two group families are searched:
  * affine groups F_q x| H (H = subgroup of order c in F_q^*, c >= 1), as before;
  * semidirect products Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1), including the
    abelian case r = 1. These are the non-cyclic groups that the notes suggest for D = 5.

Left translations are automorphisms, transitive on each side, so the diameter is at most D
iff BFS from L_e and R_e reaches all 2N vertices within D steps. Simulated annealing searches
the voltages. The orders are binary-searched over the distinct orders that have candidates,
then scanned upward. A cost-0 state is re-checked by a full BFS when the graph is small
enough. Python keeps the exact constructions (projective plane, Araujo-Pardo and Lopez,
W(q)) and the K_{d,d} fallback, and checks everything with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Single-orbit voltage lifts over two group families.
 * Group G of order N, with elements coded 0..N-1.
 *   typ 0: affine group F_q x| H, element (a, j) coded a*c + j, H = {g^(t*(q-1)/c)}.
 *   typ 1: semidirect Z_m x|_r Z_k, element (a, b) coded a*k + b,
 *          (a,b)(c,e) = (a + r^b c, b + e), needs r^k = 1 mod m.
 * Graph: L_g ~ R_(g * x_t) for t in 0..d-1, distinct voltages x_t.
 * Usage: prog d D seed time_limit lo hi   (lo, hi bound the group order N; V = 2N)
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
#define MAXN 4800
#define MAXD 32
#define MAXCAND 150000

typedef struct {
    int typ;            /* 0 affine, 1 semidirect */
    int N;              /* group order */
    int q, p, fk, c;    /* affine: field order, prime, exponent, subgroup order */
    int m, kk, r;       /* semidirect: Z_m, Z_kk, action r */
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

/* ------------------------------------------------------------ group setup */

static int GTYP = 0;
static int GN;
static int AQ, AC;
static int Hel[MAXC], HM[MAXC * MAXC], hidx[MAXQ], PWG[MAXQ];
static int SM, SK, SR;
static int SPW[MAXN];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GTYP = 0;
    AQ = q;
    AC = c;
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

static inline int amul(int x, int y) {
    int a = x / AC, j = x % AC, b = y / AC, t = y % AC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * AC + HM[j * AC + t];
}

static int ainv(int x) {
    int a = x / AC, j = x % AC;
    int jn = (AC - j) % AC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * AC + jn;
}

static void setup_semi(int m, int k, int r) {
    GTYP = 1;
    SM = m;
    SK = k;
    SR = r % m;
    GN = m * k;
    SPW[0] = 1 % m;
    for (int b = 1; b < k; b++) SPW[b] = (int)((long)SPW[b - 1] * SR % m);
}

static inline int smul(int x, int y) {
    int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
    int na = (int)(((long)a + (long)SPW[b] * c) % SM);
    int nb = b + e;
    if (nb >= SK) nb -= SK;
    return na * SK + nb;
}

static int sinv(int x) {
    int a = x / SK, b = x % SK;
    int nb = (SK - b) % SK;
    int na = (int)((SM - (long)SPW[nb] * a % SM) % SM);
    return na * SK + nb;
}

static inline int gmul(int x, int y) { return GTYP == 0 ? amul(x, y) : smul(x, y); }
static int ginv(int x) { return GTYP == 0 ? ainv(x) : sinv(x); }

/* ------------------------------------------------------------ single-orbit lift */

static int vol[MAXD];
static int fw[MAXD][MAXN], bw[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Dart t has voltage x: L_g ~ R_(g x), so R_y ~ L_(y x^-1). */
static void set_dart(int t, int x) {
    vol[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[t][g] = gmul(g, x);
        bw[t][g] = gmul(g, xi);
    }
}

/* True if x differs from vol[t2] for all t2 < limit with t2 != t. */
static int distinct_from(int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && vol[t2] == x) return 0;
    return 1;
}

/* BFS up to depth D from src (0..N-1 left, N..2N-1 right); returns vertices reached. */
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
                for (int t = 0; t < d; t++) {
                    int u = N + fw[t][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int x = v - N;
                for (int t = 0; t < d; t++) {
                    int u = bw[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    long V = 2L * GN;
    return (V - (long)bfs_count(0)) + (V - (long)bfs_count(GN));
}

/* Simulated annealing over the voltages. Returns 1 with a cost-0 state in vol, 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 6000;
    while (now() < until) {
        for (int t = 0; t < d; t++) {
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!distinct_from(t, x, t) && tries < 100000);
            set_dart(t, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!distinct_from(t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[t];
            set_dart(t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static Cand cand[MAXCAND];
static int nc = 0;
static int ng = 0;
static int gs[MAXCAND], ge[MAXCAND], gN_[MAXCAND];

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void add_cand(const Cand *c) {
    if (nc < MAXCAND) cand[nc++] = *c;
}

static void build_cands(int lo, int hi) {
    nc = 0;
    for (int q = 3; q <= hi && q < MAXQ; q++) {
        int p, fk;
        if (!factor_pp(q, &p, &fk)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            Cand cd;
            memset(&cd, 0, sizeof cd);
            cd.typ = 0; cd.N = (int)N; cd.q = q; cd.p = p; cd.fk = fk; cd.c = c;
            add_cand(&cd);
        }
    }
    for (int m = 2; m <= hi; m++) {
        for (int k = 2; (long)m * k <= hi; k++) {
            long N = (long)m * k;
            if (N < lo) continue;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_i(r, k, m) != 1 % m) continue;
                Cand cd;
                memset(&cd, 0, sizeof cd);
                cd.typ = 1; cd.N = (int)N; cd.m = m; cd.kk = k; cd.r = r;
                add_cand(&cd);
            }
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->N > y->N) - (x->N < y->N);
}

static void group_index(void) {
    ng = 0;
    for (int i = 0; i < nc;) {
        int j = i;
        while (j < nc && cand[j].N == cand[i].N) j++;
        gs[ng] = i;
        ge[ng] = j;
        gN_[ng] = cand[i].N;
        ng++;
        i = j;
    }
}

static void load_cand(const Cand *c) {
    if (c->typ == 0) setup_affine(c->q, c->p, c->fk, c->c);
    else setup_semi(c->m, c->kk, c->r);
}

static int bestN = 0;
static Cand bestC;
static int bestVol[MAXD];

static void record(const Cand *c) {
    if (c->N <= bestN) return;
    bestN = c->N;
    bestC = *c;
    for (int t = 0; t < d; t++) bestVol[t] = vol[t];
}

/* Try up to `tries` shuffled candidates of order group gidx, each with budget `per`. */
static int try_group(int g, double until, int tries, double per) {
    int s = gs[g], e = ge[g];
    for (int i = e - 1; i > s; i--) {
        int j = s + rndint(i - s + 1);
        Cand tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    int lim = s + tries;
    if (lim > e) lim = e;
    for (int t = s; t < lim && now() < until; t++) {
        double dl = now() + per;
        if (dl > until) dl = until;
        load_cand(&cand[t]);
        if (search_group(dl)) {
            record(&cand[t]);
            return 1;
        }
    }
    return 0;
}

static void search_phase(double until) {
    int a = 0, b = ng - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double per = rem * 0.03;
        if (per < 0.8) per = 0.8;
        if (per > rem) per = rem;
        if (try_group(mid, until, 3, per)) a = mid + 1;
        else b = mid - 1;
    }
    int sg = 0;
    while (sg < ng && gN_[sg] <= bestN) sg++;
    int fails = 0;
    for (int g = sg; g < ng && now() < until && fails < 4; g++) {
        double rem = until - now();
        double per = rem * 0.2;
        if (per < 0.8) per = 0.8;
        if (per > rem) per = rem;
        if (try_group(g, until, 3, per)) fails = 0;
        else fails++;
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

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    build_cands(lo, hi);
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);
    group_index();

    search_phase(t_end);

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    load_cand(&bestC);
    for (int t = 0; t < d; t++) set_dart(t, bestVol[t]);

    int N = GN, V = 2 * N, E = N * d;

    /* Full check from every vertex when cheap; the symmetry argument is the fallback. */
    if (V <= 6000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    if (v < N) {
                        for (int t = 0; t < d; t++) {
                            int u = N + fw[t][v];
                            if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                        }
                    } else {
                        int x = v - N;
                        for (int t = 0; t < d; t++) {
                            int u = bw[t][x];
                            if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                        }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < N; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, N + fw[t][v]);
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

    # Single-orbit voltage lifts over affine and semidirect groups. Order N gives 2N vertices.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 5.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
