"""Mixed-group iterated Haar search with successive halving.

New in this version:
  * A second group family, the semidirect products Z_m x|_r Z_k (r^k = 1 mod m,
    gcd(r, m) = 1). The field-based family F_q x| H only gives orders q*c with
    c | q-1, so it never produces orders such as 1248 = 2^5 * 3 * 13. The semidirect
    family covers all orders in the range.
  * Successive halving over candidate groups. Each candidate keeps its incumbent
    connection set. Rounds give the alive candidates growing time slices, the worse
    half is dropped by normalised uncovered-pair count, and new candidates are
    added in ascending order of order. Time therefore goes to the groups that look
    closest to diameter D, and the search keeps trying larger orders.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Haar graphs over mixed finite groups with successive halving.
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
#define MAXN 8192
#define MAXD 32
#define MAXCAND 60000
#define MAXALIVE 64
#define REFILL 8
#define S0 0.15

typedef struct {
    int type;          /* 0: F_q x| H (q, c); 1: Z_m x|_r Z_k (m, k, r) */
    int q, p, e, c;    /* field data, q = p^e, c divides q-1 */
    int m, k, r;       /* semidirect data */
    int N;
    int runs;
    int haveS;
    long bestc;
    int incS[MAXD];
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

static int factor_pp(int q, int *p, int *e) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *e = kk;
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

static int gtype = 0;                 /* 0 = field affine group, 1 = semidirect */
static int GQ, GC, GN, SM, SK, SR;
static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ][MAXQ], PWG[MAXQ];
static int SPW[MAXN];                 /* SPW[b] = r^b mod m for semidirect */

/* Field group F_q x| H: element (a, h_j) coded as a*c + j, h_j = g^(j*(q-1)/c). */
static void setup_field(int q, int p, int e, int c) {
    build_field(q, p, e);
    gtype = 0;
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
            HM[j][t] = hidx[MULT[Hel[j]][Hel[t]]];
}

/* Semidirect Z_m x|_r Z_k: element (a, b) coded a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_semi(int m, int k, int r) {
    gtype = 1;
    SM = m;
    SK = k;
    SR = r;
    GN = m * k;
    SPW[0] = 1 % m;
    for (int b = 1; b < k; b++) SPW[b] = (int)((long)SPW[b - 1] * r % m);
}

static inline int smul(int x, int y) {
    int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
    int na = (a + SPW[b] * c) % SM;
    int nb = (b + e) % SK;
    return na * SK + nb;
}

static inline int sinv(int x) {
    int a = x / SK, b = x % SK;
    int nb = (SK - b) % SK;
    int na = (SM - (SPW[nb] * a) % SM) % SM;
    return na * SK + nb;
}

static inline int gmul(int x, int y) {
    if (gtype == 1) return smul(x, y);
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j][t];
}

static inline int ginv(int x) {
    if (gtype == 1) return sinv(x);
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g, R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
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

/* Left translations are automorphisms, so one BFS per side decides the diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;
static int cur_cand = -1;

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) setup_field(cd->q, cd->p, cd->e, cd->c);
    else setup_semi(cd->m, cd->k, cd->r);
}

/* One annealing slice on candidate a, resumed from its incumbent (or random if none).
 * The incumbent is the lowest-cost set seen, and cost always matches the current S.
 * Returns 1 when cost 0 (diameter <= D) is reached. */
static int run_slice(int a, double until) {
    Cand *cd = &cand[a];
    if (cur_cand != a) { setup_cand(cd); cur_cand = a; }
    int N = GN;
    int found = 0;
    while (!found && now() < until) {
        if (!cd->haveS) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, cd->incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        double c0 = (double)cost;
        double Ts = (cd->haveS ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        const int iters = 8000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) break;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d), x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else set_s(i, old);
        }
        if (!cd->haveS || cost < cd->bestc) {
            cd->haveS = 1;
            cd->bestc = cost;
            memcpy(cd->incS, S, sizeof(int) * (size_t)d);
        }
        if (cost == 0) found = 1;
    }
    return found;
}

static double score_of(int a) {
    const Cand *cd = &cand[a];
    if (!cd->haveS) return 1e18;
    return (double)cd->bestc / (2.0 * cd->N);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int factor_pp_unused_guard(void) { return 0; }

static void add_cand(int type, int q, int p, int e, int c, int m, int k, int r, int N) {
    if (nc >= MAXCAND) return;
    Cand *cd = &cand[nc++];
    memset(cd, 0, sizeof *cd);
    cd->type = type;
    cd->q = q; cd->p = p; cd->e = e; cd->c = c;
    cd->m = m; cd->k = k; cd->r = r;
    cd->N = N;
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    return (a->N > b->N) - (a->N < b->N);
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
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    /* Field family: F_q x| H with c | q-1. */
    for (int q = 3; q < MAXQ; q++) {
        int p, e;
        if (!factor_pp(q, &p, &e)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            add_cand(0, q, p, e, c, 0, 0, 0, (int)N);
        }
    }
    /* Semidirect family: Z_m x|_r Z_k, covering every order in range. */
    for (int m = 2; m <= hi / 2; m++)
        for (int k = 2; (long)m * k <= hi; k++) {
            long N = (long)m * k;
            if (N < lo) continue;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_i(r, k, m) != 1) continue;
                add_cand(1, 0, 0, 0, 0, m, k, r, (int)N);
            }
        }
    if (nc == 0) { printf("0 0\n"); return 0; }

    /* Shuffle, then sort ascending by order. */
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Successive halving: alive candidates get slices that double with each run.
     * Each round keeps the better half by uncovered fraction, and refills from the
     * ascending pool. A success at order N drops every candidate of order <= N. */
    int bestN = 0, bestIdx = -1;
    int alive[MAXALIVE];
    int na = 0, nxt = 0;
    while (now() < t_end - 0.05) {
        while (na < REFILL && nxt < nc) {
            int a = nxt++;
            if (cand[a].N > bestN) alive[na++] = a;
        }
        if (na == 0) break;
        for (int j = 0; j < na; j++) {
            int a = alive[j];
            if (cand[a].N <= bestN) continue;
            double rem = t_end - now();
            if (rem <= 0.02) break;
            int lvl = cand[a].runs < 6 ? cand[a].runs : 6;
            double sl = S0 * (double)(1 << lvl);
            if (sl > 8.0) sl = 8.0;
            if (sl > rem) sl = rem;
            cand[a].runs++;
            if (run_slice(a, now() + sl)) {
                if (cand[a].N > bestN) {
                    bestN = cand[a].N;
                    bestIdx = a;
                }
            }
        }
        int m2 = 0;
        for (int j = 0; j < na; j++)
            if (cand[alive[j]].N > bestN) alive[m2++] = alive[j];
        na = m2;
        if (na >= 2) {
            for (int i = 1; i < na; i++) {
                int v = alive[i];
                double sv = score_of(v);
                int j = i - 1;
                while (j >= 0 && score_of(alive[j]) > sv) {
                    alive[j + 1] = alive[j];
                    j--;
                }
                alive[j + 1] = v;
            }
            na = (na + 1) / 2;
        }
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    cur_cand = -1;
    setup_cand(&cand[bestIdx]);
    for (int i = 0; i < d; i++) set_s(i, cand[bestIdx].incS[i]);
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

    # Search over Haar graphs on mixed groups (field affine and semidirect families).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
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
