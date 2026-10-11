import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as the safe floor).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: a different search from the parent's breakout method.
#
# Bi-group lifts. Group G is drawn from three families: cyclic Z_n, direct
# products Z_a x Z_b, and semidirect products Z_m x| Z_k. Vertices are
# A_{i,g} = i*G+g and B_{j,h} = (K+j)*G+h. Dart (l, i) joins A_{i,g} to
# B_{P[l][i], g*S[l][i]}. Left multiplication by any h is an automorphism,
# so only the identity of each block needs a BFS: 2K searches in total.
#
# Cost = unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts.
# Cost 0 means valid. Simulated annealing runs from random starts, and from a
# perturbed near-miss when one exists.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define MAXG 1600
#define NMAX (2 * MAXK * MAXG)
#define PEN 40
#define SA_ITERS 40000L
#define NEAR_ITERS 15000L

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} State;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 7, DD = 5;
static double deadline = 0.0;

/* Current group: order G, multiplication table MTB[x*G+y], identity 0. */
static int G = 1;
static int gtype = 0, gp1 = 1, gp2 = 0, gr = 0;
static int MTB[MAXG * MAXG];
static int pw_[MAXG];

static int ADJ[NMAX * MAXD];
static int CNT[NMAX], VIS[NMAX], QQ[NMAX];
static int stamp = 0;

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void build_group(int gt, int p1, int p2, int r) {
    gtype = gt;
    gp1 = p1;
    gp2 = p2;
    gr = r;
    if (gt == 0) {
        G = p1;
        for (int x = 0; x < G; x++)
            for (int y = 0; y < G; y++)
                MTB[x * G + y] = (x + y) % G;
    } else if (gt == 1) {
        int a = p1, b = p2;
        G = a * b;
        for (int x = 0; x < G; x++) {
            int i1 = x / b, j1 = x % b;
            for (int y = 0; y < G; y++) {
                int i2 = y / b, j2 = y % b;
                MTB[x * G + y] = ((i1 + i2) % a) * b + (j1 + j2) % b;
            }
        }
    } else {
        /* Semidirect Z_m x| Z_k: (a,b)(c,d) = (a + r^b c, b + d). */
        int m = p1, k = p2;
        G = m * k;
        long long p = 1 % m;
        for (int b = 0; b < k; b++) {
            pw_[b] = (int)p;
            p = p * r % m;
        }
        for (int x = 0; x < G; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < G; y++) {
                int c = y / k, d = y % k;
                long long t = ((long long)a + (long long)pw_[b] * c) % m;
                MTB[x * G + y] = (int)t * k + (b + d) % k;
            }
        }
    }
}

static int divs[512];

static void choose_group(int Gt) {
    int nd = 0;
    for (int dv = 2; dv <= Gt / 2; dv++)
        if (Gt % dv == 0 && nd < 512) divs[nd++] = dv;
    int roll = rint_(100);
    if (nd == 0 || roll < 30) {
        build_group(0, Gt, 0, 0);
        return;
    }
    int k = divs[rint_(nd)];
    int m = Gt / k;
    if (roll < 60) {
        build_group(1, k, m, 0);
        return;
    }
    for (int t = 0; t < 300 && m >= 3; t++) {
        long long c = 2 + rint_(m - 2);
        if (gcdll(c, m) == 1 && powmod_ll(c, k, m) == 1 % m) {
            build_group(2, m, k, (int)c);
            return;
        }
    }
    build_group(1, k, m, 0);
}

static void random_state(State *s, int K) {
    s->K = K;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) s->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = s->P[l][i];
            s->P[l][i] = s->P[l][j];
            s->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) s->S[l][i] = rint_(G);
    }
}

static void perturb(State *s, int moves) {
    int K = s->K;
    for (int t = 0; t < moves; t++) {
        int l = rint_(Dd);
        if (K >= 2 && rint_(4) == 0) {
            int i1 = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int tmp = s->P[l][i1];
            s->P[l][i1] = s->P[l][i2];
            s->P[l][i2] = tmp;
        } else {
            int i = rint_(K);
            s->S[l][i] = rint_(G);
        }
    }
}

/* Cost = unreached rep-pairs within DD + PEN * duplicate darts. */
static long eval_cost(const State *s, int *dupo, long *rawo) {
    int K = s->K;
    int N = 2 * K * G;
    for (int v = 0; v < N; v++) CNT[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = s->P[l][i], sv = s->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + MTB[g * G + sv];
                ADJ[a * Dd + CNT[a]++] = b;
                ADJ[b * Dd + CNT[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (s->P[l1][i] == s->P[l2][i] && s->S[l1][i] == s->S[l2][i])
                    dup++;

    long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int h = 0, t = 0;
        VIS[src] = stamp;
        QQ[t++] = src;
        for (int lv = 0; lv < DD; lv++) {
            int end = t;
            if (h == end) break;
            while (h < end) {
                int u = QQ[h++];
                for (int q = 0; q < Dd; q++) {
                    int v = ADJ[u * Dd + q];
                    if (VIS[v] != stamp) {
                        VIS[v] = stamp;
                        QQ[t++] = v;
                    }
                }
            }
        }
        raw += (long)(N - t);
    }
    *dupo = dup;
    *rawo = raw;
    return raw + (long)PEN * dup;
}

/* Simulated annealing. Returns the best cost seen; *bs holds that state. */
static long sa_run(State *s, long iters, double T0, double T1, State *bs) {
    int dup;
    long raw;
    long c = eval_cost(s, &dup, &raw);
    long bc = c;
    *bs = *s;
    if (c == 0) return 0;
    for (long t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        State old = *s;
        int K = s->K;
        if (K >= 2 && rint_(4) == 0) {
            int l = rint_(Dd);
            int i1 = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int tmp = s->P[l][i1];
            s->P[l][i1] = s->P[l][i2];
            s->P[l][i2] = tmp;
        } else {
            int l = rint_(Dd);
            int i = rint_(K);
            s->S[l][i] = rint_(G);
        }
        long c2 = eval_cost(s, &dup, &raw);
        long delta = c2 - c;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            c = c2;
            if (c < bc) {
                bc = c;
                *bs = *s;
            }
            if (c == 0) break;
        } else {
            *s = old;
        }
    }
    return bc;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long min_n = argc > 5 ? atol(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    deadline = now_s() + tl;

    long best_n = min_n;
    int have = 0;
    State bst;
    memset(&bst, 0, sizeof(bst));
    int bgt = 0, bp1 = 1, bp2 = 0, br = 0;

    int have_near = 0;
    long near_N = 0, near_c = 0;
    State nst;
    memset(&nst, 0, sizeof(nst));
    int ngt = 0, np1 = 1, np2 = 0, nr = 0;

    while (now_s() < deadline) {
        int roll = rint_(100);
        int K = roll < 45 ? 1 : (roll < 75 ? 2 : (roll < 90 ? 3 : 4));
        State cur;
        memset(&cur, 0, sizeof(cur));
        long iters;
        double T0v;
        int from_near = have_near && near_N > best_n && urand() < 0.4;
        if (from_near) {
            build_group(ngt, np1, np2, nr);
            cur = nst;
            perturb(&cur, 3);
            iters = NEAR_ITERS;
            T0v = 0.6;
        } else {
            long g0 = best_n / (2L * K) + 1;
            if (g0 > MAXG) continue;
            long span = g0 / 8 + 4;
            long Gt = g0 + (long)rint_((int)span);
            if (Gt > MAXG) Gt = MAXG;
            choose_group((int)Gt);
            if (2L * K * G <= best_n) continue;
            random_state(&cur, K);
            iters = SA_ITERS;
            T0v = 2.0;
        }

        State bs;
        memset(&bs, 0, sizeof(bs));
        sa_run(&cur, iters, T0v, 0.05, &bs);
        int dup;
        long raw;
        long cb = eval_cost(&bs, &dup, &raw);
        long N = 2L * bs.K * G;

        if (cb == 0) {
            if (N > best_n) {
                best_n = N;
                bst = bs;
                bgt = gtype;
                bp1 = gp1;
                bp2 = gp2;
                br = gr;
                have = 1;
                have_near = 0;
            }
        } else if (N > best_n) {
            if (!have_near || cb < near_c) {
                nst = bs;
                ngt = gtype;
                np1 = gp1;
                np2 = gp2;
                nr = gr;
                near_N = N;
                near_c = cb;
                have_near = 1;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    build_group(bgt, bp1, bp2, br);
    int K = bst.K;
    long n = 2L * K * G;
    long m = (long)Dd * K * G;
    printf("%ld %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bst.P[l][i], sv = bst.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + MTB[g * G + sv]);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then one C search run with the rest of the budget.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One C search run. Returns (n, edges) if it produced a valid larger graph, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # One C run: annealing over multi-block lifts, with group families
    # cyclic, Z_a x Z_b, and Z_m x| Z_k. It only returns graphs above best_n.
    if d >= 3 and D >= 3:
        budget = min(0.85 * time_limit, time_limit - 8.0) - (time.monotonic() - start) - 1.0
        if budget >= 3.0:
            res = _search(d, D, seed, budget, best_n)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
