"""Program: multi-base voltage lifts over metacyclic groups, with simulated annealing.

Construction (new in this version):
  * Base graph: s vertices per side (s = 1..4), every vertex of degree d. Slot (i, k) of A_i
    joins B_{J[i][k]} with voltage G[i][k] in a group G of order N. The lift has 2*s*N
    vertices: A_i(x) = i*N + x, B_j(y) = (s+j)*N + y. Edge: A_i(x) -- B_j(x*g).
  * Left multiplication is an automorphism of the lift, so the diameter is <= D iff a BFS
    from A_i(e) and from B_j(e) (for every base vertex) reaches all vertices within D steps.
  * s = 1 is the bi-Cayley case already used by the parent. s >= 2 gives genuinely
    different base structure, which the parent never explored.
  * Groups: metacyclic Z_m x| Z_k (r = 1 gives direct products), evaluated through formulas,
    not multiplication tables.
  * Search: simulated annealing over voltages and base-target swaps (degree balance is
    preserved), with a penalty for parallel darts. Cost = unreached pairs + penalty.
  * Schedule: baseline valid graphs first, then candidates just below the reference order
    (closest first), then just above it (smallest first), using iterative-deepening slices.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or a single edge.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXS 4
#define MAXD 8
#define MAXN 4096
#define MAXV (2 * MAXS * MAXN)
#define MAXCAND 4096
#define PEN 1000000L
#define T_HI 4.0
#define T_LO 0.15
#define CYCLES 3.0

static int d, D;
static double t_end;
static long moore_g = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int gm_m = 2, gm_k = 1, gm_r = 1, N = 2;
static int pw[MAXN];

/* element (a,b) coded as a*k+b; (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / gm_k, b = x % gm_k;
    int c = y / gm_k, e = y % gm_k;
    int aa = (a + pw[b] * c) % gm_m;
    int bb = (b + e) % gm_k;
    return aa * gm_k + bb;
}

static int ginv(int x) {
    int a = x / gm_k, b = x % gm_k;
    int nb = (gm_k - b) % gm_k;
    int c = (int)((gm_m - ((long)pw[nb] * a) % gm_m) % gm_m);
    return c * gm_k + nb;
}

static int set_group(int m, int k, int r) {
    if (m < 2 || k < 1 || (long)m * k > MAXN) return 0;
    gm_m = m;
    gm_k = k;
    gm_r = r;
    N = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    return 1;
}

/* Random metacyclic group of order Nv (mostly random r when k > 1). */
static void pick_group(int Nv, int *pm, int *pk, int *pr) {
    int divs[64];
    int nd = 0;
    for (int k = 1; k <= Nv && nd < 64; k++)
        if (Nv % k == 0 && Nv / k >= 2) divs[nd++] = k;
    int k = divs[rndint(nd)];
    int m = Nv / k;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int tries = 0; tries < 200; tries++) {
            int c = 2 + rndint(m - 2);
            if (gcd_l(c, m) == 1 && powmod_l(c, k, m) == 1) { r = c; break; }
        }
    }
    *pm = m;
    *pk = k;
    *pr = r;
}

/* ------------------------------------------------------------ lift state */

static int s = 1, V = 2;
static int J[MAXS][MAXD], G[MAXS][MAXD];
static int RA[MAXS][MAXD][MAXN];    /* RA[i][k][x]  = x * g     (A -> B) */
static int RBk[MAXS][MAXD][MAXN];   /* RBk[i][k][y] = y * g^-1  (B -> A) */
static int BI[MAXS][MAXD], BK[MAXS][MAXD];   /* incoming slots of B_j */

static void set_slot_G(int i, int k, int g) {
    G[i][k] = g;
    int gi = ginv(g);
    for (int x = 0; x < N; x++) {
        RA[i][k][x] = gmul(x, g);
        RBk[i][k][x] = gmul(x, gi);
    }
}

static void rebuild_B(void) {
    int cnt[MAXS];
    for (int j = 0; j < s; j++) cnt[j] = 0;
    for (int i = 0; i < s; i++)
        for (int k = 0; k < d; k++) {
            int j = J[i][k];
            BI[j][cnt[j]] = i;
            BK[j][cnt[j]] = k;
            cnt[j]++;
        }
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < s; i++)
        for (int k = 0; k < d; k++)
            for (int k2 = k + 1; k2 < d; k2++)
                if (J[i][k] == J[i][k2] && G[i][k] == G[i][k2]) c++;
    return c;
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int qv[MAXV];
static int tick = 0;

static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    int sN = s * N;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < sN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int u = (s + J[i][k]) * N + RA[i][k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - sN;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int i = BI[j][t], k = BK[j][t];
                    int u = i * N + RBk[i][k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from every base-vertex representative, plus duplicate-edge penalty. */
static long cost_eval(void) {
    long c = PEN * dup_count();
    for (int u = 0; u < 2 * s; u++)
        c += (long)(V - ball(u * N));
    return c;
}

/* ------------------------------------------------------------ search */

static void randomize(void) {
    static int L[MAXS * MAXD];
    int tot = s * d;
    for (int t = 0; t < tot; t++) L[t] = t / d;   /* each base vertex appears d times */
    for (int t = tot - 1; t > 0; t--) {
        int r = rndint(t + 1);
        int tmp = L[t]; L[t] = L[r]; L[r] = tmp;
    }
    for (int i = 0; i < s; i++)
        for (int k = 0; k < d; k++) {
            J[i][k] = L[i * d + k];
            set_slot_G(i, k, rndint(N));
        }
    rebuild_B();
}

static int bJ[MAXS][MAXD], bG[MAXS][MAXD];

/* Simulated annealing with sawtooth reheating. Leaves a valid state in place on success. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize();
    long cur = cost_eval();
    long bestc = cur;
    memcpy(bJ, J, sizeof J);
    memcpy(bG, G, sizeof G);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        if (s == 1 || rnd01() < 0.5) {
            int i = rndint(s), k = rndint(d);
            int og = G[i][k];
            set_slot_G(i, k, rndint(N));
            long nc = cost_eval();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) cur = nc;
            else set_slot_G(i, k, og);
        } else {
            int i1 = rndint(s), k1 = rndint(d), i2 = rndint(s), k2 = rndint(d);
            if (J[i1][k1] == J[i2][k2]) continue;
            int j1 = J[i1][k1];
            J[i1][k1] = J[i2][k2];
            J[i2][k2] = j1;
            rebuild_B();
            long nc = cost_eval();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                j1 = J[i1][k1];
                J[i1][k1] = J[i2][k2];
                J[i2][k2] = j1;
                rebuild_B();
            }
        }
        if (cur < bestc) {
            bestc = cur;
            memcpy(bJ, J, sizeof J);
            memcpy(bG, G, sizeof G);
        }
    }
    if (bestc != 0) return 0;
    memcpy(J, bJ, sizeof J);
    for (int i = 0; i < s; i++)
        for (int k = 0; k < d; k++) set_slot_G(i, k, bG[i][k]);
    rebuild_B();
    return 1;
}

/* ------------------------------------------------------------ best record */

typedef struct { int s, m, k, r; } Cand;

static int have = 0;
static int bestT = 0;
static int bsS, bsM, bsK, bsR;
static int bsJ[MAXS][MAXD], bsG[MAXS][MAXD];

static int try_cand(const Cand *c, double until) {
    if (!set_group(c->m, c->k, c->r)) return 0;
    s = c->s;
    V = 2 * s * N;
    if (!climb(until)) return 0;
    have = 1;
    bestT = V;
    bsS = s;
    bsM = gm_m;
    bsK = gm_k;
    bsR = gm_r;
    memcpy(bsJ, J, sizeof J);
    memcpy(bsG, G, sizeof G);
    return 1;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

typedef struct { int grp; long T; int s; int N; } Ent;

static int cmp_ent(const void *a, const void *b) {
    const Ent *x = a, *y = b;
    if (x->grp != y->grp) return x->grp < y->grp ? -1 : 1;
    if (x->grp == 0) return (x->T > y->T) ? -1 : (x->T < y->T);   /* below ref: closest first */
    return (x->T < y->T) ? -1 : (x->T > y->T);                    /* above ref: smallest first */
}

static Ent ents[MAXCAND];
static Cand cands[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    moore_g = moore;

    long refc = ref;
    if (refc <= 0) refc = moore / 4;
    if (refc > moore) refc = moore;
    if (refc > MAXV) refc = MAXV;
    if (refc < 2L * d) refc = 2L * d;

    /* Window: below the reference (closest first), then just above it (smallest first). */
    long lo = (long)(0.97 * (double)refc);
    long hi = (long)(1.04 * (double)refc);
    if (hi > moore) hi = moore;
    if (hi > MAXV) hi = MAXV;

    int ne = 0;
    for (int ss = 1; ss <= MAXS; ss++) {
        long nlo = lo / (2L * ss);
        if (nlo < 2) nlo = 2;
        long nhi = hi / (2L * ss);
        if (nhi > MAXN) nhi = MAXN;
        for (long Nv = nlo; Nv <= nhi && ne < MAXCAND; Nv++) {
            long T = 2L * ss * Nv;
            if (T < lo || T > hi) continue;
            ents[ne].T = T;
            ents[ne].s = ss;
            ents[ne].N = (int)Nv;
            ents[ne].grp = (T <= refc) ? 0 : 1;
            ne++;
        }
    }
    qsort(ents, (size_t)ne, sizeof(Ent), cmp_ent);

    int ncand = 0;
    for (int e = 0; e < ne && ncand < MAXCAND; e++) {
        Cand c;
        c.s = ents[e].s;
        pick_group(ents[e].N, &c.m, &c.k, &c.r);
        cands[ncand++] = c;
    }

    double budget = t_end - now();

    /* Baseline: a few valid s = 1 graphs at moderate orders, so something valid exists early. */
    {
        static const double fr[3] = {0.5, 0.75, 0.9};
        for (int f = 0; f < 3; f++) {
            double remaining = t_end - now();
            if (remaining < 1.0) break;
            long Nv = (long)(fr[f] * (double)refc) / 2;
            if (Nv > MAXN) Nv = MAXN;
            if (Nv < 2 || 2 * Nv > moore) continue;
            if (2 * Nv <= bestT) continue;
            Cand c;
            c.s = 1;
            pick_group((int)Nv, &c.m, &c.k, &c.r);
            double slice = budget * 0.02;
            if (slice < 0.3) slice = 0.3;
            if (slice > remaining * 0.5) slice = remaining * 0.5;
            try_cand(&c, now() + slice);
        }
    }

    /* Iterative deepening: slices double per round; candidates at or below bestT are skipped. */
    double base = budget * 0.01;
    if (base < 0.2) base = 0.2;
    for (int round = 0; round < 8; round++) {
        for (int ci = 0; ci < ncand; ci++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[ci];
            if (2 * c->s * (c->m * c->k) <= bestT) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            try_cand(c, now() + slice);
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }

    s = bsS;
    set_group(bsM, bsK, bsR);
    V = 2 * s * N;
    memcpy(J, bsJ, sizeof J);
    for (int i = 0; i < s; i++)
        for (int k = 0; k < d; k++) set_slot_G(i, k, bsG[i][k]);
    rebuild_B();
    if (cost_eval() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", V, (long)s * N * d);
    for (int i = 0; i < s; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, (s + J[i][k]) * N + RA[i][k][x]);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _safe_fallback(d, D):
    """A trivially valid graph: K_{d,d} when D >= 2, otherwise one edge."""
    if D >= 2:
        g = lib.haar_graph(d, range(d))
        if lib.is_valid(g[0], g[1], d, D):
            return g
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = _safe_fallback(d, D)
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
