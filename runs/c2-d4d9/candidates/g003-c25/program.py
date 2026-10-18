"""Program: bi-Cayley search over mixed group families (metacyclic and PSL/SL(2,q)).

Bold change from the parent (which only used PSL/SL(2,q), tried a few fixed orders,
and hill-climbed with a fixed 1% random-walk acceptance):
  * Connection-set search over a much wider family: random metacyclic groups
    Z_m x|_r Z_k (r^k = 1 mod m, gcd(r,m) = 1, abelian when r = 1), plus PSL/SL(2,q).
    Group orders are sampled in a window just above the record half-order (2485),
    biased toward the low end.
  * Simulated annealing over the 4-element connection set, with a temperature
    schedule that reheats every cycle, replacing the parent's plain hill-climb.
  * Each candidate group gets a time slice; after a success the window moves up
    (N > current best), so the engine keeps trying to grow the graph.
  * Fallback: if nothing beats the start graph, the C engine prints K_{d,d} and the
    Python side keeps the best valid graph (known start, else K_{d,d}).

Every graph is verified with lib.is_valid before it is returned.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search with annealing over metacyclic and PSL/SL(2,q) groups.
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": bipartite graph, degree d, diameter <= D.
 * Vertices: A_x = x, B_y = N + y. Edges: A_x -- B_{x*s_k}, k < d.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define QMAX 23

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group */

static int gtype = 0;          /* 0 = metacyclic, 1 = PSL/SL(2,q) */
static int N = 0, e_id = 0;

/* metacyclic Z_M x|_R Z_K, element (a,b) coded a*K+b, (a,b)(c,e) = (a + R^b c, b + e) */
static int M_ = 1, K_ = 1, R_ = 1;
static int pw[64];

static int mc_mul(int x, int y) {
    int a = x / K_, b = x % K_, c = y / K_, dd = y % K_;
    int aa = (a + (pw[b] * c) % M_) % M_;
    int bb = (b + dd) % K_;
    return aa * K_ + bb;
}
static int mc_inv(int x) {
    int a = x / K_, b = x % K_;
    int nb = (K_ - b) % K_;
    int na = (M_ - (pw[nb] * a) % M_) % M_;
    return na * K_ + nb;
}

/* PSL/SL(2,q) */
static int qg = 0, psl_g = 0;
static int gm[MAXN][4];
static int idx_tab[QMAX * QMAX * QMAX * QMAX];

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}
static int lookup_psl(int a, int b, int c, int e) { return idx_tab[canon_key(a, b, c, e)]; }

static int psl_build(int qq, int psl) {
    qg = qq;
    psl_g = psl;
    int ks = qq * qq * qq * qq;
    for (int i = 0; i < ks; i++) idx_tab[i] = -1;
    N = 0;
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++)
            for (int c = 0; c < qq; c++)
                for (int e = 0; e < qq; e++) {
                    if ((((a * e - b * c) % qq) + qq) % qq != 1) continue;
                    int own = ((a * qq + b) * qq + c) * qq + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (N >= MAXN) return 0;
                    gm[N][0] = a; gm[N][1] = b; gm[N][2] = c; gm[N][3] = e;
                    idx_tab[own] = N;
                    N++;
                }
    e_id = lookup_psl(1, 0, 0, 1);
    return N;
}
static int psl_mul(int x, int y) {
    int q = qg;
    int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
    int sa = gm[y][0], sb = gm[y][1], sc = gm[y][2], se = gm[y][3];
    return lookup_psl((a * sa + b * sc) % q, (a * sb + b * se) % q,
                      (c * sa + e * sc) % q, (c * sb + e * se) % q);
}
static int psl_inv(int x) {
    int q = qg;
    return lookup_psl(gm[x][3], (q - gm[x][1]) % q, (q - gm[x][2]) % q, gm[x][0]);
}

static int gmul(int x, int y) { return gtype == 0 ? mc_mul(x, y) : psl_mul(x, y); }
static int ginv(int x) { return gtype == 0 ? mc_inv(x) : psl_inv(x); }

typedef struct { int type, m, k, r, q, psl, N; } Cand;

static int setup_group(const Cand *c) {
    gtype = c->type;
    if (gtype == 0) {
        M_ = c->m;
        K_ = c->k;
        R_ = c->r;
        if (K_ < 1 || K_ > 63 || M_ < 2 || M_ * K_ > MAXN) return 0;
        N = M_ * K_;
        long p = 1 % M_;
        for (int b = 0; b < K_; b++) {
            pw[b] = (int)p;
            p = p * R_ % M_;
        }
        e_id = 0;
        return 1;
    }
    if (c->q > QMAX) return 0;
    if (psl_build(c->q, c->psl) != c->N) return 0;
    return 1;
}

/* ------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = ginv(s);
    for (int x = 0; x < N; x++) {
        Rr[k][x] = gmul(x, s);
        Ri[k][x] = gmul(x, si);
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs; 0 means diameter <= D. */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

/* ------------------------------------------------------------ annealing */

static int anneal(double until) {
    randomize_S();
    long cur = cost_now();
    if (cur == 0) return 1;
    const double Thi = 1.5, Tlo = 0.05;
    const long L = 40000;
    long step = 0;
    for (;;) {
        if ((step & 127) == 0 && now() > until) return 0;
        double frac = (double)(step % L) / (double)L;
        double T = Thi * pow(Tlo / Thi, frac);
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        int accept = 0;
        if (nc <= cur) accept = 1;
        else if (rnd01() < exp(-(double)(nc - cur) / T)) accept = 1;
        if (accept) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            S[k] = old;
            set_col(k);
        }
        step++;
    }
}

/* ------------------------------------------------------------ candidates */

static int gen_cand(long lo, long hi, Cand *c) {
    static const int qs[5] = {11, 13, 17, 19, 23};
    for (int att = 0; att < 300; att++) {
        if (rnd01() < 0.2) {
            int qq = qs[rndint(5)];
            int psl = rndint(2);
            long ord = (long)qq * ((long)qq * qq - 1);
            if (psl) ord /= 2;
            if (ord >= lo && ord <= hi && ord <= MAXN) {
                memset(c, 0, sizeof *c);
                c->type = 1; c->q = qq; c->psl = psl; c->N = (int)ord;
                return 1;
            }
            continue;
        }
        int k = 2 + rndint(39);
        long mlo = (lo + k - 1) / k, mhi = hi / k;
        if (mhi < mlo || mhi < 2) continue;
        double u = rnd01();
        long m = mlo + (long)((double)(mhi - mlo) * u * u);
        if (m > mhi) m = mhi;
        if (m < 2) continue;
        long r = 1;
        for (int t = 0; t < 80; t++) {
            long rr = 1 + rndint((int)(m - 1));
            if (gcdl(rr, m) == 1 && powmod(rr, k, m) == 1 % m) { r = rr; break; }
        }
        long ordr = m * k;
        if (ordr < lo || ordr > hi) continue;
        memset(c, 0, sizeof *c);
        c->type = 0; c->m = (int)m; c->k = k; c->r = (int)r; c->N = (int)ordr;
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long maxhalf = moore / 2;

    int have = 0;
    Cand bestC;
    memset(&bestC, 0, sizeof bestC);
    int bestS[MAXDEG];
    int bestN = 0;

    double tphase = t_end - now();
    double tstart = now();
    int iter = 0;
    while (1) {
        double remaining = t_end - now();
        if (remaining < 0.5) break;
        if (++iter > 20000) break;

        long lo, hi;
        if (have) lo = (long)bestN + 1;
        else lo = (now() - tstart < 0.45 * tphase) ? 2486 : 1000;
        hi = lo + (have ? 400 : 1000);
        if (hi > maxhalf) hi = maxhalf;
        if (hi > MAXN) hi = MAXN;
        if (lo > hi) break;

        Cand c;
        if (!gen_cand(lo, hi, &c)) continue;

        double slice = remaining / 4.0;
        if (slice < 2.5) slice = remaining;
        if (slice > remaining) slice = remaining;

        if (!setup_group(&c)) continue;
        if (anneal(now() + slice)) {
            have = 1;
            bestN = N;
            bestC = c;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (!have) {
        print_complete();
        return 0;
    }
    setup_group(&bestC);
    memcpy(S, bestS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    complete = lib.haar_graph(d, range(d))             # K_{d,d}: always valid
    start = known_start(d, D)
    best = complete
    if start is not None and lib.is_valid(start[0], start[1], d, D):
        best = start

    budget = 0.9 * time_limit - 3.0 - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 3.0)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
