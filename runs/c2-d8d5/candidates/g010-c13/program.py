import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lift search over semidirect products.
#
# A candidate is (k, m, k2, r): base k blocks per side, group G = Z_m x| Z_k2
# with r^k2 = 1 mod m, element a*k2+b. Each layer l gives a permutation
# perm[l][i] of the k B-blocks and a voltage S[l][i] in G. A-vertex (i,g) is
# joined to (perm[l][i], g*S) for each layer l, so the graph is d-regular and
# bipartite with 2*k*G vertices. Left multiplication is an automorphism, so the
# diameter is at most D iff every one of the 2k base vertices reaches the whole
# graph within D steps. The cost is the total number of unreached vertices from
# those sources, plus a heavy penalty per duplicate dart.
#
# Candidates are generated in C in ascending order of order N and scheduled
# with a small window of the lowest unsolved candidates, each given a
# doubling simulated-annealing slice. The best valid lift found is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 6
#define WIN 8
#define CAND_CAP 400000
#define RCAP 3
#define SLICE0 0.05
#define SLICEMAX 8.0

typedef uint64_t u64;
typedef struct { int N, k, m, k2, r; } Cand;

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnddbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_;
static int k_, m_, k2_, r_, G_, N_;
static int cap_N, cap_G;
static int *pw_, *invs_;
static int *perm_, *S_;
static int *nbr_, *mark_, *queue_;
static int stamp_ = 0;

static int best_n = 0, best_m = 0;
static int *best_eu = NULL, *best_ev = NULL;

static Cand *cands = NULL;
static int ncand = 0;
static int next_idx = 0;

static long long gcd_ll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product: (a,b)(c,e) = (a + r^b c, b + e). Element index a*k2 + b. */
static int gmul(int x, int y) {
    int K = k2_, M = m_;
    int a = x / K, b = x - a * K;
    int c = y / K, e = y - c * K;
    int aa = (int)((a + (long long)pw_[b] * c) % M);
    int bb = b + e;
    if (bb >= K) bb -= K;
    return aa * K + bb;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), with r^{-b} = r^{k2-b}. */
static int ginv(int x) {
    int K = k2_, M = m_;
    int a = x / K, b = x - a * K;
    int nb = (K - b) % K;
    int c = (int)(((long long)((M - a) % M)) * pw_[nb] % M);
    return c * K + nb;
}

static void set_cand(Cand c) {
    k_ = c.k; m_ = c.m; k2_ = c.k2; r_ = c.r;
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    pw_[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw_[b] = (int)((long long)pw_[b - 1] * r_ % m_);
    for (int s = 0; s < G_; s++) invs_[s] = ginv(s);
}

static void rebuild(void) {
    const int d = d_, k = k_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = perm_[l * k + i];
            int s = S_[l * k + i];
            int si = invs_[s];
            int ba = i * G, bb = (k + j) * G;
            for (int g = 0; g < G; g++) {
                nbr_[(size_t)(ba + g) * d + l] = bb + gmul(g, s);
                nbr_[(size_t)(bb + g) * d + l] = ba + gmul(g, si);
            }
        }
    }
}

/* Number of duplicate darts: same A-block, same B-block, same voltage. */
static long long dupcount(void) {
    const int d = d_, k = k_;
    long long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm_[l1 * k + i] == perm_[l2 * k + i] &&
                    S_[l1 * k + i] == S_[l2 * k + i])
                    c++;
    return c;
}

static long long evaluate(void) {
    rebuild();
    const int d = d_, k = k_, G = G_, N = N_;
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        stamp_++;
        mark_[src] = stamp_;
        queue_[0] = src;
        int tail = 1, ls = 0, le = 1;
        for (int depth = 0; depth < D_ && ls < le; depth++) {
            for (int h = ls; h < le; h++) {
                const int *nv = nbr_ + (size_t)queue_[h] * d;
                for (int l = 0; l < d; l++) {
                    int u = nv[l];
                    if (mark_[u] != stamp_) {
                        mark_[u] = stamp_;
                        queue_[tail++] = u;
                    }
                }
            }
            ls = le;
            le = tail;
        }
        cost += N - tail;
    }
    return cost + dupcount() * (long long)(2 * N + 50);
}

static void random_state(void) {
    const int d = d_, k = k_, G = G_;
    for (int l = 0; l < d; l++) {
        int *p = perm_ + l * k;
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
    }
    for (int t = 0; t < d * k; t++) S_[t] = rndint(G);
}

/* Simulated annealing on the current candidate. Returns 1 on success; the
   accepted zero-cost state is then in nbr_ / perm_ / S_. */
static int anneal(double seconds) {
    const int d = d_, k = k_, G = G_, N = N_;
    random_state();
    long long cur = evaluate();
    if (cur == 0) return 1;
    double T0 = 0.02 * N + 1.0, T1 = 0.3, T = T0;
    clock_t c0 = clock();
    double span = seconds * CLOCKS_PER_SEC;
    long long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - c0);
            if (el >= span) break;
            T = T0 * pow(T1 / T0, el / span);
        }
        it++;
        if (k >= 2 && (rnd64() & 1)) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int ia = l * k + i1, ib = l * k + i2;
            int t = perm_[ia]; perm_[ia] = perm_[ib]; perm_[ib] = t;
            long long nc = evaluate();
            if (nc <= cur || rnddbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                t = perm_[ia]; perm_[ia] = perm_[ib]; perm_[ib] = t;
            }
        } else {
            int idx = rndint(d * k);
            int old = S_[idx];
            int ns = rndint(G);
            if (ns == old) continue;
            S_[idx] = ns;
            long long nc = evaluate();
            if (nc <= cur || rnddbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                S_[idx] = old;
            }
        }
    }
    return 0;
}

static void store_best(void) {
    const int d = d_, k = k_, G = G_;
    int nA = k * G;
    int cnt = nA * d;
    if (cnt <= 0) return;
    int *eu = malloc(sizeof(int) * (size_t)cnt);
    int *ev = malloc(sizeof(int) * (size_t)cnt);
    if (!eu || !ev) { free(eu); free(ev); return; }
    int m = 0;
    for (int v = 0; v < nA; v++)
        for (int l = 0; l < d; l++) {
            eu[m] = v;
            ev[m] = nbr_[(size_t)v * d + l];
            m++;
        }
    free(best_eu);
    free(best_ev);
    best_eu = eu;
    best_ev = ev;
    best_n = N_;
    best_m = m;
}

static void add_cand(int N, int k, int m, int k2, int r) {
    if (ncand >= CAND_CAP) return;
    cands[ncand].N = N;
    cands[ncand].k = k;
    cands[ncand].m = m;
    cands[ncand].k2 = k2;
    cands[ncand].r = r;
    ncand++;
}

/* Candidates in ascending order of N. */
static void gen_cands(int lo, int hi) {
    for (int N = lo; N <= hi; N++) {
        for (int k = 1; k <= KMAX; k++) {
            if (N % (2 * k)) continue;
            int G = N / (2 * k);
            for (int m = 1; m <= G; m++) {
                if (G % m) continue;
                int k2 = G / m;
                if (m == 1) { add_cand(N, k, 1, k2, 0); continue; }
                int ch[RCAP];
                int nch = 0;
                long long seen = 0;
                for (int r = 1; r < m; r++) {
                    if (gcd_ll(r, m) != 1) continue;
                    if (powmod(r, k2, m) != 1) continue;
                    seen++;
                    if (nch < RCAP) {
                        ch[nch++] = r;
                    } else {
                        int j = rndint((int)seen);
                        if (j < RCAP) ch[j] = r;
                    }
                }
                for (int q = 0; q < nch; q++) add_cand(N, k, m, k2, ch[q]);
            }
        }
    }
}

static int next_cand(void) {
    while (next_idx < ncand) {
        int c = next_idx++;
        if (cands[c].N > best_n) return c;
    }
    return -1;
}

static void schedule(double budget) {
    int slot[WIN];
    double sl[WIN];
    for (int s = 0; s < WIN; s++) {
        slot[s] = next_cand();
        sl[s] = SLICE0;
    }
    clock_t start = clock();
    for (;;) {
        double el = (double)(clock() - start) / CLOCKS_PER_SEC;
        double rem = budget - el;
        if (rem <= 0.05) break;
        int any = 0;
        for (int s = 0; s < WIN; s++) {
            if (slot[s] >= 0 && cands[slot[s]].N <= best_n) slot[s] = -1;
            if (slot[s] < 0) {
                slot[s] = next_cand();
                sl[s] = SLICE0;
            }
            if (slot[s] < 0) continue;
            el = (double)(clock() - start) / CLOCKS_PER_SEC;
            rem = budget - el;
            if (rem <= 0.05) break;
            any = 1;
            double span = sl[s] < rem ? sl[s] : rem;
            set_cand(cands[slot[s]]);
            if (anneal(span)) {
                store_best();
                slot[s] = -1;
            } else {
                sl[s] *= 2.0;
                if (sl[s] > SLICEMAX) sl[s] = SLICEMAX;
            }
        }
        if (!any) break;
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d_ < 1 || D_ < 1 || lo < 2 || hi < lo || hi > 4000) { printf("0 0\n"); return 0; }

    cap_N = hi + 4;
    cap_G = hi / 2 + 4;
    pw_ = malloc(sizeof(int) * (size_t)cap_G);
    invs_ = malloc(sizeof(int) * (size_t)cap_G);
    perm_ = malloc(sizeof(int) * (size_t)d_ * KMAX);
    S_ = malloc(sizeof(int) * (size_t)d_ * KMAX);
    nbr_ = malloc(sizeof(int) * (size_t)cap_N * d_);
    mark_ = calloc((size_t)cap_N, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)cap_N);
    cands = malloc(sizeof(Cand) * CAND_CAP);
    if (!pw_ || !invs_ || !perm_ || !S_ || !nbr_ || !mark_ || !queue_ || !cands) {
        printf("0 0\n");
        return 0;
    }

    gen_cands(lo, hi);
    schedule(budget);

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _lift_search(d, D, seed, seconds, lo, hi):
    """Run the C lift search; returns (n, edges), with (0, []) when nothing was found."""
    out = lib.run_c(C_SOURCE, [d, D, int(seed) % (1 << 40), f"{seconds:.2f}", lo, hi],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Exact construction for the calibration case: return immediately.
        if lib.is_prime_power(d - 1):
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            return best
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: voltage lifts over semidirect products, run in C.
    margin = 3.0 + 0.05 * time_limit
    budget = time_limit - (time.monotonic() - t0) - margin
    if budget >= 1.0:
        lo = 2 * d
        hi = min(lib.moore_bound(d, D), 3000)
        if hi >= lo:
            try:
                n, e = _lift_search(d, D, seed, budget, lo, hi)
                consider(n, e)
            except Exception:
                pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
