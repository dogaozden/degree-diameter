import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Combined program.
#
# Engine: bi-Cayley simulated annealing over Z_m x| Z_k2 in C. Each trial uses
# breakout-style vertex weights: a vertex that stays short of full reach at a
# local minimum gets its weight raised, which pushes the search out of plateaus.
# The true cost (unreached pairs + duplicate-dart penalty) is tracked separately
# for best-state bookkeeping, so a zero-cost state is still a valid graph.
# A bandit picks the base size k (1..8), groups are sampled near the current
# record order, and an elite refinement step restarts from the best voltage
# state of a near-miss trial (perturbing 1-3 darts) and anneals again.
#
# Start graph: exact constructions (PG(2,q), W(q)) when they apply, else K_{d,d}.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000L
#define KMAX 8
#define ELITE_ROUNDS 3
#define ELITE_ITERS 1500
#define ELITE_PATIENCE 600
#define ELITE_THR 30
#define BREAK_STALL 150

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 88172645463325252ULL;

/* group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static int64_t PW[64];

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_edges = NULL;

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (-(PW[nb] * (int64_t)a)) % GM;
    if (t < 0) t += GM;
    return (int)(t * GK + nb);
}

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = (p * r) % m;
    }
}

static const int KCH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = KCH[rnd(20)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.3) {
            r = m - 1;
            if (gcd64(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rnd((uint64_t)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) {
        c += (int)(x & 1u);
        x >>= 1;
    }
    return c;
}

/* A-block i (vertices i*GG..) joins B-block j = lay[l][i] with voltage s = S[l][i]. */
static void set_dart(int **nbr, const int *lay, const int *S, int k, int l, int i) {
    int j = lay[l * k + i];
    int s = S[l * k + i];
    int si = ginv(s);
    int Ab = i * GG, Bb = (k + j) * GG;
    int *nb = nbr[l];
    for (int g = 0; g < GG; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, si);
    }
}

/* out[v] = bitmask of representative blocks within distance D of v. */
static void compute_reach(int **nbr, int d, int k, int N, int D, uint32_t *out, uint32_t *tmp) {
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * GG] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = out[v];
            for (int l = 0; l < d; l++) r |= out[nbr[l][v]];
            tmp[v] = r;
            if (r != out[v]) changed = 1;
        }
        memcpy(out, tmp, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static long unreached(const uint32_t *reach, int k, int N) {
    long s = 0;
    for (int v = 0; v < N; v++) s += popc(reach[v]);
    return 2L * k * N - s;
}

static long dupcount(const int *lay, const int *S, int d, int k) {
    int tot = d * k;
    long dup = 0;
    for (int a = 0; a < tot; a++) {
        int la = a / k, ia = a % k;
        for (int b = 0; b < a; b++) {
            int lb = b / k, ib = b % k;
            if (ia == ib && lay[la * k + ia] == lay[lb * k + ib] && S[la * k + ia] == S[lb * k + ib]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

/* Weighted missing-reach cost: sum over vertices of W[v] * (missing representative blocks). */
static long wcost(const uint32_t *reach, const int *W, int k, int N) {
    long s = 0;
    for (int v = 0; v < N; v++) s += (long)W[v] * (long)(2 * k - popc(reach[v]));
    return s;
}

/* Evaluate the current configuration: rr receives the reach masks,
   *tru the true cost, *wc the weighted cost used for acceptance. */
static void evalc(int **nbr, int d, int k, int N, int D, const int *lay, const int *S,
                  const int *W, uint32_t *rr, uint32_t *tmp, long *wc, long *tru) {
    compute_reach(nbr, d, k, N, D, rr, tmp);
    long dp = dupcount(lay, S, d, k);
    long un = unreached(rr, k, N);
    *tru = un + PENALTY * dp;
    *wc = wcost(rr, W, k, N) + PENALTY * dp;
}

static void store_best(int **nbr, int d, int k) {
    long A = (long)k * GG;
    long n = 2 * A;
    if (n <= g_best_n) return;
    long cnt = A * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < A; u++) {
        for (int l = 0; l < d; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = nbr[l][u];
            c++;
        }
    }
    free(g_edges);
    g_edges = e;
    g_best_m = cnt;
    g_best_n = n;
}

/* Anneal one configuration on the current group with breakout weights.
   If init_lay/init_S are given, start from a copy of them with `perturb`
   random changes; otherwise start random. Writes the best true-cost
   configuration into out_lay/out_S and its true cost into out_cost.
   Returns 1 if a zero-cost (valid) graph was reached (and stored). */
static int run_trial(int d, int D, int k, int iters, int patience,
                     const int *init_lay, const int *init_S, int perturb,
                     int *out_lay, int *out_S, long *out_cost) {
    int N = 2 * k * GG;
    uint32_t full = (1u << (2 * k)) - 1u;
    int K = d * k;
    int *lay = malloc(sizeof(int) * (size_t)K);
    int *S = malloc(sizeof(int) * (size_t)K);
    int *blay = malloc(sizeof(int) * (size_t)K);
    int *bS = malloc(sizeof(int) * (size_t)K);
    int **nbr = malloc(sizeof(int *) * (size_t)d);
    uint32_t *rc = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *rn = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *tmp = malloc(sizeof(uint32_t) * (size_t)N);
    int *W = malloc(sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++) nbr[l] = malloc(sizeof(int) * (size_t)N);

    if (init_lay && init_S) {
        memcpy(lay, init_lay, sizeof(int) * (size_t)K);
        memcpy(S, init_S, sizeof(int) * (size_t)K);
        for (int p = 0; p < perturb; p++) {
            if (k >= 2 && rndf() < 0.3) {
                int l = (int)rnd((uint64_t)d);
                int i1 = (int)rnd((uint64_t)k);
                int i2 = (int)rnd((uint64_t)(k - 1));
                if (i2 >= i1) i2++;
                int tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
            } else {
                S[rnd((uint64_t)K)] = (int)rnd((uint64_t)GG);
            }
        }
    } else {
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) lay[l * k + i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = (int)rnd((uint64_t)(i + 1));
                int t = lay[l * k + i];
                lay[l * k + i] = lay[l * k + j];
                lay[l * k + j] = t;
            }
        }
        for (int q = 0; q < K; q++) S[q] = (int)rnd((uint64_t)GG);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(nbr, lay, S, k, l, i);

    for (int v = 0; v < N; v++) W[v] = 1;
    long wc = 0, tru = 0;
    evalc(nbr, d, k, N, D, lay, S, W, rc, tmp, &wc, &tru);
    long best_tru = tru;
    memcpy(blay, lay, sizeof(int) * (size_t)K);
    memcpy(bS, S, sizeof(int) * (size_t)K);
    double c0 = wc > 1 ? (double)wc : 1.0;
    int last = 0;
    int stall = 0;

    for (int t = 0; t < iters && tru != 0; t++) {
        if (elapsed() > g_budget) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        long c2w = 0, c2t = 0;
        if (k >= 2 && rndf() < 0.25) {
            /* layer-swap move */
            int l = (int)rnd((uint64_t)d);
            int i1 = (int)rnd((uint64_t)k);
            int i2 = (int)rnd((uint64_t)(k - 1));
            if (i2 >= i1) i2++;
            int tv = lay[l * k + i1];
            lay[l * k + i1] = lay[l * k + i2];
            lay[l * k + i2] = tv;
            set_dart(nbr, lay, S, k, l, i1);
            set_dart(nbr, lay, S, k, l, i2);
            evalc(nbr, d, k, N, D, lay, S, W, rn, tmp, &c2w, &c2t);
            if (c2w <= wc || rndf() < exp(-(double)(c2w - wc) / temp)) {
                wc = c2w;
                tru = c2t;
                uint32_t *p = rc;
                rc = rn;
                rn = p;
                if (tru < best_tru) {
                    best_tru = tru;
                    last = t;
                    stall = 0;
                    memcpy(blay, lay, sizeof(int) * (size_t)K);
                    memcpy(bS, S, sizeof(int) * (size_t)K);
                } else {
                    stall++;
                }
            } else {
                tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
                set_dart(nbr, lay, S, k, l, i1);
                set_dart(nbr, lay, S, k, l, i2);
                stall++;
            }
        } else {
            /* voltage move: defect-targeted with probability 0.4 */
            int l = 0, i = 0;
            int picked = 0;
            if (rndf() < 0.4) {
                long nbad = 0;
                for (int v = 0; v < N; v++)
                    if (rc[v] != full) nbad++;
                if (nbad > 0) {
                    long pick = (long)rnd((uint64_t)nbad);
                    int u = -1;
                    for (int v = 0; v < N; v++) {
                        if (rc[v] != full) {
                            if (pick == 0) {
                                u = v;
                                break;
                            }
                            pick--;
                        }
                    }
                    int block = u / GG;
                    l = (int)rnd((uint64_t)d);
                    if (block < k) {
                        i = block;
                    } else {
                        i = -1;
                        for (int q = 0; q < k; q++) {
                            if (lay[l * k + q] == block - k) {
                                i = q;
                                break;
                            }
                        }
                        if (i < 0) i = 0;
                    }
                    picked = 1;
                }
            }
            if (!picked) {
                l = (int)rnd((uint64_t)d);
                i = (int)rnd((uint64_t)k);
            }

            int old = S[l * k + i];
            int nw = (int)rnd((uint64_t)GG);
            if (nw == old) {
                stall++;
                continue;
            }
            S[l * k + i] = nw;
            set_dart(nbr, lay, S, k, l, i);
            evalc(nbr, d, k, N, D, lay, S, W, rn, tmp, &c2w, &c2t);
            if (c2w <= wc || rndf() < exp(-(double)(c2w - wc) / temp)) {
                wc = c2w;
                tru = c2t;
                uint32_t *p = rc;
                rc = rn;
                rn = p;
                if (tru < best_tru) {
                    best_tru = tru;
                    last = t;
                    stall = 0;
                    memcpy(blay, lay, sizeof(int) * (size_t)K);
                    memcpy(bS, S, sizeof(int) * (size_t)K);
                } else {
                    stall++;
                }
            } else {
                S[l * k + i] = old;
                set_dart(nbr, lay, S, k, l, i);
                stall++;
            }
        }

        /* Breakout: raise the weight of every vertex still short of full reach,
           then recompute the weighted cost of the current state. */
        if (stall >= BREAK_STALL && tru != 0) {
            for (int v = 0; v < N; v++)
                if (rc[v] != full) W[v]++;
            long dp = dupcount(lay, S, d, k);
            wc = wcost(rc, W, k, N) + PENALTY * dp;
            stall = 0;
        }
    }

    int ok = (tru == 0);
    if (ok) store_best(nbr, d, k);
    memcpy(out_lay, blay, sizeof(int) * (size_t)K);
    memcpy(out_S, bS, sizeof(int) * (size_t)K);
    *out_cost = best_tru;

    for (int l = 0; l < d; l++) free(nbr[l]);
    free(nbr);
    free(lay);
    free(S);
    free(blay);
    free(bS);
    free(rc);
    free(rn);
    free(tmp);
    free(W);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    g_best_n = atol(argv[5]);
    g_t0 = clock();

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long trials[KMAX + 1], wins[KMAX + 1];
    for (int kk = 0; kk <= KMAX; kk++) {
        trials[kk] = 0;
        wins[kk] = 0;
    }

    int cap = d * KMAX;
    int *blay = malloc(sizeof(int) * (size_t)cap);
    int *bS = malloc(sizeof(int) * (size_t)cap);
    int *tlay = malloc(sizeof(int) * (size_t)cap);
    int *tS = malloc(sizeof(int) * (size_t)cap);

    while (elapsed() < g_budget) {
        int k;
        if (rndf() < 0.2) {
            k = 1 + (int)rnd(KMAX);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KMAX; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndf();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long base = g_best_n / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + (long)rnd((uint64_t)span);
        if (target < 2) target = 2;

        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (2L * k * GG <= g_best_n) continue;

        trials[k]++;
        long bc = 0;
        if (run_trial(d, D, k, 4000, 1200, NULL, NULL, 0, blay, bS, &bc)) {
            wins[k]++;
            continue;
        }

        /* Elite refinement on the same group: restart from the best state. */
        int K = d * k;
        for (int rr = 0; rr < ELITE_ROUNDS && bc <= ELITE_THR && elapsed() < g_budget; rr++) {
            long bc2 = 0;
            int pert = 1 + (int)rnd(3);
            if (run_trial(d, D, k, ELITE_ITERS, ELITE_PATIENCE, blay, bS, pert, tlay, tS, &bc2)) {
                wins[k]++;
                break;
            }
            if (bc2 <= bc) {
                bc = bc2;
                memcpy(blay, tlay, sizeof(int) * (size_t)K);
                memcpy(bS, tS, sizeof(int) * (size_t)K);
            }
        }
    }

    free(blay);
    free(bS);
    free(tlay);
    free(tS);

    if (g_best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_best_n, g_best_m);
    for (long c = 0; c < g_best_m; c++) {
        printf("%d %d\n", g_edges[2 * c], g_edges[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as the start graph.
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
# Driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, budget, min_n, timeout):
    """Run the C engine; returns (n, edges), or (0, []) if it found nothing better than min_n."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n], timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C engine with breakout-weighted annealing, a bandit over
    # base size, group sampling, and elite refinement from near-miss states.
    c_budget = deadline - time.monotonic()
    if c_budget > 0.5 and d >= 3 and D >= 3:
        remaining = time_limit - (time.monotonic() - start)
        timeout = max(1.0, min(c_budget + 4.0, remaining - 2.0))
        try:
            n, e = _c_search(d, D, int(seed) & 0x7FFFFFFF, c_budget, best_n, timeout)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
