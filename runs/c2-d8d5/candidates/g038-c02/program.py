import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts with semidirect-product
# voltage groups Z_m x| Z_k2. The base graph has k vertices per side, so the
# lift has 2*k*G vertices (G = m*k2). Every layer is a perfect matching between
# the two sides, and the voltages are chosen by annealing. The cost is the
# number of (vertex, base vertex) pairs at distance > D, plus a penalty for
# repeated darts. A zero cost gives a valid graph. Candidate groups come from
# stdin-free argv, and each candidate runs in its own time slice.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define G_MAX 2600
#define K_MAX 4
#define C_MAX 512
#define PEN 20LL

static int d_, D_, k_, G_, NV;
static int *MUL = NULL;
static int *layers = NULL, *S = NULL, *nb = NULL, *bad_list = NULL;
static u64 *reachA = NULL, *reachB = NULL;
static int nbad = 0;
static int bestN = 0, bestM = 0, found = 0;
static int *bestE = NULL;

static void free_state(void) {
    free(layers); layers = NULL;
    free(S); S = NULL;
    free(nb); nb = NULL;
    free(bad_list); bad_list = NULL;
    free(reachA); reachA = NULL;
    free(reachB); reachB = NULL;
}

static int alloc_state(void) {
    free_state();
    layers = malloc(sizeof(int) * (size_t)(d_ * k_));
    S = malloc(sizeof(int) * (size_t)(d_ * k_));
    nb = malloc(sizeof(int) * (size_t)d_ * (size_t)NV);
    bad_list = malloc(sizeof(int) * (size_t)NV);
    reachA = malloc(sizeof(u64) * (size_t)NV);
    reachB = malloc(sizeof(u64) * (size_t)NV);
    return layers && S && nb && bad_list && reachA && reachB;
}

/* Semidirect product Z_m x| Z_k2 with (a,b)(c,d) = (a + r^b c, b + d), coded a*k2+b. */
static int setup_group(int k, int m, int k2, int r) {
    long long G = (long long)m * k2;
    if (k < 1 || k > K_MAX || m < 1 || k2 < 1 || G > G_MAX || r < 0) return 0;
    if (m > 1) {
        long long p = 1;
        for (int t = 0; t < k2; t++) p = p * r % m;
        if (p != 1) return 0;
    }
    int *pw = malloc(sizeof(int) * (size_t)k2);
    if (!pw) return 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    G_ = (int)G;
    k_ = k;
    NV = 2 * k * G_;
    free(MUL);
    MUL = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    if (!MUL) { free(pw); return 0; }
    for (int x = 0; x < G_; x++) {
        int a1 = x / k2, b1 = x % k2;
        for (int y = 0; y < G_; y++) {
            int a2 = y / k2, b2 = y % k2;
            int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % m);
            int b = (b1 + b2) % k2;
            MUL[(size_t)x * G_ + y] = a * k2 + b;
        }
    }
    free(pw);
    return 1;
}

static void random_state(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) layers[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = layers[l * k_ + i];
            layers[l * k_ + i] = layers[l * k_ + j];
            layers[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) S[l * k_ + i] = rint_(G_);
    }
}

/* Dart (l, i) joins A_i x to B_{layers[l][i]} x*S[l][i]. */
static void build_nb(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) {
            int j = layers[l * k_ + i], s = S[l * k_ + i];
            for (int x = 0; x < G_; x++) {
                int a = i * G_ + x;
                int y = (k_ + j) * G_ + MUL[(size_t)x * G_ + s];
                nb[(size_t)l * NV + a] = y;
                nb[(size_t)l * NV + y] = a;
            }
        }
    }
}

static int dupcount(void) {
    int c = 0, n = d_ * k_;
    for (int p = 0; p < n; p++)
        for (int q = p + 1; q < n; q++)
            if (p % k_ == q % k_ && layers[p] == layers[q] && S[p] == S[q]) c++;
    return c;
}

static long long evalcost(void) {
    build_nb();
    int full_bits = 2 * k_;
    u64 full = (1ULL << full_bits) - 1;
    u64 *cur = reachA, *nxt = reachB;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < full_bits; b++) cur[(size_t)b * G_] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            u64 r = cur[v];
            for (int l = 0; l < d_; l++) r |= cur[nb[(size_t)l * NV + v]];
            nxt[v] = r;
            if (r != cur[v]) changed = 1;
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long long unr = 0;
    nbad = 0;
    for (int v = 0; v < NV; v++) {
        int pc = __builtin_popcountll(cur[v] & full);
        unr += full_bits - pc;
        if (pc != full_bits) bad_list[nbad++] = v;
    }
    return unr + PEN * (long long)dupcount();
}

static void save_current(void) {
    build_nb();
    int m = 0;
    for (int v = 0; v < NV; v++)
        for (int l = 0; l < d_; l++)
            if (nb[(size_t)l * NV + v] > v) m++;
    int *E = malloc(sizeof(int) * 2 * (size_t)m + 2);
    if (!E) return;
    int p = 0;
    for (int v = 0; v < NV; v++)
        for (int l = 0; l < d_; l++) {
            int u = nb[(size_t)l * NV + v];
            if (u > v) { E[p++] = v; E[p++] = u; }
        }
    free(bestE);
    bestE = E;
    bestM = m;
    bestN = NV;
    found = 1;
}

static void run_candidate(double slice_ticks) {
    random_state();
    long long cost = evalcost();
    double T0 = (double)(cost > 50 ? cost : 50) * 0.02;
    if (T0 < 2.0) T0 = 2.0;
    const double T1 = 0.2;
    double start = (double)clock();
    while (cost > 0) {
        double el = (double)clock() - start;
        if (el >= slice_ticks) break;
        double frac = el / slice_ticks;
        double T = T0 * pow(T1 / T0, frac);
        double x = rdbl();
        if (k_ >= 2 && x < 0.15) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *P = layers + l * k_;
            int t = P[i1]; P[i1] = P[i2]; P[i2] = t;
            long long c2 = evalcost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = P[i1]; P[i1] = P[i2]; P[i2] = t;
            }
        } else {
            int l, i;
            if (nbad > 0 && rdbl() < 0.5) {
                int v = bad_list[rint_(nbad)];
                int blk = v / G_;
                l = rint_(d_);
                if (blk < k_) {
                    i = blk;
                } else {
                    int j = blk - k_;
                    i = 0;
                    for (int ii = 0; ii < k_; ii++)
                        if (layers[l * k_ + ii] == j) { i = ii; break; }
                }
            } else {
                l = rint_(d_);
                i = rint_(k_);
            }
            int idx = l * k_ + i;
            int old = S[idx];
            int ns = rint_(G_);
            if (ns == old) continue;
            S[idx] = ns;
            long long c2 = evalcost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[idx] = old;
            }
        }
    }
    if (cost == 0 && NV > bestN) save_current();
}

static int parse_cands(const char *s, int *ck, int *cm, int *ck2, int *cr, int maxc) {
    int n = 0;
    const char *p = s;
    while (*p && n < maxc) {
        int k, m, k2, r, used = 0;
        if (sscanf(p, "%d,%d,%d,%d%n", &k, &m, &k2, &r, &used) != 4 || used <= 0) break;
        ck[n] = k; cm[n] = m; ck2[n] = k2; cr[n] = r;
        n++;
        p += used;
        if (*p == ';') p++;
        else break;
    }
    return n;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    bestN = atoi(argv[5]);

    int ck[C_MAX], cm[C_MAX], ck2[C_MAX], cr[C_MAX];
    int nc = 0;
    if (argc > 6) nc = parse_cands(argv[6], ck, cm, ck2, cr, C_MAX);
    if (d_ < 1 || D_ < 1 || nc == 0) { printf("0 0\n"); return 0; }

    double start = (double)clock();
    double total = limit * CLOCKS_PER_SEC;
    for (int c = 0; c < nc; c++) {
        double left = total - ((double)clock() - start);
        if (left <= 0) break;
        int k = ck[c], m = cm[c], k2 = ck2[c], r = cr[c];
        if (k < 1 || k > K_MAX || m < 1 || k2 < 1) continue;
        long long G = (long long)m * k2;
        if (G > G_MAX) continue;
        if (2LL * k * G <= bestN) continue;
        if (!setup_group(k, m, k2, r)) continue;
        if (!alloc_state()) { free_state(); continue; }
        double slice = left / (double)(nc - c);
        run_candidate(slice);
        free_state();
    }
    free(MUL);
    MUL = NULL;

    if (!found) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    }
    free(bestE);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_G_MAX = 2600
_K2_CHOICES = (1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21,
               24, 28, 30, 32, 36, 40)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G_target, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order at least G_target (and at most _G_MAX), or None."""
    for _ in range(40):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-G_target // k2))
        if m * k2 > _G_MAX:
            continue
        if k2 == 1:
            return m, 1, 1
        opts = [c for c in range(1, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if opts:
            return m, k2, rng.choice(opts)
    return None


def _gen_candidates(best_n, rng, count):
    """Candidate lifts (k, m, k2, r) with 2*k*G just above best_n, sorted by order ascending."""
    chosen = {}
    for _ in range(count * 40):
        if len(chosen) >= count:
            break
        k = rng.choice((1, 1, 2, 2, 3, 4))
        g = math.exp(rng.uniform(math.log(0.004), math.log(0.45)))
        lo = best_n // (2 * k) + 1
        hi = max(lo, int(best_n * (1.0 + g) / (2 * k)) + 1)
        G_target = rng.randint(lo, hi)
        s = _sample_group(G_target, rng)
        if s is None:
            continue
        m, k2, r = s
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        chosen[(k, m, k2, r)] = 2 * k * G
    return [key for key, _ in sorted(chosen.items(), key=lambda kv: kv[1])]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Rounds of C lift search. Each round uses candidates just above the
    # current best order, and the C side climbs within a round as it succeeds.
    end = t0 + time_limit - 7.0
    while True:
        left = end - time.monotonic()
        if left < 3.0:
            break
        budget = min(left, max(5.0, 0.25 * time_limit))
        cands = _gen_candidates(best[0], rng, 10)
        if not cands:
            break
        arg = ";".join(f"{k},{m},{k2},{r}" for k, m, k2, r in cands)
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", best[0], arg],
                            timeout=budget + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            break  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
