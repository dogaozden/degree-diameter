"""Bi-Cayley lift search with a native C annealer (new in this version).

The parent searched in Python with numpy. This version moves the whole
search loop into C, so it makes roughly 50-100x more moves in the same
time. The C engine:
  * samples groups Z_m x| Z_k2 (including non-trivial actions r with
    r^k2 = 1 mod m) directly, with no Python-side group tables;
  * computes group products by formula, so memory is O(d*N) rather than O(G^2);
  * targets moves at defective vertices (vertices not within distance D of
    every block representative);
  * runs a bandit over base sizes k and restarts annealing on stagnation.

Python keeps the exact constructions (projective plane, generalized
quadrangle) and validates the C output with lib.is_valid.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent).
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
# C engine: annealing over bi-Cayley lifts of Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s:
#   A_{i,g} ~ B_{j, g*s},  B_{j,h} ~ A_{i, h*s^-1}.
# Every layer is a permutation, so every vertex has degree d and the
# base multigraph is d-regular (every d-regular bipartite base is a union
# of d perfect matchings, so this loses no generality).
#
# Left multiplication is an automorphism, so checking distances from the
# k-block representatives (identity of each block) decides the diameter.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 5
#define KUSE 4
#define PEN 1000L

typedef uint16_t mask_t;

static uint64_t rs_state = 88172645463325252ULL;

static uint64_t rnd64(void) {
    uint64_t x = rs_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rs_state = x;
    return x;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0;
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int dd;       /* degree d */
static int DIAM;     /* diameter D */
static int KB;       /* number of A blocks (= number of B blocks) */
static int M_, K2_, G_;
static long long pw_[64];
static int NN;       /* current number of vertices 2*KB*G_ */
static int cap_N = 0;
static int *nbr = NULL;
static mask_t *ra = NULL, *rb = NULL;
static int pc_[1024];
static int layers[MAXD][MAXK];
static int svol[MAXD][MAXK];

static int *best_e = NULL;
static long best_m = 0;
static long best_n = 0;

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

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static const int K2OPT[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Group Z_M x| Z_K2, element a*K2 + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x - a * K2_;
    int c = y / K2_, e = y - c * K2_;
    int aa = (int)(((long long)a + pw_[b] * (long long)c) % M_);
    int bb = b + e;
    if (bb >= K2_) bb -= K2_;
    return aa * K2_ + bb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2_, b = x - a * K2_;
    int nb = (K2_ - b) % K2_;
    long long t = ((long long)M_ - a) % M_;
    int aa = (int)(t * pw_[nb] % M_);
    return aa * K2_ + nb;
}

/* Sample a group of order >= target: returns its order G_. */
static int setup_group(long target) {
    int k2 = K2OPT[rndint(20)];
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    if (rndint(4) == 0) m += rndint(3);
    int M = (int)m;
    int r = 1;
    if (k2 > 1 && rndint(10) < 7) {
        int cnt = 0;
        for (int c = 2; c < M; c++)
            if (gcd_i(c, M) == 1 && powmod_ll(c, k2, M) == 1 % M) cnt++;
        if (cnt > 0) {
            int pick = rndint(cnt);
            for (int c = 2; c < M; c++) {
                if (gcd_i(c, M) == 1 && powmod_ll(c, k2, M) == 1 % M) {
                    if (pick == 0) {
                        r = c;
                        break;
                    }
                    pick--;
                }
            }
        }
    }
    M_ = M;
    K2_ = k2;
    G_ = M * k2;
    pw_[0] = 1 % M;
    for (int t = 1; t < k2; t++) pw_[t] = pw_[t - 1] * r % M;
    return G_;
}

static void ensure_cap(int N) {
    if (N <= cap_N) return;
    free(nbr);
    free(ra);
    free(rb);
    nbr = malloc(sizeof(int) * (size_t)dd * (size_t)N);
    ra = malloc(sizeof(mask_t) * (size_t)N);
    rb = malloc(sizeof(mask_t) * (size_t)N);
    cap_N = (nbr && ra && rb) ? N : 0;
}

/* Write layer l: A_i to B_j with voltage s, and the matching B-side entries. */
static void set_dart(int l, int i, int j, int s) {
    const int G = G_, K = KB;
    int *row = nbr + (size_t)l * (size_t)NN;
    int sinv = ginv(s);
    int ba = i * G, bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        row[ba + g] = bb + gmul(g, s);
        row[bb + g] = ba + gmul(g, sinv);
    }
}

/* Sum over vertices of the number of block representatives NOT within distance DIAM. */
static long total_cost(void) {
    const int K = KB, G = G_, N = NN, D = DIAM, dg = dd;
    mask_t *cur = ra, *nxt = rb;
    memset(cur, 0, sizeof(mask_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * G] = (mask_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            mask_t x = cur[v];
            for (int l = 0; l < dg; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        mask_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    ra = cur;
    rb = nxt;
    long cost = 0;
    const int full = 2 * K;
    for (int v = 0; v < N; v++) cost += full - pc_[cur[v]];
    return cost;
}

/* Number of duplicate darts (same A block, same B block, same voltage). */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int l = 0; l < dd; l++)
            for (int l2 = l + 1; l2 < dd; l2++)
                if (layers[l][i] == layers[l2][i] && svol[l][i] == svol[l2][i]) c++;
    return c;
}

static void random_init(void) {
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < KB; i++) layers[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = tmp;
        }
        for (int i = 0; i < KB; i++) {
            svol[l][i] = rndint(G_);
            set_dart(l, i, layers[l][i], svol[l][i]);
        }
    }
}

/* Simulated annealing from a random start. Returns 1 when a valid lift is found. */
static int run_search(long iters, long patience, double until) {
    const int full = (1 << (2 * KB)) - 1;
    random_init();
    long cost = total_cost() + PEN * dupcount();
    double c0 = (double)(cost > 1 ? cost : 1);
    long bestc = cost, last = 0;
    for (long t = 0; t < iters && cost != 0; t++) {
        if ((t & 127) == 0 && elapsed() > until) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (KB >= 2 && rndu() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndint(dd);
            int i1 = rndint(KB);
            int i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            set_dart(l, i1, layers[l][i1], svol[l][i1]);
            set_dart(l, i2, layers[l][i2], svol[l][i2]);
            c2 = total_cost() + PEN * dupcount();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1, layers[l][i1], svol[l][i1]);
                set_dart(l, i2, layers[l][i2], svol[l][i2]);
            }
        } else {
            /* Voltage move, aimed at a defective vertex with probability 0.4. */
            int l = -1, i = -1;
            if (rndu() < 0.4) {
                for (int tries = 0; tries < 40; tries++) {
                    int u = rndint(NN);
                    if (ra[u] != full) {
                        int blk = u / G_;
                        l = rndint(dd);
                        if (blk < KB) {
                            i = blk;
                        } else {
                            int j = blk - KB;
                            for (int ii = 0; ii < KB; ii++)
                                if (layers[l][ii] == j) {
                                    i = ii;
                                    break;
                                }
                        }
                        break;
                    }
                }
            }
            if (i < 0) {
                l = rndint(dd);
                i = rndint(KB);
            }
            int old = svol[l][i];
            int nw = rndint(G_);
            if (nw == old) continue;
            svol[l][i] = nw;
            set_dart(l, i, layers[l][i], nw);
            c2 = total_cost() + PEN * dupcount();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                svol[l][i] = old;
                set_dart(l, i, layers[l][i], old);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
    }
    return cost == 0;
}

/* Keep the current valid lift as the best so far (edges from the A side). */
static void store_result(void) {
    long K = KB, G = G_;
    long m = (long)dd * K * G;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    long idx = 0;
    for (long u = 0; u < K * G; u++)
        for (int l = 0; l < dd; l++) {
            e[2 * idx] = (int)u;
            e[2 * idx + 1] = nbr[(size_t)l * NN + u];
            idx++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = NN;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long lb = (argc > 5) ? atol(argv[5]) : 0;
    if (dd < 1 || dd > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs_state = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_state == 0) rs_state = 1;
    for (int i = 0; i < 20; i++) rnd64();
    pc_[0] = 0;
    for (int v = 1; v < 1024; v++) pc_[v] = pc_[v >> 1] + (v & 1);
    t0 = clock();

    best_n = lb;
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) {
        trials[k] = 0;
        wins[k] = 0;
    }
    const long iters = 6000, patience = 1500;

    while (elapsed() < budget) {
        int k;
        if (rndu() < 0.2) {
            k = 1 + rndint(KUSE);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KUSE; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndu();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long base = best_n / (2L * k);
        long span = base / 8 + 1;
        long target = base + 1 + (long)rndint((int)span);
        if (target < 2) target = 2;
        int G = setup_group(target);
        if (2L * k * G <= best_n) continue;
        KB = k;
        NN = 2 * KB * G_;
        ensure_cap(NN);
        if (!nbr || !ra || !rb) break;
        trials[k]++;
        int ok = run_search(iters, patience, budget);
        if (ok) {
            wins[k]++;
            if (NN > best_n) store_result();
        }
    }

    if (best_e) {
        printf("%ld %ld\n", best_n, best_m);
        for (long i = 0; i < best_m; i++) printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions: return immediately for the calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() - t_start < budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # D = 2 is settled by K_{d,d}, which is optimal for bipartite diameter 2.
    if D == 2 or d < 2 or d > 64:
        return best

    # Native C search for a larger lift; it only returns graphs above best[0].
    c_budget = budget - (time.monotonic() - t_start) - 2.0  # room for compile and parsing
    if c_budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, int(seed), f"{c_budget:.2f}", best[0]],
                         stdin_graph=None, timeout=c_budget + 10.0)
        n, edges = lib.parse_graph_text(text)
        consider(n, edges)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
