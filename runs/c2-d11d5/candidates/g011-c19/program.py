"""Bi-Cayley voltage-lift search in C (bold change: the whole lift search moved into C).

Each candidate is a k-block bi-Cayley graph over the semidirect product Z_m x|_r Z_k2 with
d random permutation layers and voltages. The C engine runs simulated annealing on voltages
and layer permutations, using bitmask distance propagation over the 2k block representatives
(valid because the group acts regularly on every block). Order goals ratchet above the best
graph found. Every returned graph is re-checked with lib.is_valid, and K_{d,d} (or a known
construction) is the fallback.
"""
import itertools
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

#define MAXN 20000
#define MAXK 6
#define MAXL 16
#define PEN 1000

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double tdead;

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

static long gcd_l(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Current group: Z_M x|_r Z_K2 with G = M*K2, elements coded a*K2+b. */
static int K, G, M, K2, N;
static long long pw[64];
static int perm[MAXL][MAXK];
static int volt[MAXL][MAXK];
static int nbr[MAXL][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN], accreach[MAXN];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (a + pw[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = (-(pw[nb] * a)) % M;
    if (t < 0) t += M;
    return (int)(t * K2 + nb);
}

static void setup_group(int k, int m, int k2, int r) {
    K = k;
    M = m;
    K2 = k2;
    G = m * k2;
    N = 2 * k * G;
    pw[0] = 1 % M;
    for (int t = 1; t < K2; t++) pw[t] = (pw[t - 1] * r) % M;
}

/* Vertices: A block i -> i*G + g, B block j -> (K+j)*G + h.
 * Layer l sends A_{i,g} to B_{perm[l][i], g*s} with s = volt[l][i]. */
static void set_block(int l, int i) {
    int j = perm[l][i], s = volt[l][i];
    int si = ginv(s);
    int A0 = i * G, B0 = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][A0 + g] = B0 + gmul(g, s);
        nbr[l][B0 + g] = A0 + gmul(g, si);
    }
}

static void build_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_block(l, i);
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(G);
    }
    build_all();
}

/* Propagate representative-block bitmasks for D rounds. Returns number of unreached
 * (vertex, block) pairs. Since the group acts regularly on blocks, this is exact. */
static long eval_unr(uint64_t **out) {
    uint64_t *X = bufA, *Y = bufB;
    for (int v = 0; v < N; v++) X[v] = 0;
    for (int b = 0; b < 2 * K; b++) X[(long)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = X[v];
            for (int l = 0; l < d; l++) x |= X[nbr[l][v]];
            Y[v] = x;
            changed |= (x != X[v]);
        }
        uint64_t *t = X;
        X = Y;
        Y = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - __builtin_popcountll(X[v]);
    *out = X;
    return unr;
}

/* Duplicate (i, j, s) triples create repeated edges; they are penalised. */
static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

static long total_cost(uint64_t **res) {
    long unr = eval_unr(res);
    return unr + (long)PEN * dup_count();
}

/* Pick (layer, A-block) to modify, biased toward a currently unreached block. */
static void choose_block(uint64_t full, int *pl, int *pi) {
    int l = rndint(d), i = rndint(K);
    if (rnd01() < 0.5) {
        for (int tries = 0; tries < 40; tries++) {
            int v = rndint(N);
            if (accreach[v] == full) continue;
            int blk = v / G;
            if (blk < K) {
                i = blk;
            } else {
                int j = blk - K;
                for (int ii = 0; ii < K; ii++)
                    if (perm[l][ii] == j) {
                        i = ii;
                        break;
                    }
            }
            break;
        }
    }
    *pl = l;
    *pi = i;
}

static long anneal(long iters, long patience, int *found) {
    random_state();
    uint64_t *X = NULL;
    uint64_t full = (1ULL << (2 * K)) - 1;
    long cost = total_cost(&X);
    memcpy(accreach, X, sizeof(uint64_t) * (size_t)N);
    long best = cost, last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > tdead) break;
        double temp = 0.3 + 1.5 * (1.0 - (double)t / (double)iters);

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            set_block(l, i1);
            set_block(l, i2);
            long nc = total_cost(&X);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
                memcpy(accreach, X, sizeof(uint64_t) * (size_t)N);
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
                set_block(l, i1);
                set_block(l, i2);
            }
            continue;
        }

        int l, i;
        choose_block(full, &l, &i);
        int old = volt[l][i];
        int nv = rndint(G);
        if (nv == old) continue;
        volt[l][i] = nv;
        set_block(l, i);
        long nc = total_cost(&X);
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
            cost = nc;
            memcpy(accreach, X, sizeof(uint64_t) * (size_t)N);
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            volt[l][i] = old;
            set_block(l, i);
        }
    }
    *found = (cost == 0);
    return cost;
}

static int try_group(long goal, double mb, int *pk, int *pm, int *pk2, int *pr) {
    static const int K2S[12] = {1, 1, 2, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    int kk = 1 + rndint(MAXK);
    int q = K2S[rndint(12)];
    long Gmin = (goal + 2L * kk - 1) / (2L * kk);
    long mm = (Gmin + q - 1) / q + rndint(3);
    if (mm < 2) mm = 2;
    long GG = mm * q;
    long NN = 2L * kk * GG;
    if (NN > MAXN || (double)NN > mb || NN < goal) return 0;
    int rr = 1;
    if (q == 2 && mm >= 3 && rnd01() < 0.5) {
        rr = (int)(mm - 1);
    } else if (q >= 2 && mm >= 3) {
        for (int tries = 0; tries < 200; tries++) {
            long c = 2 + rndint((int)(mm - 2));
            if (gcd_l(c, mm) == 1 && powmod(c, q, mm) == 1 % mm) {
                rr = (int)c;
                break;
            }
        }
    }
    *pk = kk;
    *pm = (int)mm;
    *pk2 = q;
    *pr = rr;
    return 1;
}

static double moore_bound(void) {
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
    }
    return 2 * s;
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double t0 = now();
    tdead = t0 + limit;
    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double mb = moore_bound();
    long best_N = 0;
    int bK = 0, bM = 0, bK2 = 0, bR = 1;
    static int bperm[MAXL][MAXK], bvolt[MAXL][MAXK];

    while (now() < tdead) {
        long base = best_N > 0 ? best_N : 2L * d;
        long goal;
        if (best_N == 0) goal = 2L * d;
        else if (rnd01() < 0.7) goal = base + 1 + (long)(base * (0.005 + 0.025 * rnd01()));
        else goal = base + 1 + (long)(base * (0.03 + 0.08 * rnd01()));
        int k, m, k2, r;
        if (!try_group(goal, mb, &k, &m, &k2, &r)) continue;
        setup_group(k, m, k2, r);
        int found = 0;
        anneal(12000, 3000, &found);
        if (found && (long)N > best_N) {
            best_N = N;
            bK = K;
            bM = M;
            bK2 = K2;
            bR = r;
            memcpy(bperm, perm, sizeof perm);
            memcpy(bvolt, volt, sizeof volt);
        }
    }

    if (best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bK, bM, bK2, bR);
    memcpy(perm, bperm, sizeof perm);
    memcpy(volt, bvolt, sizeof volt);
    build_all();
    long m_edges = (long)K * G * d;
    printf("%d %ld\n", N, m_edges);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++) printf("%d %d\n", u, nbr[l][u]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (used for calibration and as extra candidates).
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions. The calibration case (d=3, D=3) returns here.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: the C engine runs the bi-Cayley lift annealing for the rest of the budget.
    if D >= 3 and d >= 2:
        limit = t0 + total - time.monotonic() - 0.5
        if limit > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(limit, 2)],
                                 timeout=limit + 15)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
