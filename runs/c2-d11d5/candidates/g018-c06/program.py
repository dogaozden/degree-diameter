"""Combined program: exact projective/generalized-polygon constructions for D = 3, 4, then a C
bi-Cayley lift annealer over semidirect products Z_m x| Z_k2 (with a block-representative
bitmask distance test) that searches for the largest valid lift it can find.

Every returned graph is checked with lib.is_valid, and K_{d,d} (or a cycle for d = 2) is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 *
 * Usage:  prog d D seed time_limit
 * stdin is ignored. stdout: "n m" and the edges of the best valid graph found, or "0 0".
 *
 * Model: K blocks A_0..A_{K-1} and K blocks B_0..B_{K-1}, each block a copy of a finite
 * group H = Z_M x| Z_K2 (element (a,b) coded as a*K2+b, product (a,b)(c,e) = (a + r^b c, b+e)).
 * Layer l pairs A_i with B_{lay[l][i]} through voltage vol[l][i]: A_{i,g} ~ B_{j, g*s}.
 * Every layer is a perfect matching of blocks, so every vertex has degree exactly d.
 *
 * Key fact used here: left multiplication by H is an automorphism that fixes every block.
 * So the lift has diameter <= D iff each of the 2K block representatives (vertex b*G) reaches
 * every vertex within D steps. This is tracked with one bitmask per vertex over the 2K
 * representatives, which costs D*N*d operations per evaluation.
 *
 * Cost = (number of unreached (representative, vertex) pairs) + PEN * (duplicate darts).
 * Cost 0 means a valid graph. Moves: change one voltage (biased toward unreached vertices)
 * or swap the targets of two blocks inside one layer.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define KMAX 8
#define K2MAX 64
#define PEN 1000L

static int d, D;
static long MAXNV;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

/* Current lift state. */
static int K, G, NV;
static long GM, GR;
static int GK2;
static long pw[K2MAX];
static int *lay, *vol, *nbr, *bestNbr;
static uint32_t *RA, *RB;
static int best_K, best_G, best_n;
static int wins[KMAX + 1], trials[KMAX + 1];

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

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Group product in Z_GM x| Z_GK2. */
static int gmul(int x, int y) {
    int a = x / GK2, b = x - a * GK2;
    int c = y / GK2, e = y - c * GK2;
    long t = (a + pw[b] * (long)c) % GM;
    int nb = b + e;
    if (nb >= GK2) nb -= GK2;
    return (int)(t * GK2 + nb);
}

/* Group inverse: (a,b)^-1 = (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / GK2, b = x - a * GK2;
    int nb = (GK2 - b) % GK2;
    long na = (GM - (pw[nb] * (long)a) % GM) % GM;
    return (int)(na * GK2 + nb);
}

/* Rewrite layer l's neighbours for A-block i and its target B-block. */
static void build_dart(int l, int i) {
    int j = lay[l * K + i], s = vol[l * K + i];
    int si = ginv(s);
    int A = i * G, B = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[(size_t)(A + g) * d + l] = B + gmul(g, s);
        nbr[(size_t)(B + g) * d + l] = A + gmul(g, si);
    }
}

/* Penalised cost: unreached (representative, vertex) pairs plus duplicate darts. */
static long eval_cost(void) {
    int NB = 2 * K;
    uint32_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)NV);
    for (int b = 0; b < NB; b++) cur[(size_t)b * G] |= 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint32_t x = cur[v];
            const int *q = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[q[l]];
            nxt[v] = x;
            changed |= ((x ^ cur[v]) != 0);
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    if (cur != RA) memcpy(RA, cur, sizeof(uint32_t) * (size_t)NV);
    uint32_t full = (NB >= 32) ? 0xffffffffu : ((1u << NB) - 1u);
    long bad = 0;
    for (int v = 0; v < NV; v++) bad += NB - __builtin_popcount(RA[v] & full);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 1; l1 < d; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i])
                    dup++;
    return bad + PEN * dup;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l * K + i];
            lay[l * K + i] = lay[l * K + j];
            lay[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) vol[l * K + i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) build_dart(l, i);
}

/* Choose a dart (layer, A-block), biased toward a random unreached vertex. */
static void pick_dart(int *pl, int *pi) {
    int l = rndint(d), i = -1, v = -1;
    uint32_t full = (2 * K >= 32) ? 0xffffffffu : ((1u << (2 * K)) - 1u);
    if (rnd01() < 0.5) {
        for (int t = 0; t < 40; t++) {
            int c = rndint(NV);
            if (RA[c] != full) {
                v = c;
                break;
            }
        }
    }
    if (v >= 0) {
        if (v < K * G) {
            i = v / G;
        } else {
            int j = v / G - K;
            for (int t = 0; t < K; t++)
                if (lay[l * K + t] == j) {
                    i = t;
                    break;
                }
        }
    }
    if (i < 0) i = rndint(K);
    *pl = l;
    *pi = i;
}

/* Simulated annealing on the current group. Returns the final cost (0 means valid). */
static long anneal(long iters, double deadline, long patience) {
    long cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last = 0;
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        if (it - last > patience) break;
        double frac = (double)it / (double)iters;
        double temp = 0.01 * c0 * (1.0 - frac);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int *a = &lay[l * K + i1], *b = &lay[l * K + i2];
            int t = *a;
            *a = *b;
            *b = t;
            build_dart(l, i1);
            build_dart(l, i2);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
                if (nc == 0) last = it;
            } else {
                t = *a;
                *a = *b;
                *b = t;
                build_dart(l, i1);
                build_dart(l, i2);
            }
            continue;
        }

        int l, i;
        pick_dart(&l, &i);
        int old = vol[l * K + i];
        int nw = rndint(G);
        if (nw == old) continue;
        vol[l * K + i] = nw;
        build_dart(l, i);
        long nc = eval_cost();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
            cost = nc;
            if (nc == 0) last = it;
        } else {
            vol[l * K + i] = old;
            build_dart(l, i);
        }
    }
    return cost;
}

/* Sample a semidirect group Z_m x| Z_k2 with order about target. */
static int sample_group(long target, long *m_out, int *k2_out, long *r_out) {
    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 24};
    int nk = (int)(sizeof K2S / sizeof K2S[0]);
    for (int att = 0; att < 200; att++) {
        int k2 = K2S[rndint(nk)];
        long m = target / k2 + rndint(3);
        if (m < 2) m = 2;
        long r = 1 % m;
        if (k2 > 1 && m >= 3 && rnd01() < 0.75) {
            int ok = 0;
            for (int t = 0; t < 400; t++) {
                long c = 2 + rndint((int)(m - 2));
                if (gcdl(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    ok = 1;
                    break;
                }
            }
            if (!ok) continue;
        }
        *m_out = m;
        *k2_out = k2;
        *r_out = r;
        return 1;
    }
    return 0;
}

static void setup_group(int k, long m, int k2, long r) {
    K = k;
    GM = m;
    GK2 = k2;
    GR = r;
    G = (int)(m * k2);
    NV = 2 * K * G;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = pw[b - 1] * r % m;
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

static double moore_d(void) {
    if (D <= 0 || d <= 0) return 1.0;
    if (d == 1) return 2.0;
    if (d == 2) return 2.0 * D;
    double s = 0.0, p = 1.0;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1e9) break;
    }
    return 2.0 * s;
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
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double mb = moore_d();
    MAXNV = (long)(mb < 300000.0 ? mb : 300000.0);
    if (MAXNV < 4) {
        printf("0 0\n");
        return 0;
    }
    lay = malloc(sizeof(int) * (size_t)d * KMAX);
    vol = malloc(sizeof(int) * (size_t)d * KMAX);
    nbr = malloc(sizeof(int) * (size_t)MAXNV * d);
    bestNbr = malloc(sizeof(int) * (size_t)MAXNV * d);
    RA = malloc(sizeof(uint32_t) * (size_t)MAXNV);
    RB = malloc(sizeof(uint32_t) * (size_t)MAXNV);
    if (!lay || !vol || !nbr || !bestNbr || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    best_n = 0;
    double goal = 64.0;
    while (now() < t_end) {
        if (goal > (double)MAXNV) goal = (double)MAXNV;
        int k = pick_k();
        long tg = (long)(goal / (2.0 * k));
        if (tg < 2) tg = 2;
        long m;
        int k2;
        long r;
        if (!sample_group(tg, &m, &k2, &r)) {
            goal *= 0.99;
            continue;
        }
        long Gc = m * k2;
        if (2L * k * Gc > MAXNV) {
            goal *= 0.995;
            continue;
        }
        if (2L * k * Gc <= best_n) {
            goal = best_n * 1.02;
            continue;
        }
        setup_group(k, m, k2, r);
        random_lift();
        trials[k]++;
        long c = anneal(3000, t_end, 800);
        if (c == 0) {
            wins[k]++;
            if (NV > best_n) {
                memcpy(bestNbr, nbr, sizeof(int) * (size_t)NV * d);
                best_n = NV;
                best_K = K;
                best_G = G;
            }
            goal = NV * 1.03;
        } else {
            double low = best_n * 1.01;
            double down = goal * 0.995;
            goal = low > down ? low : down;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    int A = best_K * best_G;
    long me = (long)A * d;
    printf("%d %ld\n", best_n, me);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, bestNbr[(size_t)u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
# ----------------------------------------------------------------------------

def _cycle(n):
    """Cycle C_n (n even): bipartite, 2-regular, diameter n/2."""
    return n, [(i, (i + 1) % n) for i in range(n)]


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
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(2 * D)

    # K_{d,d} has diameter 2 and is the optimum for D = 2; it is also the safe fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    bound = lib.moore_bound(d, D)
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
        return best_n >= bound

    t_start = time.monotonic()

    # Exact or near-exact constructions. If one reaches the Moore bound, nothing can beat it.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None and consider(*pg):
                return best_n, best_e
        except Exception:
            pass
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                if consider(*lib.araujo_lopez_graph(d - 2)):
                    return best_n, best_e
            except Exception:
                pass
        if D == 4:
            try:
                for q in range(min(d - 1, 9), 1, -1):
                    if lib.is_prime_power(q):
                        if consider(*_gq_w(q)):
                            return best_n, best_e
                        break
            except Exception:
                pass

    # Search: the C annealer uses the remaining time, with a margin for validation and parsing.
    elapsed = time.monotonic() - t_start
    total = max(1.0, 0.8 * time_limit - 4.0 - elapsed)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(total, 2)],
                         stdin_graph=None, timeout=total + 20)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
