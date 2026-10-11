import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: voltage lifts over ARBITRARY finite groups given as multiplication
# tables. Python builds the group (abelian products, metacyclic Z_m x| Z_k, and
# affine-diagonal (Z_p x Z_p) x| Z_k, which is not metacyclic) and passes its table
# on stdin. The C engine runs simulated annealing with breakout weights and a small
# iterated-local-search pool on that one group, and stops as soon as it finds a
# zero-cost lift.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so the degree is DEG.
# Left multiplication is an automorphism, so diameter <= D iff BFS of depth D from
# each of the 2K block representatives (the identity of each block) covers all.
# Every output is re-checked with lib.is_valid, and the fallback is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 5000
#define ILS_ITERS 2500
#define POOLMAX 16
#define BRK 150
#define MAXK 16

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, G, T, NN;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp = 0;
static long long wt[2 * MAXK], unc[2 * MAXK];
static long long wsum_w = 0, last_w = 0;
static int *poolJ[POOLMAX], *poolS[POOLMAX];
static long long poolC[POOLMAX];
static int npool = 0;

static inline void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MT[g * G + s];
}

static void alloc_config(void) {
    NN = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)NN * DEG);
    cnt = malloc(sizeof(int) * (size_t)NN);
    stamp = calloc((size_t)NN, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NN);
    nx = malloc(sizeof(int) * (size_t)NN);
    for (int i = 0; i < POOLMAX; i++) {
        poolJ[i] = malloc(sizeof(int) * (size_t)T);
        poolS[i] = malloc(sizeof(int) * (size_t)T);
        poolC[i] = BIGC;
    }
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void reset_weights(void) {
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)NN);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NN);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = NN - count;
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Random kicks: within-layer target swaps and voltage changes (layers stay permutations). */
static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

/* Annealing on the weighted cost with breakout bumps. The caller must have just called
   eval_cost() so that cost and last_w describe the start state. Best state by true cost
   goes to bestJ/bestS. Returns the best true cost. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (poolC[i] > poolC[slot]) slot = i;
        if (poolC[slot] <= cost) return;
    }
    poolC[slot] = cost;
    memcpy(poolJ[slot], J, sizeof(int) * (size_t)T);
    memcpy(poolS[slot], S, sizeof(int) * (size_t)T);
}

static void load_state(const int *J, const int *S) {
    memcpy(dJ, J, sizeof(int) * (size_t)T);
    memcpy(dS, S, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
}

static void emit_graph(void) {
    printf("%d %d\n", NN, T * G);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time K G  (group table on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    G = atoi(argv[6]);
    if (DEG < 1 || DIAM < 1 || K < 1 || K > MAXK || G < 2) {
        printf("0 0\n");
        return 0;
    }
    int ns = 0, ms = 0;
    if (scanf("%d %d", &ns, &ms) != 2 || ms < 0) {
        printf("0 0\n");
        return 0;
    }
    long long need = (long long)G * G;
    if (2LL * ms < need) {
        printf("0 0\n");
        return 0;
    }
    int *buf = malloc(sizeof(int) * (size_t)(2 * ms + 2));
    for (int i = 0; i < 2 * ms; i++) {
        if (scanf("%d", &buf[i]) != 1) {
            printf("0 0\n");
            return 0;
        }
    }
    MT = malloc(sizeof(int) * (size_t)need);
    for (long long i = 0; i < need; i++) {
        MT[i] = buf[i];
        if (MT[i] < 0 || MT[i] >= G) {
            printf("0 0\n");
            return 0;
        }
    }
    for (int x = 0; x < G; x++) {
        if (MT[x] != x || MT[(size_t)x * G] != x) {
            printf("0 0\n");
            return 0;
        }
    }
    alloc_config();
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int found = 0;
    while (!found && elapsed() < DEADLINE) {
        long long bc;
        if (npool > 0 && rnd_unit() < 0.5) {
            int pi = rnd_int(npool);
            load_state(poolJ[pi], poolS[pi]);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            reset_weights();
            long long c0 = eval_cost();
            bc = run_sa(ILS_ITERS, 0.35, c0);
        } else {
            random_init();
            reset_weights();
            long long c0 = eval_cost();
            bc = run_sa(ITERS, 1.0, c0);
        }
        if (bc == 0) {
            load_state(bestJ, bestS);
            found = 1;
        } else {
            pool_add(bc, bestJ, bestS);
        }
    }
    if (found) emit_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Groups as multiplication tables (identity = element 0).
# ----------------------------------------------------------------------------

HINT = {(6, 5): 684}   # record orders used only to choose where to search


def _ab_mul(a, b):
    """Z_a x Z_b, element i*b + j."""
    def mul(x, y):
        i, j = divmod(x, b)
        k, l = divmod(y, b)
        return ((i + k) % a) * b + (j + l) % b
    return mul


def _affine_mul(p, k, r1, r2):
    """(Z_p x Z_p) x| Z_k with diagonal action diag(r1, r2); r1^k = r2^k = 1 mod p.
    Element (v, b) with v = x1*p + x2 coded as v*k + b. Not metacyclic in general."""
    def mul(x, y):
        v, b = divmod(x, k)
        w, c = divmod(y, k)
        x1, x2 = divmod(v, p)
        y1, y2 = divmod(w, p)
        z1 = (x1 + pow(r1, b, p) * y1) % p
        z2 = (x2 + pow(r2, b, p) * y2) % p
        return (z1 * p + z2) * k + (b + c) % k
    return mul


def _group_mul(desc):
    kind = desc[0]
    if kind == "ab":
        a, b = desc[1], desc[2]
        return a * b, _ab_mul(a, b)
    if kind == "meta":
        m, k, r = desc[1], desc[2], desc[3]
        order, mul, _ = lib.semidirect_group(m, k, r)
        return order, mul
    if kind == "aff":
        p, k, r1, r2 = desc[1], desc[2], desc[3], desc[4]
        return p * p * k, _affine_mul(p, k, r1, r2)
    raise ValueError(kind)


def _primes_upto(n):
    out = []
    for p in range(2, math.isqrt(n) + 1):
        if all(p % q for q in range(2, math.isqrt(p) + 1)):
            out.append(p)
    return out


def _descriptors(g, rng):
    """Group descriptors of order g: abelian products, metacyclic, and affine-diagonal."""
    out = []
    for a in range(2, g):
        if g % a == 0 and a <= g // a:
            out.append(("ab", a, g // a))
    for k in range(2, g):
        if g % k == 0 and g // k >= 2:
            m = g // k
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(rs)
            for r in rs[:2]:
                out.append(("meta", m, k, r))
    for p in _primes_upto(g):
        if g % (p * p) == 0 and g // (p * p) >= 2:
            k = g // (p * p)
            roots = [r for r in range(1, p) if pow(r, k, p) == 1]
            for _ in range(3):
                out.append(("aff", p, k, rng.choice(roots), rng.choice(roots)))
    return out


def _jobs(lo, rng):
    """(K, descriptor) jobs whose lift order 2*K*G starts at lo and grows slowly."""
    jobs = []
    for K in (1, 2, 3):
        gb = -(-lo // (2 * K))
        spread = max(2, gb // 25)
        for g in range(gb, gb + spread + 1):
            descs = _descriptors(g, rng)
            rng.shuffle(descs)
            for desc in descs[:4]:
                jobs.append((2 * K * g, rng.random(), K, desc))
    jobs.sort(key=lambda j: (j[0], j[1]))
    return [(K, desc) for _, _, K, desc in jobs]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    deadline = start + 0.85 * time_limit - 1.0
    hint = HINT.get((d, D), 0)
    lo = max(best_n + 1, hint)
    rng = random.Random(1009 * seed + 31 * d + D)

    for idx, (K, desc) in enumerate(_jobs(lo, rng)):
        remaining = deadline - time.monotonic()
        if remaining < 2.5:
            break
        per_call = min(remaining - 0.5, 10.0)
        try:
            order, mul = _group_mul(desc)
            flat = [mul(x, y) for x in range(order) for y in range(order)]
            pairs = [(flat[i], flat[i + 1] if i + 1 < len(flat) else 0)
                     for i in range(0, len(flat), 2)]
            out = lib.run_c(C_SOURCE, [d, D, seed * 97 + idx, f"{per_call:.2f}", K, order],
                            stdin_graph=(order, pairs), timeout=per_call + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
