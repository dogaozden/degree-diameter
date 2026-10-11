import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# Voltage lifts over GENERAL finite groups, given as multiplication tables.
# Python builds a pool of groups: semidirect products Z_m x| Z_k, unitriangular
# groups U3(Z_n) (non-abelian, order n^3), and direct products of those with
# cyclic groups. The C engine receives the tables on stdin and runs simulated
# annealing with breakout weights over voltage assignments for K base vertices
# per side and DEG layers. Each layer is a permutation, so the lift is
# DEG-regular. Left multiplication is an automorphism, so the diameter check
# needs BFS from the 2K block representatives only.
#
# Safe fallbacks: K_{d,d}, PG(2,q) incidence, and W(q) for D >= 4. Every C
# output is re-checked with lib.is_valid before it is returned.
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
#define POOLMAX 32
#define POOLP 0.6
#define BRK 120
#define MAXQ 64
#define MAXK 4
#define MAXDEG 8
#define MAXT (MAXK * MAXDEG)

typedef struct { int N; const int *mul; } Grp;
typedef struct { int g; int K; long long cost; int J[MAXT]; int S[MAXT]; } Cfg;

static Grp grp[MAXQ];
static int NG = 0;
static int DEG, DIAM;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static int cg, GN, K, T, NV;
static const int *MUL;

static int dI[MAXT], dJ[MAXT], dS[MAXT], bestJ[MAXT], bestS[MAXT];
static int *perm, *adj, *cnt, *stamp, *fr, *nx;
static int capG, capV;
static int curstamp = 0;
static long long wt[2 * MAXK], unc[2 * MAXK];
static long long wsum = 0;
static long long last_w = 0;
static Cfg pool[POOLMAX];
static int npool = 0;

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

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * GN;
    for (int g = 0; g < GN; g++) pm[g] = MUL[g * GN + s];
}

static int has_dup(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) return 1;
    return 0;
}

/* Returns the true cost (uncovered ordered pairs from the 2K block representatives).
   Sets unc[] per block and last_w to the breakout-weighted cost. */
static long long eval_cost(void) {
    int N = NV;
    if (has_dup()) {
        for (int r = 0; r < 2 * K; r++) unc[r] = 0;
        last_w = BIGC;
        return BIGC;
    }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * GN, bj = (K + dJ[t]) * GN;
        const int *pm = perm + (size_t)t * GN;
        for (int g = 0; g < GN; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cnt[a] >= DEG || cnt[b] >= DEG) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)capV);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = r * GN;
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
        unc[r] = N - count;
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void setup(int gi, int k) {
    cg = gi;
    GN = grp[gi].N;
    MUL = grp[gi].mul;
    K = k;
    T = DEG * K;
    NV = 2 * K * GN;
    for (int r = 0; r < 2 * K; r++) { wt[r] = 1; unc[r] = 0; }
    wsum = 2 * K;
    for (int t = 0; t < T; t++) dI[t] = t % K;
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
            dS[t] = rnd_int(GN);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
    for (int tries = 0; tries < 300 && has_dup(); tries++) {
        int t = rnd_int(T);
        dS[t] = rnd_int(GN);
        build_perm(t);
    }
}

/* Random kicks: within-layer target swaps and voltage changes (layers stay permutations). */
static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(GN);
            build_perm(t);
        }
    }
}

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
                    if (unc[r] > 0) { wt[r]++; wsum++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2; wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t], news = rnd_int(GN);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2; wcur = w2;
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

static void emit_current(void) {
    int m = T * GN;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < GN; g++) {
            best_e[idx++] = dI[t] * GN + g;
            best_e[idx++] = (K + dJ[t]) * GN + perm[(size_t)t * GN + g];
        }
    }
    best_m = m;
    best_n = NV;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the current best. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (NV > best_n) emit_current();
}

static void pool_add(long long cost) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->g = cg;
    c->K = K;
    c->cost = cost;
    memcpy(c->J, bestJ, sizeof(int) * (size_t)T);
    memcpy(c->S, bestS, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * grp[pool[i].g].N;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

static int pick_fresh(int *og, int *ok) {
    static const int kc[7] = {1, 1, 2, 2, 3, 3, 4};
    int k0 = kc[rnd_int(7)];
    for (int a = 0; a <= MAXK; a++) {
        int k = (a == 0) ? k0 : a;
        int cands[MAXQ], nc = 0;
        for (int gi = 0; gi < NG; gi++)
            if (2LL * k * grp[gi].N > best_n) cands[nc++] = gi;
        if (nc > 0) {
            *og = cands[rnd_int(nc)];
            *ok = k;
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [best_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* stdin: header "Q m", then 2m ints: [N_1, table_1 (N_1^2 ints), N_2, table_2, ...] */
    int Q = 0, mpairs = 0;
    if (scanf("%d %d", &Q, &mpairs) != 2) { Q = 0; mpairs = 0; }
    if (Q < 0) Q = 0;
    if (mpairs < 0) mpairs = 0;
    long long tok = 2LL * mpairs;
    int *S = malloc(sizeof(int) * (size_t)(tok + 2));
    long long got = 0;
    while (got < tok && scanf("%d", &S[got]) == 1) got++;

    long long pos = 0;
    int maxN = 1;
    for (int q = 0; q < Q && NG < MAXQ; q++) {
        if (pos >= got) break;
        long long N = S[pos++];
        if (N < 1 || N > 2000 || pos + N * N > got) break;
        int *mul = S + pos;
        pos += N * N;
        int ok = 1;
        for (long long x = 0; x < N * N && ok; x++)
            if (mul[x] < 0 || mul[x] >= N) ok = 0;
        for (long long x = 0; x < N && ok; x++)
            if (mul[x] != x || mul[x * N] != x) ok = 0;   /* identity must be index 0 */
        if (!ok) continue;
        grp[NG].N = (int)N;
        grp[NG].mul = mul;
        NG++;
        if (N > maxN) maxN = (int)N;
    }
    if (NG == 0) {
        printf("0 0\n");
        return 0;
    }

    capG = maxN;
    capV = 2 * MAXK * capG;
    perm = malloc(sizeof(int) * (size_t)MAXT * (size_t)capG);
    adj = malloc(sizeof(int) * (size_t)capV * MAXDEG);
    cnt = malloc(sizeof(int) * (size_t)capV);
    stamp = calloc((size_t)capV, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)capV);
    nx = malloc(sizeof(int) * (size_t)capV);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg c = pool[pi];
            setup(c.g, c.K);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc);
            continue;
        }
        int gi = 0, k = 1;
        if (!pick_fresh(&gi, &k)) break;
        setup(gi, k);
        random_init();
        long long cst = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cst);
        finish_run(bc);
        pool_add(bc);
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
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
# Group tables. Identity is always index 0. Element (a, b) of a semidirect
# product is coded as a*k + b; in U3(Z_n), (x, y, z) is coded as (x*n + y)*n + z.
# ----------------------------------------------------------------------------

def _cyc_table(c):
    tab = [0] * (c * c)
    for x in range(c):
        row = x * c
        for y in range(c):
            tab[row + y] = (x + y) % c
    return c, tab


def _sd_table(m, k, r):
    """Z_m x| Z_k with (a,b)*(c,e) = (a + r^b c, b + e)."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    tab = [0] * (N * N)
    for x in range(N):
        a, b = divmod(x, k)
        row = x * N
        for c in range(m):
            ra = (a + pw[b] * c) % m
            cc = c * k
            for e in range(k):
                tab[row + cc + e] = ra * k + (b + e) % k
    return N, tab


def _u3_table(n):
    """Upper unitriangular 3x3 matrices over Z_n, order n^3."""
    N = n ** 3
    trip = [(x, y, z) for x in range(n) for y in range(n) for z in range(n)]
    tab = [0] * (N * N)
    for i, (x1, y1, z1) in enumerate(trip):
        row = i * N
        for j, (x2, y2, z2) in enumerate(trip):
            tab[row + j] = (((x1 + x2) % n) * n + (y1 + y2) % n) * n + (z1 + z2 + x1 * y2) % n
    return N, tab


def _dp_table(na, ta, nb, tb):
    """Direct product; element a*nb + b."""
    N = na * nb
    tab = [0] * (N * N)
    for x in range(N):
        a1, b1 = divmod(x, nb)
        row = x * N
        for y in range(N):
            a2, b2 = divmod(y, nb)
            tab[row + y] = ta[a1 * na + a2] * nb + tb[b1 * nb + b2]
    return N, tab


def _rec_order(rec):
    t = rec[0]
    if t == "sd":
        return rec[1] * rec[2]
    if t == "u3":
        return rec[1] ** 3
    if t == "cyc":
        return rec[1]
    return _rec_order(rec[1]) * _rec_order(rec[2])


def _rec_table(rec):
    t = rec[0]
    if t == "sd":
        return _sd_table(rec[1], rec[2], rec[3])
    if t == "u3":
        return _u3_table(rec[1])
    if t == "cyc":
        return _cyc_table(rec[1])
    na, ta = _rec_table(rec[1])
    nb, tb = _rec_table(rec[2])
    return _dp_table(na, ta, nb, tb)


def _random_recipe(rng, lo, hi, depth):
    roll = rng.random()
    if roll < 0.5:
        k = rng.randint(2, 12)
        m_lo = max(2, -(-lo // k))
        m_hi = hi // k
        if m_hi < m_lo:
            return None
        m = rng.randint(m_lo, m_hi)
        if k == 2 and rng.random() < 0.3:
            return ("sd", m, 2, m - 1)
        for _ in range(40):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                return ("sd", m, k, r)
        return None
    if roll < 0.8:
        return ("u3", rng.randint(3, 9))
    if depth > 0:
        return None
    c = rng.randint(2, 6)
    base = _random_recipe(rng, -(-lo // c), hi // c, 1)
    if base is None:
        return None
    return ("prod", base, ("cyc", c))


def _group_pool(best_n, rng):
    """Choose group recipes whose orders can beat best_n for some block count K in 1..4."""
    lo, hi = best_n // 8 + 1, 800
    if hi < lo:
        return []
    half = best_n // 2
    seen, big, small = set(), [], []
    for _ in range(900):
        rec = _random_recipe(rng, lo, hi, 0)
        if rec is None or rec in seen:
            continue
        seen.add(rec)
        N = _rec_order(rec)
        if N < lo or N > hi:
            continue
        (big if N > half else small).append((N, rec))
    rng.shuffle(big)
    rng.shuffle(small)
    chosen, used = [], 0
    for N, rec in big + small:
        if len(chosen) >= 14:
            break
        if used + N * N > 1_200_000:
            continue
        chosen.append(rec)
        used += N * N
    return chosen


def _stdin_for(recs):
    """Encode group tables as the (n, edges) pair that lib.run_c writes as 'Q m' plus flat ints."""
    S = []
    for rec in recs:
        N, tab = _rec_table(rec)
        S.append(N)
        S.extend(tab)
    if len(S) % 2:
        S.append(0)
    return (len(recs), list(zip(S[0::2], S[1::2])))


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

    rng = random.Random(seed * 1000003 + best_n * 7919 + d * 131 + D)
    stdin = None
    try:
        recs = _group_pool(best_n, rng)
        if recs:
            stdin = _stdin_for(recs)
    except Exception:
        stdin = None

    remaining = 0.88 * time_limit - (time.monotonic() - start) - 2.0
    if stdin is not None and remaining >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=stdin, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
