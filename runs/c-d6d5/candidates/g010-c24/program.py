import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Approach: lifts over arbitrary finite groups given as multiplication tables.
#
# The earlier engine only used semidirect products Z_m x| Z_k. Here Python
# builds other groups (affine subgroups of AGL(1,p), dihedral groups, SL(2,p),
# and direct products with small cyclic groups) and passes each one as a
# multiplication table. The C engine places K A-vertices and K B-vertices in
# each group block. Dart (i, j, s) in layer l joins A_{i,g} to B_{j, g*s}, and
# each layer is a permutation of K, so the graph is DEG-regular and bipartite.
# Left multiplication is an automorphism, so diameter <= D iff BFS of depth D
# from the 2K block representatives covers every vertex. The C engine runs
# simulated annealing with breakout weights and perturbation restarts from the
# best state.
#
# Python tries (group, K) pairs whose vertex count 2*K*|G| beats the current
# best, smallest first, and keeps the best graph that lib.is_valid accepts.
# A valid fallback (incidence graph, W(q), or K_{d,d}) is always kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 3000
#define BRK 120
#define MAXK 8

static struct timespec T0;
static double DEADLINE;
static uint64_t rs[2];

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

static int DEG, DIAM, K, G, T, N;
static int *MUL;
static int *dI, *dJ, *dS, *bestJ, *bestS, *gJ, *gS;
static int *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;
static long long *wt, *unc;
static long long wsum = 0;
static long long last_w = 0;
static long long gcost = BIGC;

static void alloc_all(void) {
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    gJ = malloc(sizeof(int) * (size_t)T);
    gS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * (size_t)G);
    adj = malloc(sizeof(int) * (size_t)N * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * (size_t)G;
    for (int g = 0; g < G; g++) pm[g] = MUL[g * G + s];
}

static void rebuild_all(void) {
    for (int t = 0; t < T; t++) build_perm(t);
}

static void reset_weights(void) {
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
    wsum = 2 * K;
}

/* Returns the number of uncovered ordered pairs from the block representatives.
   Sets unc[r] per block and last_w to the breakout-weighted cost. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * (size_t)G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = r * G;
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
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    rebuild_all();
}

static void load_state(const int *J, const int *S) {
    memcpy(dJ, J, sizeof(int) * (size_t)T);
    memcpy(dS, S, sizeof(int) * (size_t)T);
    rebuild_all();
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
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

/* Simulated annealing on the weighted cost, with breakout weight bumps.
   Returns the best true cost; the best state goes to bestJ/bestS. */
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

static void emit_graph(const int *J, const int *S) {
    load_state(J, S);
    int m = T * G;
    printf("%d %d\n", 2 * K * G, m);
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            int a = dI[t] * G + g;
            int b = (K + dJ[t]) * G + MUL[g * G + dS[t]];
            printf("%d %d\n", a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit K  (stdin: group table as n m + pairs)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    uint64_t sm = sd * 2654435761ULL + 991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int gin, mIn;
    if (scanf("%d %d", &gin, &mIn) != 2 || gin < 1 || mIn != gin * gin) {
        printf("0 0\n");
        return 0;
    }
    if (DEG < 1 || DIAM < 1 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    G = gin;
    MUL = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int i = 0; i < mIn; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= mIn || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        MUL[u] = v;
    }

    alloc_all();
    int found = 0;
    while (!found && elapsed() < DEADLINE) {
        if (gcost < BIGC && rnd_unit() < 0.5) {
            load_state(gJ, gS);
            perturb(2 + rnd_int(4));
            rebuild_all();
        } else {
            random_init();
        }
        reset_weights();
        long long c0 = eval_cost();
        double ts = gcost < BIGC ? 0.4 : 1.0;
        long long bc = run_sa(ITERS, ts, c0);
        if (bc == 0) {
            emit_graph(bestJ, bestS);
            found = 1;
            break;
        }
        if (bc < gcost) {
            gcost = bc;
            memcpy(gJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(gS, bestS, sizeof(int) * (size_t)T);
        }
    }
    if (!found) printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group tables. Each builder returns (order, table) where table[x*G + y] is
# the index of the product of elements x and y.
# ----------------------------------------------------------------------------

MAXG = 600


def _from_mul(elems, mul):
    """Multiplication table of a finite group given by its element list and product function."""
    idx = {e: i for i, e in enumerate(elems)}
    return len(elems), [idx[mul(a, b)] for a in elems for b in elems]


def _cyclic(c):
    return _from_mul(list(range(c)), lambda x, y: (x + y) % c)


def _affine(p, k):
    """Subgroup of AGL(1,p) of maps x -> a*x + b with a^k = 1 (order p*k)."""
    mus = [a for a in range(1, p) if pow(a, k, p) == 1]
    elems = [(a, b) for a in mus for b in range(p)]
    return _from_mul(elems, lambda x, y: ((x[0] * y[0]) % p, (x[0] * y[1] + x[1]) % p))


def _dihedral(n):
    """Dihedral group of order 2n."""
    elems = [(r, s) for s in range(2) for r in range(n)]

    def mul(x, y):
        r1, s1 = x
        r2, s2 = y
        return ((r1 + (r2 if s1 == 0 else -r2)) % n, (s1 + s2) % 2)

    return _from_mul(elems, mul)


def _sl2(p):
    """SL(2, p) for prime p."""
    elems = [m for m in itertools.product(range(p), repeat=4) if (m[0] * m[3] - m[1] * m[2]) % p == 1]

    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)

    return _from_mul(elems, mul)


def _product(A, B):
    """Direct product of two groups given as (order, table)."""
    GA, TA = A
    GB, TB = B
    G = GA * GB
    T = [0] * (G * G)
    for x1 in range(GA):
        for x2 in range(GB):
            x = x1 * GB + x2
            for y1 in range(GA):
                a = TA[x1 * GA + y1] * GB
                for y2 in range(GB):
                    T[x * G + y1 * GB + y2] = a + TB[x2 * GB + y2]
    return G, T


def _is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def _specs():
    """(order, thunk) pairs for the candidate groups; thunks build the tables lazily."""
    base = []
    for p in range(3, 60):
        if not _is_prime(p):
            continue
        for k in range(2, p):
            if (p - 1) % k == 0 and p * k <= MAXG:
                base.append((p * k, lambda p=p, k=k: _affine(p, k)))
    for n in range(3, MAXG // 2 + 1):
        base.append((2 * n, lambda n=n: _dihedral(n)))
    for p in (3, 5, 7):
        base.append((p * (p * p - 1), lambda p=p: _sl2(p)))
    specs = list(base)
    for c in range(2, 6):
        for o, th in base:
            if o * c <= MAXG:
                specs.append((o * c, lambda th=th, c=c: _product(th(), _cyclic(c))))
    small = [(o, th) for o, th in base if o <= 60]
    for i, (o1, th1) in enumerate(small):
        for o2, th2 in small[i:]:
            if o1 * o2 <= MAXG:
                specs.append((o1 * o2, lambda a=th1, b=th2: _product(a(), b())))
    return specs


def _plan(best_n, seed, specs):
    """(declared order, tiebreak, K, thunk) for every group and K that could beat best_n, smallest first."""
    rng = random.Random(seed)
    out = []
    for g, th in specs:
        if g > MAXG:
            continue
        for K in (1, 2, 3):
            N = 2 * K * g
            if N > best_n:
                out.append((N, rng.random(), K, th))
    out.sort(key=lambda t: (t[0], t[1]))
    return out[:80]


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
# Driver: baselines, then group-table lifts searched by the C annealer.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Reserve time for the one-off C compile (outside the C deadline), parsing and validation.
    deadline = start + 0.85 * time_limit - 2.5
    if d >= 2 and D >= 2:
        plan = _plan(best_n, seed, _specs())
        for _, _, K, th in plan:
            remaining = deadline - time.monotonic()
            if remaining < 1.5:
                break
            try:
                g, table = th()
            except Exception:
                continue
            if 2 * K * g <= best_n:
                continue
            slice_s = min(max(remaining / 10.0, 2.0), 4.0, remaining)
            stdin_graph = (g, [(i, table[i]) for i in range(g * g)])
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{slice_s:.2f}", K],
                                stdin_graph=stdin_graph, timeout=slice_s + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
