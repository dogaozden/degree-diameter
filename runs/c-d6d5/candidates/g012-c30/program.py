import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an arbitrary finite group given by its
# multiplication table. A base graph has K A-vertices and K B-vertices. Dart
# (i, j, s) joins A_i,g to B_j,g*s for all g, so left multiplication is an
# automorphism and the diameter check only needs BFS from the 2K block
# representatives. Simulated annealing with breakout weights and an elite pool
# (iterated local search) searches the voltages. The groups arrive on stdin as
# several tables in one run, so the whole search is a single C process.
#
# stdin payload (after the "0 m" header that lib.graph_to_text writes):
#   Q, then for each group: N, then N*N ints, entry x*N+y = x*y (identity = 0).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define BRK 150
#define MAXG 64

static uint64_t rs[2];
static struct timespec T0;

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

static int DEG, DIAM, NG, MAXT;
static long long MOORE;
static int gN[MAXG];
static int *gMul[MAXG];

static int CG, K, N, T;
static const int *MUL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static long long *wt, *unc;
static long long last_w, wsum_w;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;

typedef struct { int g, K; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * N;
    for (int g = 0; g < N; g++) pm[g] = MUL[(size_t)g * N + s];
}

/* Returns the true cost: uncovered (block rep, vertex) pairs. Sets unc[] and last_w (weighted). */
static long long eval_cost(void) {
    int NT = 2 * K * N;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = NT;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)NT);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * N, bj = (K + dJ[t]) * N;
        const int *pm = perm + (size_t)t * N;
        for (int g = 0; g < N; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * N;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NT);
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
        unc[r] = NT - count;
        total += NT - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void setup(int g, int k) {
    CG = g;
    K = k;
    N = gN[g];
    MUL = gMul[g];
    T = DEG * K;
    int NT = 2 * K * N;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * N);
    adj = malloc(sizeof(int) * (size_t)NT * DEG);
    cnt = malloc(sizeof(int) * (size_t)NT);
    stamp = calloc((size_t)NT, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NT);
    nx = malloc(sizeof(int) * (size_t)NT);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
}

static void emit(void) {
    int m = T * N;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < N; g++) {
            best_e[idx++] = dI[t] * N + g;
            best_e[idx++] = (K + dJ[t]) * N + perm[(size_t)t * N + g];
        }
    }
    best_m = m;
    best_n = 2 * K * N;
}

static void random_init(void) {
    int p[8];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dJ[t] = p[i];
            dS[t] = rnd_int(N);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

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
            dS[t] = rnd_int(N);
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
            int news = rnd_int(N);
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

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * N > best_n) emit();
    }
}

static void pool_add(long long cost, int g, int k, const int *J, const int *S, int tt) {
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
    c->g = g;
    c->K = k;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)tt);
    memcpy(c->S, S, sizeof(int) * (size_t)tt);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * gN[pool[i].g];
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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n] < groups\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    best_e = NULL;
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = 3 * DEG;
    long long mb = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        mb += p;
        p *= (DEG - 1);
        if (p > 1000000000LL) p = 1000000000LL;
    }
    MOORE = 2 * mb;

    long cap = 1 << 16, na = 0;
    int *all = malloc(sizeof(int) * (size_t)cap);
    int x;
    while (scanf("%d", &x) == 1) {
        if (na == cap) {
            cap *= 2;
            all = realloc(all, sizeof(int) * (size_t)cap);
        }
        all[na++] = x;
    }
    NG = 0;
    if (na >= 3) {
        long idx = 2;
        int Q = all[idx++];
        for (int g = 0; g < Q && g < MAXG; g++) {
            if (idx >= na) break;
            int nq = all[idx++];
            if (nq < 1) break;
            long sz = (long)nq * nq;
            if (idx + sz > na) break;
            gMul[NG] = malloc(sizeof(int) * (size_t)sz);
            memcpy(gMul[NG], all + idx, sizeof(int) * (size_t)sz);
            gN[NG] = nq;
            NG++;
            idx += sz;
        }
    }
    free(all);

    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        if (NG == 0) break;
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            int g = pool[pi].g, k = pool[pi].K;
            int tt = DEG * k;
            setup(g, k);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)tt);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)tt);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, g, k, bestJ, bestS, T);
            free_config();
            continue;
        }

        int feas_g[MAXG * 3], feas_k[MAXG * 3];
        int nf = 0;
        for (int g = 0; g < NG; g++) {
            for (int k = 1; k <= 3; k++) {
                long long nn = 2LL * k * gN[g];
                if (nn > best_n && nn <= MOORE) {
                    feas_g[nf] = g;
                    feas_k[nf] = k;
                    nf++;
                }
            }
        }
        if (nf == 0) break;
        int c = rnd_int(nf);
        setup(feas_g[c], feas_k[c]);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, CG, K, bestJ, bestS, T);
        free_config();
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
# Group construction in Python. Each group is a permutation group: a list of
# generator permutations (tuples) and the identity tuple. Elements are found
# by closure, and the multiplication table is built with numpy.
# ----------------------------------------------------------------------------

_BUDGET = 1_300_000  # total table entries sent to C


def _closure(gens, identity, cap):
    """All elements of the permutation group generated by gens; identity first. Raises if more than cap."""
    elems = [identity]
    seen = {identity}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[j] for j in g)
            if y not in seen:
                if len(elems) >= cap:
                    raise ValueError("group larger than expected")
                seen.add(y)
                elems.append(y)
    return elems


def _cayley_table(elems):
    """Flat list t with t[x*N+y] = index of elems[x] o elems[y]. Identity must be index 0."""
    N = len(elems)
    arr = np.array(elems, dtype=np.int16)
    index = {row.tobytes(): i for i, row in enumerate(arr)}
    flat = []
    for x in range(N):
        comp = arr[x][arr]  # comp[y, i] = elems[x][elems[y][i]]
        flat.extend(index[row.tobytes()] for row in comp)
    return flat


def _proj_perms(F, q, mats):
    """Permutations of the q+1 points of the projective line for 2x2 matrices (a, b, c, d)."""
    perms = []
    for a, b, c, d in mats:
        p = []
        for i in range(q + 1):
            x, y = (i, 1) if i < q else (1, 0)
            X = F.add(F.mul(a, x), F.mul(b, y))
            Y = F.add(F.mul(c, x), F.mul(d, y))
            p.append(q if Y == 0 else F.mul(X, F.inv(Y)))
        perms.append(tuple(p))
    return perms


def _vec_perms(F, q, mats):
    """Permutations of the q^2 vectors of GF(q)^2 for 2x2 matrices (a, b, c, d)."""
    perms = []
    for a, b, c, d in mats:
        p = []
        for x in range(q):
            for y in range(q):
                X = F.add(F.mul(a, x), F.mul(b, y))
                Y = F.add(F.mul(c, x), F.mul(d, y))
                p.append(X * q + Y)
        perms.append(tuple(p))
    return perms


_U = (1, 1, 0, 1)
_L = (1, 0, 1, 1)


def _psl(q):
    """PSL(2, q) acting on the projective line."""
    F = lib.GF(q)
    return _proj_perms(F, q, [_U, _L]), tuple(range(q + 1))


def _pgl(q):
    """PGL(2, q) acting on the projective line."""
    F = lib.GF(q)
    a = F.primitive_element()
    return _proj_perms(F, q, [_U, _L, (a, 0, 0, 1)]), tuple(range(q + 1))


def _sl(q):
    """SL(2, q) acting on GF(q)^2."""
    F = lib.GF(q)
    return _vec_perms(F, q, [_U, _L]), tuple(range(q * q))


def _agl(q):
    """Affine group AGL(1, q) acting on GF(q), order q(q-1)."""
    F = lib.GF(q)
    a = F.primitive_element()
    t = tuple(F.add(x, 1) for x in range(q))
    m = tuple(F.mul(a, x) for x in range(q))
    return [t, m], tuple(range(q))


def _sym(n):
    """Symmetric group S_n on n points."""
    return [tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])], tuple(range(n))


def _cyc(k):
    """Cyclic group Z_k acting on k points."""
    return [tuple(list(range(1, k)) + [0])], tuple(range(k))


def _prod(A, B):
    """Direct product of two permutation groups acting on disjoint point sets."""
    ga, ea = A
    gb, eb = B
    na, nb = len(ea), len(eb)
    gens = [tuple(list(g) + list(range(na, na + nb))) for g in ga]
    gens += [tuple(list(range(na)) + [na + x for x in g]) for g in gb]
    return gens, tuple(range(na + nb))


# (order, builder), in priority order. Only groups that can beat the current record are built.
_SPECS = [
    (504, lambda: _psl(8)),
    (506, lambda: _agl(23)),
    (360, lambda: _psl(9)),
    (168, lambda: _psl(7)),
    (120, lambda: _sl(5)),
    (336, lambda: _pgl(7)),
    (360, lambda: _prod(_sym(5), _cyc(3))),
    (360, lambda: _prod(_psl(5), _cyc(6))),
    (342, lambda: _agl(19)),
    (120, lambda: _pgl(5)),
    (660, lambda: _psl(11)),
    (600, lambda: _agl(25)),
    (702, lambda: _agl(27)),
]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    hi = lib.moore_bound(d, D)
    if best_n >= hi or d < 2 or D < 3:
        return best

    # Build the candidate groups (cheap, within a fraction of the budget).
    chosen = []
    used = 0
    for N, thunk in _SPECS:
        if not any(best_n < 2 * k * N <= hi for k in (1, 2, 3)):
            continue
        if used + N * N > _BUDGET or time.monotonic() - start > 0.25 * time_limit:
            continue
        try:
            gens, ident = thunk()
            elems = _closure(gens, ident, N)
            if len(elems) != N:
                continue
            flat = _cayley_table(elems)
        except Exception:
            continue
        chosen.append((N, flat))
        used += N * N

    rem = 0.85 * time_limit - (time.monotonic() - start) - 4.0
    if not chosen or rem < 3.0:
        return best

    payload = [len(chosen)]
    for N, flat in chosen:
        payload.append(N)
        payload.extend(flat)
    if len(payload) % 2:
        payload.append(0)
    edges = list(zip(payload[::2], payload[1::2]))

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{rem:.2f}", best_n],
                        stdin_graph=(0, edges), timeout=rem + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
