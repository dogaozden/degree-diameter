import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an ARBITRARY finite group given by a
# multiplication table. The Python driver supplies several groups (cyclic,
# abelian Z_a x Z_b, semidirect Z_m x| Z_k, and affine groups Z_p x| Z_k acting
# on the line over GF(p)). The graph has 2K base blocks of G vertices each:
# A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h. Dart t = (i, j, s) joins
# A_{i,g} to B_{j,g*s} for all g. Each layer is a permutation, so every vertex
# has degree DEG. Left multiplication is an automorphism, so diameter <= D iff
# BFS of depth D from one vertex per block covers the whole graph.
#
# Search: simulated annealing with breakout weights, plus iterated local search
# from an elite pool. Groups are chosen so that 2*K*G beats the current best.
#
# Input (stdin, in the graph text format): the header is ignored, and the
# edge tokens form the stream "NG, then for each group: G, then G*G entries".
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
#define POOLMAX 40
#define POOLP 0.5
#define BRK 120
#define MAXDEG 16
#define MAXK 3
#define MAXT (MAXDEG * MAXK)
#define MAXGROUPS 64

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

static int DEG, DIAM;
static int NG = 0;
static int gord[MAXGROUPS];
static int *gtab[MAXGROUPS];

static int K, G, T, GI;
static const int *mt;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;

typedef struct {
    int K, GI;
    long long cost;
    int J[MAXT], S[MAXT];
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mt[g * G + s];
}

/* Returns the true cost (sum of uncovered vertices over block representatives).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = N;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
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
            memset(stamp, 0, sizeof(int) * (size_t)N);
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
        unc[r] = N - count;
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_config(void) {
    int N = 2 * K * G;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
}

static void setup_group(int k, int gi) {
    K = k;
    GI = gi;
    G = gord[gi];
    mt = gtab[gi];
    T = DEG * K;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
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
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

/* Annealing on the weighted cost with breakout weight bumps. The caller must
   have just called eval_cost(). Returns the best true cost; the best state is
   stored in bestJ/bestS. */
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
                eval_cost();
                wcur = last_w;
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

/* A zero-cost run is a valid graph: emit it if it beats the current best. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2 * K * G > best_n) emit();
}

static void pool_add(long long cost, const int *J, const int *S) {
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
    c->K = K;
    c->GI = GI;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (2LL * pool[i].K * gord[pool[i].GI] > best_n) cand[nc++] = i;
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
        fprintf(stderr, "usage: prog d D seed time_limit [best_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    /* Input: graph header "n m", then the 2m tokens of the group stream. */
    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    (void)hn;
    int want = 0;
    if (hm > 0 && scanf("%d", &want) != 1) want = 0;
    int got = 0;
    for (int gi = 0; gi < want && gi < MAXGROUPS; gi++) {
        int g = 0;
        if (scanf("%d", &g) != 1 || g < 2 || g > 2000) break;
        int *tab = malloc(sizeof(int) * (size_t)g * g);
        int fail = 0;
        for (int x = 0; x < g * g; x++) {
            if (scanf("%d", &tab[x]) != 1 || tab[x] < 0 || tab[x] >= g) { fail = 1; break; }
        }
        if (fail) { free(tab); break; }
        gord[gi] = g;
        gtab[gi] = tab;
        got++;
    }
    NG = got;
    if (NG == 0) {
        printf("0 0\n");
        return 0;
    }

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            setup_group(c.K, c.GI);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
            continue;
        }

        /* Fresh random lift over a random group that can still beat best_n. */
        int feas[MAXK], nf = 0;
        for (int kk = 1; kk <= MAXK; kk++) {
            int any = 0;
            for (int gi = 0; gi < NG; gi++)
                if (2LL * kk * gord[gi] > best_n) any = 1;
            if (any) feas[nf++] = kk;
        }
        if (nf == 0) break;
        int k = feas[rnd_int(nf)];
        int cand[MAXGROUPS], nc = 0;
        for (int gi = 0; gi < NG; gi++)
            if (2LL * k * gord[gi] > best_n) cand[nc++] = gi;
        int gi = cand[rnd_int(nc)];
        setup_group(k, gi);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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
# Safe baseline: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group families (multiplication tables are passed to C as integer streams).
# ----------------------------------------------------------------------------

def _is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def _factor_set(n):
    out, x, f = set(), n, 2
    while f * f <= x:
        while x % f == 0:
            out.add(f)
            x //= f
        f += 1
    if x > 1:
        out.add(x)
    return out


def _primitive_root(p):
    fs = _factor_set(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    return 1


def _candidates(lo, hi):
    """Group specs (kind, order, spec) with lo <= order <= hi."""
    out = []
    for m in range(max(lo, 2), hi + 1):
        out.append(("cyc", m, ("cyc", m)))
    for a in range(2, 13):
        for b in range(a, hi // a + 1):
            order = a * b
            if lo <= order <= hi:
                out.append(("abel", order, ("abel", a, b)))
    for m in range(3, hi // 2 + 1):
        for k in range(2, 13):
            order = m * k
            if order < lo or order > hi:
                continue
            r = next((r for r in range(2, min(m, 60))
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1), None)
            if r is not None:
                out.append(("semi", order, ("semi", m, k, r)))
    for p in range(5, hi + 1):
        if not _is_prime(p):
            continue
        for k in range(2, p):
            if (p - 1) % k == 0 and lo <= p * k <= hi:
                out.append(("aff", p * k, ("aff", p, k)))
    return out


def _make_mul(spec):
    """Return (order, mul) for a group spec; elements are ints 0..order-1."""
    kind = spec[0]
    if kind == "cyc":
        m = spec[1]
        return m, (lambda x, y, m=m: (x + y) % m)
    if kind == "abel":
        a, b = spec[1], spec[2]

        def mul_ab(x, y, a=a, b=b):
            i1, j1 = divmod(x, b)
            i2, j2 = divmod(y, b)
            return ((i1 + i2) % a) * b + (j1 + j2) % b

        return a * b, mul_ab
    if kind == "semi":
        m, k, r = spec[1], spec[2], spec[3]
        order, mul, _inv = lib.semidirect_group(m, k, r)
        return order, mul
    # Affine group x -> a x + b over GF(p), with a in the subgroup of order k.
    p, k = spec[1], spec[2]
    g = _primitive_root(p)
    h = pow(g, (p - 1) // k, p)
    hp = [pow(h, i, p) for i in range(k)]

    def mul_aff(x, y, p=p, k=k, hp=hp):
        i1, b1 = divmod(x, p)
        i2, b2 = divmod(y, p)
        return ((i1 + i2) % k) * p + (hp[i1] * b2 + b1) % p

    return p * k, mul_aff


def _group_stream(best_n):
    """Edge list whose flat tokens encode NG and the group tables, or None."""
    lo = best_n // 6 + 1
    hi = min(480, best_n // 2 + 60)
    if lo > hi:
        return None
    cands = _candidates(lo, hi)
    if not cands:
        return None
    kinds = ["semi", "aff", "abel", "cyc"]
    num_targets = 16
    used, chosen = set(), []
    spent, budget = 0, 2_200_000
    for j in range(num_targets):
        target = lo + (hi - lo) * j / max(1, num_targets - 1)
        kind = kinds[j % len(kinds)]
        free = [i for i in range(len(cands)) if i not in used]
        if not free:
            break
        same = [i for i in free if cands[i][0] == kind]
        pool_ = same or free
        i = min(pool_, key=lambda t: abs(cands[t][1] - target))
        order = cands[i][1]
        if spent + order * order > budget:
            continue
        used.add(i)
        spent += order * order
        chosen.append(cands[i][2])
    if not chosen:
        return None
    flat = [len(chosen)]
    for spec in chosen:
        order, mul = _make_mul(spec)
        flat.append(order)
        flat.extend(mul(x, y) for x in range(order) for y in range(order))
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid graph found: PG(2,q) baseline, then the C group-lift search."""
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

    if best_n >= lib.moore_bound(d, D):
        return best

    try:
        stream = _group_stream(best_n)
    except Exception:
        stream = None

    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if stream and remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=(0, stream), timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
