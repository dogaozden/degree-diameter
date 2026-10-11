"""Combined search: tabu voltage lifts with an elite pool, and safe algebraic fallbacks.

The C engine searches voltage lifts of semidirect products Z_m x| Z_k2 over a base of
K A-vertices and K B-vertices. Vertices are A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h,
and dart t = (i, j, s) joins A_{i,g} to B_{j,g*s} for all g. Each layer is a permutation,
so every vertex has degree DEG. Left multiplication by G is an automorphism, so the
diameter is at most DIAM iff a BFS of depth DIAM from each of the 2K block
representatives covers everything.

Search, per run:
- Fresh runs start from a random lift over a group of order just above the record and
  run tabu search. Each step scans all G voltages of one random dart and takes the best
  non-tabu move, which may be worse. Within-layer target swaps are also scanned. After a
  stagnation window the search restarts from the best state with a partial perturbation.
- Pool runs (iterated local search) pick an elite configuration whose group order still
  beats the record, perturb it, and run tabu search again. Runs that reach cost 0 are
  emitted if they beat the current best order.

Python builds the algebraic baselines (projective plane, generalized quadrangle, K_{d,d}),
passes the best order so far to C, and validates every result with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define POOLMAX 32
#define STAG 200
#define FRESH_ITERS 3000
#define ILS_ITERS 1500
#define POOLP 0.6
#define MAXK 3

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

static double DEADLINE = 0.0;
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM, K, K2, M, R, G, T, N, MAXT;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stampv, *fr, *nx;
static int *bestJ, *bestS;
static long long *tabu;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void rebuild_all(void) {
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Number of (representative, vertex) pairs at distance > DIAM. Zero means valid. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
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
            memset(stampv, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stampv[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stampv[v] != curstamp) {
                        stampv[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        total += N - count;
    }
    return total;
}

static void setup_group(int k, int k2, int m, int r) {
    K = k; K2 = k2; M = m; R = r;
    G = m * k2;
    T = DEG * k;
    N = 2 * k * G;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stampv = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    tabu = calloc((size_t)T * G, sizeof(long long));
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_config(void) {
    free(Rpow); free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stampv); free(fr); free(nx); free(tabu);
    Rpow = NULL; dI = dJ = dS = bestJ = bestS = perm = NULL;
    adj = NULL; cnt = stampv = fr = nx = NULL; tabu = NULL;
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

/* Random kicks: within-layer target swaps and voltage changes (layers stay permutations). */
static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
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

static void save_best_state(void) {
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
}

static void load_best_state(void) {
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    rebuild_all();
}

/* Tabu search from the current state (cost must match it). Leaves the best state loaded. */
static long long run_tabu(int maxit, long long cost, int *timed_out) {
    long long best = cost;
    long long it = 0, last = 0;
    *timed_out = 0;
    save_best_state();
    while (best > 0 && it < maxit) {
        if (elapsed() > DEADLINE) { *timed_out = 1; break; }
        it++;
        if (K > 1 && rnd_int(5) == 0) {
            int l = rnd_int(DEG);
            long long bc = BIGC;
            int b1 = -1, b2 = -1, ties = 0;
            for (int i1 = 0; i1 < K; i1++) {
                for (int i2 = i1 + 1; i2 < K; i2++) {
                    int t1 = l * K + i1, t2 = l * K + i2;
                    int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                    long long c = eval_cost();
                    tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                    if (c < bc) {
                        bc = c; b1 = t1; b2 = t2; ties = 1;
                    } else if (c == bc) {
                        ties++;
                        if (rnd_int(ties) == 0) { b1 = t1; b2 = t2; }
                    }
                }
            }
            if (b1 >= 0) {
                int tmp = dJ[b1]; dJ[b1] = dJ[b2]; dJ[b2] = tmp;
                cost = bc;
            }
        } else {
            int t = rnd_int(T);
            int old = dS[t];
            long long bc = BIGC;
            int bv = -1, ties = 0, aborted = 0;
            for (int v = 0; v < G; v++) {
                if (v == old) continue;
                if ((v & 31) == 31 && elapsed() > DEADLINE) { aborted = 1; break; }
                dS[t] = v;
                build_perm(t);
                long long c = eval_cost();
                int is_tabu = tabu[(size_t)t * G + v] > it;
                if (is_tabu && c >= best) continue;
                if (c < bc) {
                    bc = c; bv = v; ties = 1;
                } else if (c == bc) {
                    ties++;
                    if (rnd_int(ties) == 0) bv = v;
                }
            }
            dS[t] = old;
            build_perm(t);
            if (aborted) { *timed_out = 1; break; }
            if (bv >= 0) {
                dS[t] = bv;
                build_perm(t);
                cost = bc;
                tabu[(size_t)t * G + old] = it + 5 + rnd_int(10);
            }
        }

        if (cost < best) {
            best = cost;
            save_best_state();
            last = it;
        }
        if (it - last > STAG && best > 0) {
            /* Iterated tabu: restart from the best state with a partial perturbation. */
            load_best_state();
            for (int t = 0; t < T; t++)
                if (rnd_unit() < 0.2) dS[t] = rnd_int(G);
            rebuild_all();
            cost = eval_cost();
            last = it;
        }
    }
    load_best_state();
    return best;
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
    c->K = K; c->K2 = K2; c->M = M; c->R = R; c->cost = cost;
    memcpy(c->J, bestJ, sizeof(int) * (size_t)T);
    memcpy(c->S, bestS, sizeof(int) * (size_t)T);
}

/* Pick an elite entry whose group order still beats the record (best of 3 samples). */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].K2 * pool[i].M;
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
    best_n = N;
}

static void finish_run(long long bc) {
    if (bc == 0 && N > best_n) emit();
}

/* Choose a group of order g: semidirect Z_m x| Z_c2 with m*c2 = g, mostly non-abelian. */
static void choose_group(int g, int *c2o, int *mo, int *ro) {
    int all[16], na = 0, nab[16], nn = 0;
    for (int c = 1; c <= 12; c++) {
        if (g % c == 0 && g / c >= 2) {
            all[na++] = c;
            if (c >= 2) nab[nn++] = c;
        }
    }
    int c2;
    if (nn > 0 && rnd_unit() < 0.75) c2 = nab[rnd_int(nn)];
    else c2 = all[rnd_int(na)];
    int m = g / c2, r = 1;
    if (c2 > 1) {
        int found = 0;
        if (m >= 3) {
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 2 + rnd_int(m - 2);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
        }
        if (!found) {
            c2 = 1; m = g; r = 1;
        }
    }
    *c2o = c2; *mo = m; *ro = r;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = 3 * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    int stop = 0;
    while (!stop && elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-run tabu. */
            int k = pool[pi].K, k2 = pool[pi].K2, m = pool[pi].M, r = pool[pi].R;
            setup_group(k, k2, m, r);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
            rebuild_all();
            perturb(2 + rnd_int(4));
            rebuild_all();
            long long c = eval_cost();
            int to = 0;
            long long bc = run_tabu(ILS_ITERS, c, &to);
            finish_run(bc);
            pool_add(bc);
            free_config();
            if (to) stop = 1;
            continue;
        }

        /* Fresh random lift over a group of order just above the record. */
        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        if (2 * k * g > 300000) break;
        int c2, m, r;
        choose_group(g, &c2, &m, &r);
        setup_group(k, c2, m, r);
        random_init();
        long long c = eval_cost();
        int to = 0;
        long long bc = run_tabu(FRESH_ITERS, c, &to);
        finish_run(bc);
        pool_add(bc);
        free_config();
        if (to) stop = 1;
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
# Algebraic baselines.
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

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
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
