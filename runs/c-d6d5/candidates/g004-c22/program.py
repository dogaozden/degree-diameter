import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-coset (voltage) lifts over semidirect products Z_m x| Z_k2 with
# base K in {1,2,3,4} A-vertices and K B-vertices. Search is tabu search with
# sampled neighbourhoods (replacing the earlier annealing), and duplicate edges
# are penalised rather than forbidden, so the search can move through them.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = l*K + i (layer l)
# joins A_i,g to B_{dJ[t]}, g*dS[t] for all g. Each layer is a permutation of
# the B-blocks, so every vertex has degree DEG. Left multiplication is an
# automorphism, so diameter <= D iff BFS of depth D from the 2K block
# representatives reaches every vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 4
#define DUPPEN 100000LL
#define NB 36
#define STALL 250
#define ELITE 12
#define TENURE 6
#define TABU_ITERS 2500

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Cfg;

typedef struct {
    int type;      /* 0: change dS[t]; 1: swap dJ[t] and dJ[t2] */
    int t, t2, old, news;
} Move;

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
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM, K, K2, M, G, T, N, R;
static int *Rpow, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS, *tabu_until;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static Cfg elite[ELITE];
static int nelite = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
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

/* BFS from src up to DIAM levels; returns the number of vertices not reached. */
static long long bfs_bad(int src) {
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
    return (long long)(N - count);
}

/* Cost = unreached (block representative, vertex) pairs + DUPPEN per duplicate dart pair. */
static long long eval_cost(void) {
    long long dups = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (t1 % K == t2 % K && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dups++;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = (t % K) * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) total += bfs_bad(r * G);
    return total + DUPPEN * dups;
}

static void alloc_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    T = DEG * K;
    N = 2 * K * G;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    tabu_until = calloc((size_t)2 * T, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    curstamp = 0;
}

static void free_group(void) {
    free(Rpow); free(dJ); free(dS); free(bestJ); free(bestS); free(tabu_until);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    Rpow = dJ = dS = bestJ = bestS = tabu_until = perm = adj = cnt = stamp = fr = nx = NULL;
}

static void random_init(void) {
    int p[KMAX];
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

static void apply_move(const Move *mv) {
    if (mv->type == 0) {
        dS[mv->t] = mv->news;
        build_perm(mv->t);
    } else {
        int tmp = dJ[mv->t]; dJ[mv->t] = dJ[mv->t2]; dJ[mv->t2] = tmp;
    }
}

static void undo_move(const Move *mv) {
    if (mv->type == 0) {
        dS[mv->t] = mv->old;
        build_perm(mv->t);
    } else {
        int tmp = dJ[mv->t]; dJ[mv->t] = dJ[mv->t2]; dJ[mv->t2] = tmp;
    }
}

static void random_move(Move *mv) {
    if (K > 1 && rnd_unit() < 0.3) {
        int l = rnd_int(DEG);
        int i1 = rnd_int(K);
        int i2 = rnd_int(K - 1);
        if (i2 >= i1) i2++;
        mv->type = 1;
        mv->t = l * K + i1;
        mv->t2 = l * K + i2;
        mv->old = mv->news = 0;
        return;
    }
    int t = rnd_int(T);
    int old = dS[t];
    int news = old;
    if (G > 1) {
        news = rnd_int(G - 1);
        if (news >= old) news++;
    }
    mv->type = 0;
    mv->t = t;
    mv->t2 = 0;
    mv->old = old;
    mv->news = news;
}

static int is_tabu(const Move *mv, int it) {
    if (mv->type == 0) return tabu_until[mv->t] > it;
    return tabu_until[T + mv->t] > it || tabu_until[T + mv->t2] > it;
}

static void mark_tabu(const Move *mv, int until) {
    if (mv->type == 0) {
        tabu_until[mv->t] = until;
    } else {
        tabu_until[T + mv->t] = until;
        tabu_until[T + mv->t2] = until;
    }
}

/* Tabu search over sampled neighbourhoods. Best state goes to bestJ/bestS; returns its cost. */
static long long tabu_run(int iters, long long cost) {
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    memset(tabu_until, 0, sizeof(int) * (size_t)(2 * T));
    int stall = 0;
    for (int it = 1; it <= iters && bestc > 0; it++) {
        if (elapsed() > DEADLINE) break;
        int have = 0;
        long long bc = 0;
        Move bm;
        for (int c = 0; c < NB; c++) {
            Move mv;
            random_move(&mv);
            apply_move(&mv);
            long long c2 = eval_cost();
            undo_move(&mv);
            if (is_tabu(&mv, it) && c2 >= bestc) continue;
            if (!have || c2 < bc || (c2 == bc && rnd_int(2))) {
                have = 1;
                bc = c2;
                bm = mv;
            }
        }
        if (!have) continue;
        apply_move(&bm);
        cost = bc;
        mark_tabu(&bm, it + TENURE + rnd_int(4));
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
            stall = 0;
        } else if (++stall > STALL) {
            break;
        }
    }
    return bestc;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = (t % K) * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = N;
}

/* A zero-cost run is a valid simple bipartite graph; emit it if it beats the record. */
static void finish_run(long long bc) {
    if (bc == 0 && 2LL * K * G > best_n) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        emit();
    }
}

static void elite_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= DUPPEN) return;
    int slot;
    if (nelite < ELITE) {
        slot = nelite++;
    } else {
        slot = 0;
        for (int i = 1; i < ELITE; i++)
            if (elite[i].cost > elite[slot].cost) slot = i;
        if (elite[slot].cost <= cost) return;
    }
    Cfg *c = &elite[slot];
    c->K = K; c->K2 = K2; c->M = M; c->R = R; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Pick an elite whose group order still beats the record (best of 3 by cost). */
static int pick_elite(void) {
    int cand[ELITE], nc = 0;
    for (int i = 0; i < nelite; i++) {
        long long nn = 2LL * elite[i].K * elite[i].K2 * elite[i].M;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (elite[c].cost < elite[bi].cost) bi = c;
    }
    return bi;
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
    for (int i = 0; i < ELITE; i++) {
        elite[i].J = malloc(sizeof(int) * (size_t)(DEG * KMAX));
        elite[i].S = malloc(sizeof(int) * (size_t)(DEG * KMAX));
        elite[i].cost = DUPPEN;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* Base sizes K weighted towards 2 and 3; K = 4 gives the widest base. */
    static const int kc[8] = {1, 2, 2, 2, 3, 3, 4, 4};
    while (elapsed() < DEADLINE) {
        int ei = -1;
        if (nelite > 0 && rnd_unit() < 0.55) ei = pick_elite();
        if (ei >= 0) {
            /* Perturb an elite configuration and re-search it with tabu. */
            Cfg c = elite[ei];
            alloc_group(c.K, c.K2, c.M, c.R);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            int nm = 3 + rnd_int(5);
            for (int s = 0; s < nm; s++) {
                Move mv;
                random_move(&mv);
                apply_move(&mv);
            }
            long long cst = eval_cost();
            long long bc = tabu_run(TABU_ITERS, cst);
            finish_run(bc);
            elite_add(bc, bestJ, bestS);
            free_group();
            continue;
        }

        /* Fresh random lift over a group of order near the record. */
        int k = kc[rnd_int(8)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 4 + 3;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                c2 = 1;
                m = g;
                r = 1;
            }
        }
        alloc_group(k, c2, m, r);
        random_init();
        long long cst = eval_cost();
        long long bc = tabu_run(TABU_ITERS, cst);
        finish_run(bc);
        elite_add(bc, bestJ, bestS);
        free_group();
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
# Driver: baselines in Python, then the C tabu search over base-K lifts.
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

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
