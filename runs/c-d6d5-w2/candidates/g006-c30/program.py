import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu search over voltage lifts of semidirect products
# Z_m x| Z_k2 with a base of K A-blocks and K B-blocks.
#
# This version replaces the earlier simulated annealing with a tabu search.
# Each step samples NSAMP random single moves (change one dart's voltage, or
# swap the targets of two darts in one layer), evaluates each, and applies the
# best non-tabu move, even if it is worse. Recently touched darts are tabu for
# a short random tenure. A tabu move is allowed only if it beats the best cost
# seen in this run (aspiration). The objective is the number of uncovered
# ordered pairs from one representative per block, plus a penalty for
# duplicate darts (which would create multi-edges).
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) with
# t = l*K + i joins A_i,g to B_j,g*s for all g. Each layer's targets form a
# permutation, so every vertex has degree DEG. Left multiplication is an
# automorphism, so diameter <= D iff a BFS of depth D from each of the 2K
# block representatives reaches every vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define NSAMP 20
#define MAXKB 4
#define ITERS_PER_RUN 40000
#define STAG 3000

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

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

static int DEG, DIAM, K, K2, M, G, R, T, N;
static int best_n, best_m;
static int *best_e = NULL;
static int *Rpow, *dJ, *dS, *perm, *adj, *degc, *stamp, *fr, *nx, *tabu;
static int curstamp;

typedef struct { int type, t, t2, old, nw, l, i1, i2; } Move;

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void setup(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    N = 2 * K * G;
    T = DEG * K;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    degc = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    tabu = malloc(sizeof(int) * (size_t)T);
    curstamp = 0;
}

static void free_all(void) {
    free(Rpow); free(dJ); free(dS); free(perm); free(adj);
    free(degc); free(stamp); free(fr); free(nx); free(tabu);
    Rpow = dJ = dS = perm = adj = degc = stamp = fr = nx = tabu = NULL;
}

static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        int p[MAXKB];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            dJ[l * K + i] = p[i];
            dS[l * K + i] = rnd_int(G);
        }
    }
}

/* Rebuilds permutations and adjacency, returns total uncovered pairs (plus duplicate penalty). */
static long long eval_cost(void) {
    for (int t = 0; t < T; t++) {
        int s = dS[t];
        int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
    }
    long long pen = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (t1 % K == t2 % K && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) pen++;

    memset(degc, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = (t % K) * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (degc[a] >= DEG || degc[b] >= DEG) return BIGC * 2;
            adj[(size_t)a * DEG + degc[a]++] = b;
            adj[(size_t)b * DEG + degc[b]++] = a;
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
        total += N - count;
    }
    return total + pen * (long long)N;
}

static void apply_move(const Move *mv) {
    if (mv->type == 0) {
        dS[mv->t] = mv->nw;
    } else {
        int tmp = dJ[mv->t]; dJ[mv->t] = dJ[mv->t2]; dJ[mv->t2] = tmp;
    }
}

static void undo_move(const Move *mv) {
    if (mv->type == 0) {
        dS[mv->t] = mv->old;
    } else {
        int tmp = dJ[mv->t]; dJ[mv->t] = dJ[mv->t2]; dJ[mv->t2] = tmp;
    }
}

static void gen_move(Move *mv) {
    mv->t2 = -1;
    if (K > 1 && rnd_int(4) == 0) {
        int l = rnd_int(DEG);
        int i1 = rnd_int(K);
        int i2 = rnd_int(K - 1);
        if (i2 >= i1) i2++;
        mv->type = 1;
        mv->l = l; mv->i1 = i1; mv->i2 = i2;
        mv->t = l * K + i1;
        mv->t2 = l * K + i2;
    } else {
        int t = rnd_int(T);
        int old = dS[t];
        int nw = rnd_int(G - 1);
        if (nw >= old) nw++;
        mv->type = 0;
        mv->t = t; mv->old = old; mv->nw = nw;
    }
}

/* Tabu search from the current random state. Returns 1 if a zero-cost graph is in the state. */
static int tabu_run(void) {
    long long cur = eval_cost();
    long long bestc = cur;
    int since = 0;
    for (int i = 0; i < T; i++) tabu[i] = -1;
    for (int it = 0; it < ITERS_PER_RUN && cur > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        Move bm;
        long long bc = 0;
        int have = 0;
        for (int s = 0; s < NSAMP; s++) {
            Move mv;
            gen_move(&mv);
            apply_move(&mv);
            long long c = eval_cost();
            undo_move(&mv);
            int tb = (tabu[mv.t] > it) || (mv.t2 >= 0 && tabu[mv.t2] > it);
            if (tb && c >= bestc) continue;
            if (!have || c < bc || (c == bc && rnd_int(2))) {
                bm = mv; bc = c; have = 1;
            }
        }
        if (!have) continue;
        apply_move(&bm);
        cur = bc;
        int ten = 4 + rnd_int(T / 2 + 3);
        tabu[bm.t] = it + ten;
        if (bm.t2 >= 0) tabu[bm.t2] = it + ten;
        if (cur < bestc) { bestc = cur; since = 0; }
        else since++;
        if (since > STAG) break;
    }
    if (cur == 0) {
        eval_cost();
        return 1;
    }
    return 0;
}

static void save_best(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        int i = t % K;
        for (int g = 0; g < G; g++) {
            best_e[idx++] = i * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 8 + 2;
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
        setup(k, c2, m, r);
        random_init();
        if (tabu_run() && N > best_n) save_best();
        free_all();
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
# Driver: baselines in Python, then the C tabu search over lifts.
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

    # Spend 92% of the budget in C. The C deadline counts from program start,
    # so compile time is excluded; a 1.5 s reserve covers compile, parsing and
    # validation.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
