import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over semidirect products Z_m x| Z_k2 with a base of
# K A-vertices and K B-vertices. Each group is searched by a tabu search with
# full-neighbourhood moves (every voltage of a chosen dart, or every target
# swap inside a layer), not by annealing. Tabu tenure forbids immediately
# undoing a move, with aspiration when a move beats the group's best. After
# STALL_MAX steps without improvement the search kicks the best state and
# continues. The number of kicks is capped, then a new random group is drawn.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex has
# degree DEG. Left multiplication is an automorphism, so the diameter is <= D
# iff BFS of depth D from each of the 2K block representatives covers all.
#
# Group orders are sampled between the current best order and a floor value
# supplied by the driver, so the search can climb while still aiming high.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define NSAMP 80
#define STALL_MAX 300
#define MAX_ROUNDS 8
#define GROUP_SECS 6.0

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

static int DEG, DIAM, K, K2, M, G, T, R, N;
static int FLOORN;
static int *Rpow;
static int *dI, *dJ, *dS, *bJ, *bS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static long long *tabu_until;
static int curstamp;
static int best_n, best_m;
static int *best_e = NULL;

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

static int dup_check(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return 1;
    return 0;
}

/* Sum over the 2K block representatives of uncovered vertices after DIAM steps. 0 means valid. */
static long long eval_cost(void) {
    if (dup_check()) return BIGC;
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
        total += N - count;
    }
    return total;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    tabu_until = malloc(sizeof(long long) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    curstamp = 0;
    for (int t = 0; t < T; t++) {
        dI[t] = t % K;
        dJ[t] = 0;
        dS[t] = 0;
        tabu_until[t] = 0;
    }
}

static void free_group(void) {
    free(dI); free(dJ); free(dS); free(bJ); free(bS); free(tabu_until);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
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
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Change the voltage of one random dart to its best non-tabu alternative (aspiration allowed). */
static void volt_move(long long *cur, long long gbest, long long it) {
    int t = rnd_int(T);
    int olds = dS[t];
    int nopt = G - 1;
    int full = (nopt <= NSAMP);
    int ns = full ? nopt : NSAMP;
    long long bc = BIGC * 4;
    int bs = -1, ties = 0;
    for (int q = 0; q < ns; q++) {
        int s;
        if (full) {
            s = (q < olds) ? q : q + 1;
        } else {
            s = rnd_int(G);
            if (s == olds) continue;
        }
        dS[t] = s;
        build_perm(t);
        long long c = eval_cost();
        if (tabu_until[t] > it && c >= gbest) continue;
        if (c < bc) {
            bc = c; bs = s; ties = 1;
        } else if (c == bc && rnd_int(++ties) == 0) {
            bs = s;
        }
    }
    dS[t] = olds;
    build_perm(t);
    if (bs < 0) return;
    dS[t] = bs;
    build_perm(t);
    *cur = bc;
    tabu_until[t] = it + 2 + rnd_int(6);
}

/* Swap the targets of two darts inside one layer (keeps the layer a permutation). */
static void swap_move(long long *cur, long long gbest, long long it) {
    int l = rnd_int(DEG);
    long long bc = BIGC * 4;
    int b1 = -1, b2 = -1, ties = 0;
    for (int i1 = 0; i1 < K; i1++) {
        for (int i2 = i1 + 1; i2 < K; i2++) {
            int t1 = l * K + i1, t2 = l * K + i2;
            int tb = (tabu_until[t1] > it) || (tabu_until[t2] > it);
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c = eval_cost();
            tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            if (tb && c >= gbest) continue;
            if (c < bc) {
                bc = c; b1 = t1; b2 = t2; ties = 1;
            } else if (c == bc && rnd_int(++ties) == 0) {
                b1 = t1; b2 = t2;
            }
        }
    }
    if (b1 < 0) return;
    int tmp = dJ[b1]; dJ[b1] = dJ[b2]; dJ[b2] = tmp;
    *cur = bc;
    tabu_until[b1] = it + 2 + rnd_int(6);
    tabu_until[b2] = tabu_until[b1];
}

/* Tabu search inside one group. Leaves dJ/dS/perm at the best state found. */
static long long tabu_group(double gend) {
    long long cur = eval_cost();
    long long best = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    long long it = 0;
    int stall = 0, rounds = 0;
    while (cur > 0) {
        if ((it & 7) == 0 && (elapsed() > DEADLINE || elapsed() > gend)) break;
        it++;
        if (K > 1 && rnd_unit() < 0.2) swap_move(&cur, best, it);
        else volt_move(&cur, best, it);
        if (cur < best) {
            best = cur;
            stall = 0;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
        } else {
            stall++;
        }
        if (stall > STALL_MAX) {
            rounds++;
            if (rounds > MAX_ROUNDS) break;
            memcpy(dJ, bJ, sizeof(int) * (size_t)T);
            memcpy(dS, bS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            int kicks = 2 + rnd_int(3);
            for (int k = 0; k < kicks; k++) {
                int t = rnd_int(T);
                dS[t] = rnd_int(G);
                build_perm(t);
            }
            cur = eval_cost();
            if (cur < best) {
                best = cur;
                memcpy(bJ, dJ, sizeof(int) * (size_t)T);
                memcpy(bS, dS, sizeof(int) * (size_t)T);
            }
            stall = 0;
            for (int t = 0; t < T; t++) tabu_until[t] = 0;
        }
    }
    memcpy(dJ, bJ, sizeof(int) * (size_t)T);
    memcpy(dS, bS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    return best;
}

/* Pick a group whose order gives a graph larger than the current best.
   Half the draws sample near the floor (aim high), half sample from the current best upward. */
static void pick_group(int *ko, int *c2o, int *mo, int *ro) {
    static const int kc[6] = {1, 2, 2, 3, 1, 2};
    int k = kc[rnd_int(6)];
    int base = best_n > FLOORN ? best_n : FLOORN;
    int lo = best_n / (2 * k) + 1;
    int hi = base / (2 * k) + 1;
    if (hi < lo) hi = lo;
    int g;
    if (rnd_int(2) == 0) g = hi + rnd_int(hi / 10 + 3);
    else g = lo + rnd_int(hi - lo + 3);
    if (g < 2) g = 2;

    int opts[16], no = 0;
    for (int c = 1; c <= 12; c++)
        if (g % c == 0 && g / c >= 2) opts[no++] = c;
    int c2 = opts[rnd_int(no)];
    int m = g / c2, r = 1;
    if (c2 > 1) {
        int found = 0;
        for (int tr = 0; tr < 300 && !found; tr++) {
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
    *ko = k; *c2o = c2; *mo = m; *ro = r;
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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n] [floor_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    FLOORN = argc > 6 ? atoi(argv[6]) : best_n;
    best_m = 0;
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE - 0.3) {
        int k, c2, m, r;
        pick_group(&k, &c2, &m, &r);
        setup_group(k, c2, m, r);
        random_init();
        double gend = elapsed() + GROUP_SECS;
        if (gend > DEADLINE) gend = DEADLINE;
        long long bc = tabu_group(gend);
        if (bc == 0 && N > best_n) emit();
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
# Safe baseline families (always validated before use).
# ----------------------------------------------------------------------------

# Known record orders used only as a search floor for the C engine; the engine
# still emits any valid improvement over the baseline, so this cannot lower the score.
KNOWN_FLOOR = {(6, 5): 684}


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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q <= 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then one C tabu run over voltage lifts.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.88 * time_limit - (time.monotonic() - start) - 3.0
    if remaining >= 2.0:
        floor_n = max(best_n, KNOWN_FLOOR.get((d, D), 0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n, floor_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
