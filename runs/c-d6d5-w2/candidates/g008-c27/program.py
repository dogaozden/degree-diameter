import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu search over voltage lifts of semidirect products Z_m x| Z_k2.
#
# Base graph: K A-vertices and K B-vertices, DEG layers. Layer l is a
# permutation sigma_l of {0..K-1} (dart (i, sigma_l(i)) for each i) plus one
# voltage s per dart. Vertices A_i,g = i*G + g and B_j,h = (K+j)*G + h, and
# dart (i, j, s) joins A_i,g to B_j,g*s for every g. Left multiplication is an
# automorphism, so diameter <= D iff a BFS of depth D from each of the 2K block
# representatives covers every vertex.
#
# Search: a tabu search, not annealing. At each step NCAND random moves are
# sampled (voltage change, or swap of two targets within one layer). The best
# non-tabu move is applied even if it worsens the cost, and the reverse move is
# tabu for a short tenure. Aspiration allows a tabu move that beats the run's
# best. After NOIMP steps without improvement, a new random group and lift are
# drawn. Cost = total uncovered ordered pairs. Cost 0 is a valid graph, and it
# is emitted if it beats the current best order.
#
# Timing uses wall-clock time from program start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define NCAND 14
#define TTENURE 7
#define NOIMP 2500
#define TABUSZ 8192

static uint64_t rs0, rs1;
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, K, K2, M, G, T, R, N;
static int *Rpow, *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static long long *unc;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static long long tabu[TABUSZ];
static long long step_no = 0;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t nextr(void) {
    uint64_t s1 = rs0;
    const uint64_t s0 = rs1;
    rs0 = s0;
    s1 ^= s1 << 23;
    rs1 = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs1 + s0;
}

static int rint_(int n) { return (int)(nextr() % (uint64_t)n); }
static double runit(void) { return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0); }

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

/* (a,b)*(c,e) = (a + r^b c, b + e), index a*K2 + b. */
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

static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = N;
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
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = r * G;
        stamp[r * G] = curstamp;
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
        total += N - count;
    }
    return total;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    T = DEG * K;
    N = 2 * K * G;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_group(void) {
    free(Rpow); free(dI); free(dJ); free(dS); free(perm);
    free(adj); free(cnt); free(stamp); free(fr); free(nx); free(unc);
}

static void random_init(void) {
    int p[64];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rint_(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = m;
    best_n = N;
}

static void apply_swap(int t1, int t2) {
    int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
}

static void set_volt(int t, int s) {
    dS[t] = s;
    build_perm(t);
}

/* Tabu search on one lift. Stops at cost 0 (emits if larger) or on stagnation. */
static void run_search(void) {
    long long cur = eval_cost();
    long long run_best = cur;
    int since = 0;
    while (cur > 0 && since < NOIMP) {
        if (elapsed() > DEADLINE) break;
        step_no++;
        long long bv = 4 * BIGC;
        int btype = -1, b1 = 0, b2 = 0, bkey = 0;
        for (int c = 0; c < NCAND; c++) {
            int type, a1, a2, key;
            long long v;
            if (K > 1 && runit() < 0.4) {
                int l = rint_(DEG), i1 = rint_(K), i2 = rint_(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                key = 256 + l * 64 + (i1 < i2 ? i1 * 8 + i2 : i2 * 8 + i1);
                apply_swap(t1, t2);
                v = eval_cost();
                apply_swap(t1, t2);
                type = 1; a1 = t1; a2 = t2;
            } else {
                int t = rint_(T), ns = rint_(G);
                if (ns == dS[t]) continue;
                int old = dS[t];
                set_volt(t, ns);
                v = eval_cost();
                set_volt(t, old);
                type = 0; a1 = t; a2 = ns; key = t % 256;
            }
            int is_tabu = tabu[key] > step_no;
            if (is_tabu && v >= run_best) continue;
            if (v < bv) {
                bv = v; btype = type; b1 = a1; b2 = a2; bkey = key;
            }
        }
        if (btype < 0) { since++; continue; }
        if (btype == 1) apply_swap(b1, b2);
        else set_volt(b1, b2);
        cur = bv;
        tabu[bkey] = step_no + TTENURE + rint_(4);
        if (cur < run_best) {
            run_best = cur;
            since = 0;
        } else {
            since++;
        }
        if (cur == 0) {
            if (N > best_n) emit();
            break;
        }
    }
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 777ULL;
    rs0 = splitmix(&sm);
    rs1 = splitmix(&sm);

    static const int kc[6] = {1, 2, 2, 3, 4, 6};
    while (elapsed() < DEADLINE) {
        int k = kc[rint_(6)];
        int gmin = best_n / (2 * k) + 1;
        int g = gmin + rint_(gmin / 6 + 3);
        if (g < 2) g = 2;
        int opts[24], no = 0;
        for (int c = 1; c <= 12 && c <= g; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rint_(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found && m >= 2; tr++) {
                int cand = 1 + rint_(m - 1);
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
        setup_group(k, c2, m, r);
        random_init();
        run_search();
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
# Driver: baselines in Python, then the C tabu search on lifts.
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

    # Nearly all of the budget goes to the C search. The reserve covers the
    # one-off compile, parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
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
