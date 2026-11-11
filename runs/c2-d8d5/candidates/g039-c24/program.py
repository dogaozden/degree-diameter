import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage lifts over semidirect products Z_m x| Z_k2.
#
# A lift has 2k base blocks (k left, k right) of G = m*k2 vertices each, and
# d layers. Layer l has a permutation LAY[l] pairing left block i with right
# block LAY[l][i] and a voltage SV[l][i] in the group. Edges are
# (i,g)-(j, g*s). Left translation is an automorphism, so the lift has
# diameter <= D exactly when every seed (i,1) reaches all vertices within D
# steps. The cost is the total count of unreached vertices over the 2k seeds,
# plus a penalty for parallel darts. Annealing runs over voltages and layer
# permutations, and the best lift larger than the input order is printed.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define MAXK 6
#define MAXDEG 16
#define MAXG 8192
#define MAXN (2 * MAXK * MAXG)
#define PEN 1000LL

static int DEG, DIA, K, GG, M_, K2, RR;
static int pw[32];
static int Aa[MAXG], Bb[MAXG], sinvT[MAXG];
static int LAY[MAXDEG][MAXK];
static int SV[MAXDEG][MAXK];
static int nb[MAXDEG][MAXN];
static int stamp[MAXN], lev[MAXN], qb[MAXN];
static int epoch = 0;
static int bestN = 0, outM = 0, found = 0;
static int *outU, *outV;
static clock_t deadline_clk;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void setup_group(int m, int k2, int r) {
    M_ = m; K2 = k2; RR = r; GG = m * k2;
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < GG; x++) { Aa[x] = x / k2; Bb[x] = x % k2; }
    for (int x = 0; x < GG; x++) {
        int a = Aa[x], b = Bb[x];
        int nbb = (k2 - b) % k2;
        int ia = (m - (int)((long long)pw[nbb] * a % m)) % m;
        sinvT[x] = ia * k2 + nbb;
    }
}

static inline int gmul(int x, int y) {
    int a = Aa[x], b = Bb[x], c = Aa[y], d2 = Bb[y];
    int aa = (a + (int)((long long)pw[b] * c % M_)) % M_;
    int bb = (b + d2) % K2;
    return aa * K2 + bb;
}

/* Rebuild neighbour lists of layer l from LAY and SV. */
static void build_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = LAY[l][i], s = SV[l][i], si = sinvT[s];
        for (int g = 0; g < GG; g++)
            nb[l][i * GG + g] = (K + j) * GG + gmul(g, s);
        for (int h = 0; h < GG; h++)
            nb[l][(K + j) * GG + h] = i * GG + gmul(h, si);
    }
}

static long long count_dups(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DEG; l1++)
            for (int l2 = l1 + 1; l2 < DEG; l2++)
                if (LAY[l1][i] == LAY[l2][i] && SV[l1][i] == SV[l2][i]) c++;
    return c;
}

/* Sum over the 2K seeds (identity of each block) of vertices not within DIA. */
static long long eval_cost(void) {
    long long tot = 0;
    int NN = 2 * K * GG;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * GG;
        epoch++;
        int head = 0, tail = 0;
        stamp[src] = epoch; lev[src] = 0; qb[tail++] = src;
        while (head < tail) {
            int v = qb[head++];
            if (lev[v] >= DIA) continue;
            for (int l = 0; l < DEG; l++) {
                int u = nb[l][v];
                if (stamp[u] != epoch) {
                    stamp[u] = epoch;
                    lev[u] = lev[v] + 1;
                    qb[tail++] = u;
                }
            }
        }
        tot += NN - tail;
    }
    return tot + PEN * count_dups();
}

static int anneal(int iters, int patience) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) LAY[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1), t = LAY[l][i];
            LAY[l][i] = LAY[l][j];
            LAY[l][j] = t;
        }
        for (int i = 0; i < K; i++) SV[l][i] = rint_(GG);
        build_layer(l);
    }
    long long cost = eval_cost();
    double c0 = (double)(cost > 0 ? cost : 1);
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && clock() >= deadline_clk) break;
        double frac = (double)t / (double)iters;
        double T = 0.02 * c0 * (1.0 - frac);
        if (T < 0.3) T = 0.3;
        int l = rint_(DEG);
        if (K >= 2 && rdbl() < 0.3) {
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int tmp = LAY[l][i1]; LAY[l][i1] = LAY[l][i2]; LAY[l][i2] = tmp;
            build_layer(l);
            long long nc = eval_cost();
            int acc = (nc <= cost) || (rdbl() < exp(-(double)(nc - cost) / T));
            if (acc) {
                cost = nc;
                last = t;
            } else {
                tmp = LAY[l][i1]; LAY[l][i1] = LAY[l][i2]; LAY[l][i2] = tmp;
                build_layer(l);
            }
        } else {
            int i = rint_(K);
            int old = SV[l][i];
            int nw = rint_(GG);
            if (nw == old) continue;
            SV[l][i] = nw;
            build_layer(l);
            long long nc = eval_cost();
            int acc = (nc <= cost) || (rdbl() < exp(-(double)(nc - cost) / T));
            if (acc) {
                cost = nc;
                last = t;
            } else {
                SV[l][i] = old;
                build_layer(l);
            }
        }
    }
    return cost == 0 && count_dups() == 0;
}

static void save_graph(void) {
    int m = 0;
    for (int l = 0; l < DEG; l++)
        for (int v = 0; v < K * GG; v++) {
            outU[m] = v;
            outV[m] = nb[l][v];
            m++;
        }
    outM = m;
    bestN = 2 * K * GG;
    found = 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double secs = atof(argv[4]);
    bestN = atoi(argv[5]);
    if (DEG < 1 || DEG > MAXDEG || DIA < 1) { printf("0 0\n"); return 0; }

    outU = malloc(sizeof(int) * (size_t)MAXK * MAXG * MAXDEG);
    outV = malloc(sizeof(int) * (size_t)MAXK * MAXG * MAXDEG);
    if (!outU || !outV) { printf("0 0\n"); return 0; }

    static const int K2L[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int NK2 = (int)(sizeof(K2L) / sizeof(K2L[0]));

    deadline_clk = clock() + (clock_t)(secs * CLOCKS_PER_SEC);
    while (clock() < deadline_clk) {
        int k = 1 + rint_(MAXK);
        int k2 = K2L[rint_(NK2)];
        int base = bestN / (2 * k) + 1;
        int extra = base / 25 + 1;
        int Gt = base + rint_(extra);
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        int r = 1;
        if (k2 > 1 && m >= 3) {
            for (int tries = 0; tries < 80; tries++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        K = k;
        setup_group(m, k2, r);
        if (2 * K * GG <= bestN) continue;
        if (anneal(6000, 1500)) {
            if (2 * K * GG > bestN) save_graph();
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, outM);
    for (int i = 0; i < outM; i++) printf("%d %d\n", outU[i], outV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: edge-toggle annealer with vertex growth (grows a valid graph).
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int *bvCur, *bvNew;
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

static long long bad_pairs(int *out) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        out[v] = N - pc;
        total += out[v];
    }
    return total;
}

static int pick_vertex(void) {
    if (rdbl() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rint_(N);
            if (bvCur[v] > 0) return v;
        }
    }
    return rint_(N);
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int grow_max = argc > 5 ? atoi(argv[5]) : 60;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bvCur = malloc(sizeof(int) * (size_t)cap_n);
    bvNew = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = bad_pairs(bvCur);
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_vertex(), y = pick_vertex();
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs(bvNew);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            int *tp = bvCur; bvCur = bvNew; bvNew = tp;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _run_lift(d, D, seed, seconds, n_best):
    """Run the C voltage-lift search; returns (n, edges) or (0, []) if nothing larger was found."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", n_best],
                    stdin_graph=None, timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C edge annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    def left():
        return time_limit - (time.monotonic() - t0)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: C voltage-lift search over semidirect products (new construction).
    if d >= 3 and left() > 8.0:
        lift_s = 0.7 * time_limit - (time.monotonic() - t0)
        if lift_s >= 2.0:
            try:
                n, e = _run_lift(d, D, rng.randrange(1, 1 << 30), lift_s, best[0])
                consider(n, e)
            except Exception:
                pass  # keep the valid fallback

    # Phase 2: C edge annealer grows the best valid graph by vertex pairs.
    grow_s = left() - 6.0
    if grow_s >= 1.0:
        try:
            n, e = _grow_in_c(best[0], best[1], d, D, grow_s,
                              rng.randrange(1, 1 << 30), 200)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
