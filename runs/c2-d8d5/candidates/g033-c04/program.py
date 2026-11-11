import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New in this version: a C-native voltage-lift annealer over semidirect
# products Z_m x| Z_k2 (C_LIFT). The base graph has k blocks per side, each of
# d darts (layer l, block i) joins A-block i to B-block lay[l][i] with voltage
# S[l][i]. Vertex transitivity under left multiplication lets the cost count
# only (representative, vertex) pairs at distance > D, using 2k-bit reach masks.
# Duplicate darts are penalised. The whole inner loop runs in C, so it is far
# faster than the old Python annealer. Python picks (k, group order) targets
# adaptively, and C_GROW then grows the best valid graph by edge toggles.
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

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define PEN 1000LL

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, M_, K2_, R_, G_, N_;
static int *mulT, *invT, *lay, *Sv, *nbr;
static u64 *curR, *propR, *sA, *sB;

static int setup_group(void) {
    long long p = 1 % M_;
    int *pw = malloc(sizeof(int) * (size_t)K2_);
    if (!pw) return 0;
    for (int b = 0; b < K2_; b++) { pw[b] = (int)p; p = (p * R_) % M_; }
    int ok = (p == 1 % M_);
    int ga = R_, gb = M_;
    while (gb) { int t = ga % gb; ga = gb; gb = t; }
    if (ga != 1) ok = 0;
    if (!ok) { free(pw); return 0; }
    G_ = M_ * K2_;
    int G = G_;
    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    invT = malloc(sizeof(int) * (size_t)G);
    if (!mulT || !invT) { free(pw); return 0; }
    for (int x = 0; x < G; x++) {
        int a = x / K2_, b = x % K2_;
        for (int y = 0; y < G; y++) {
            int c = y / K2_, e = y % K2_;
            long long f = ((long long)a + (long long)pw[b] * c) % M_;
            mulT[(size_t)x * G + y] = (int)f * K2_ + (b + e) % K2_;
        }
    }
    free(pw);
    for (int x = 0; x < G; x++) {
        int found = -1;
        for (int y = 0; y < G; y++) if (mulT[(size_t)x * G + y] == 0) { found = y; break; }
        if (found < 0) return 0;
        invT[x] = found;
    }
    return 1;
}

/* Vertex id: block*G + g. A-blocks 0..K-1, B-blocks K..2K-1.
   Dart (l,i) with j = lay[l][i], s = Sv[l][i] joins A(i,g) to B(j, g*s). */
static void build_nbr(void) {
    int K = K_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = lay[l * K + i];
            int s = Sv[l * K + i];
            int is = invT[s];
            for (int g = 0; g < G; g++) {
                nbr[(size_t)(i * G + g) * d + l] = (K + j) * G + mulT[(size_t)g * G + s];
                nbr[(size_t)((K + j) * G + g) * d + l] = i * G + mulT[(size_t)g * G + is];
            }
        }
}

/* Reach from representatives (block b, identity element) to all vertices in D steps.
   Returns the number of (representative, vertex) pairs at distance > D. */
static long long eval_un(u64 *res) {
    int N = N_, d = d_, K = K_, G = G_, D = D_;
    u64 *x = sA, *y = sB;
    memset(x, 0, sizeof(u64) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) x[(size_t)b * G] = 1ULL << b;
    for (int it = 0; it < D; it++) {
        for (int v = 0; v < N; v++) {
            u64 t = x[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) t |= x[nb[l]];
            y[v] = t;
        }
        u64 *tp = x; x = y; y = tp;
    }
    long long s = 0;
    for (int v = 0; v < N; v++) {
        s += __builtin_popcountll(x[v]);
        res[v] = x[v];
    }
    return (long long)2 * K * N - s;
}

static long long dup_count(void) {
    long long c = 0;
    int K = K_, d = d_;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && Sv[l1 * K + i] == Sv[l2 * K + i]) c++;
    return c;
}

static long long cost_of(u64 *res) {
    build_nbr();
    long long un = eval_un(res);
    return un + PEN * dup_count();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 10; w++) rnd();
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    R_ = atoi(argv[8]);
    if (d_ < 2 || D_ < 1 || K_ < 1 || K_ > 32 || M_ < 1 || K2_ < 1 || limit <= 0) {
        printf("0 0\n");
        return 0;
    }
    if ((long long)M_ * K2_ < 2 || (long long)M_ * K2_ > 2500) {
        printf("0 0\n");
        return 0;
    }
    R_ = ((R_ % M_) + M_) % M_;
    if (!setup_group()) { printf("0 0\n"); return 0; }

    int K = K_, d = d_, G = G_;
    N_ = 2 * K * G;
    int N = N_;
    lay = malloc(sizeof(int) * (size_t)(d * K));
    Sv = malloc(sizeof(int) * (size_t)(d * K));
    nbr = malloc(sizeof(int) * (size_t)N * (size_t)d);
    curR = malloc(sizeof(u64) * (size_t)N);
    propR = malloc(sizeof(u64) * (size_t)N);
    sA = malloc(sizeof(u64) * (size_t)N);
    sB = malloc(sizeof(u64) * (size_t)N);
    if (!lay || !Sv || !nbr || !curR || !propR || !sA || !sB) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d; l++) {
        int *p = lay + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
    }
    for (int t = 0; t < d * K; t++) Sv[t] = rint_(G);

    long long cost = cost_of(curR);
    u64 full = (2 * K >= 64) ? ~0ULL : ((1ULL << (2 * K)) - 1ULL);
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = 20.0 * pow(0.3 / 20.0, el / limit);
        int type = 0, l = 0, i = 0, i2 = 0, oldv = 0;
        if (K >= 2 && rdbl() < 0.2) {
            type = 1;
            l = rint_(d);
            i = rint_(K);
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int *p = lay + l * K;
            int t = p[i]; p[i] = p[i2]; p[i2] = t;
        } else {
            type = 0;
            int found = 0;
            if (rdbl() < 0.5) {
                for (int t = 0; t < 30 && !found; t++) {
                    int u = rint_(N);
                    if (curR[u] == full) continue;
                    int c = u / G;
                    if (c < K) {
                        i = c; l = rint_(d); found = 1;
                    } else {
                        int j = c - K;
                        l = rint_(d);
                        for (int ii = 0; ii < K; ii++)
                            if (lay[l * K + ii] == j) { i = ii; found = 1; break; }
                    }
                }
            }
            if (!found) { l = rint_(d); i = rint_(K); }
            int idx = l * K + i;
            oldv = Sv[idx];
            int nv = rint_(G);
            if (nv == oldv) nv = (oldv + 1) % G;
            Sv[idx] = nv;
        }
        long long nc = cost_of(propR);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            u64 *tp = curR; curR = propR; propR = tp;
        } else {
            if (type == 1) {
                int *p = lay + l * K;
                int t = p[i]; p[i] = p[i2]; p[i2] = t;
            } else {
                Sv[l * K + i] = oldv;
            }
            build_nbr();
        }
    }

    if (cost == 0) {
        int A = K * G;
        printf("%d %d\n", N, A * d);
        for (int v = 0; v < A; v++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", v, nbr[(size_t)v * d + l]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""

_KS = (1, 2, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cand = edges + [(v, n) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C edge-toggle grower from a valid graph; returns parsed output."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 == G, m >= 2, r^k2 = 1 mod m, gcd(r, m) = 1, or None."""
    divs = [k2 for k2 in range(1, min(G, 40) + 1) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1 or rng.random() < 0.3:
        return m, k2, 1
    cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return m, k2, 1
    return m, k2, rng.choice(cands)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)
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

    # Exact constructions for D >= 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # calibration case: exact record, return at once
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Phase 0 (D = 3 only): use spare degree of the PG-based start.
    if D == 3:
        slack_end = t0 + max(0.5, min(0.08 * T, T - 15.0))
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 1: C-native voltage-lift search with adaptive targets.
    if D >= 3 and d >= 2:
        lift_end = t0 + max(1.0, min(0.68 * T, T - 14.0))
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}
        step = 0.05

        while True:
            remaining = lift_end - time.monotonic()
            if remaining < 1.0:
                break
            if rng.random() < 0.2:
                k = rng.choice(_KS)
            else:
                k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())
            G_min = best[0] // (2 * k) + 1
            G = G_min + rng.randrange(0, max(1, int(G_min * step)) + 1)
            G = max(G, 2)
            if G > 2500:
                break
            grp = _sample_group(G, rng)
            if grp is None:
                continue
            m, k2, r = grp
            secs = min(remaining, max(1.5, min(6.0, 0.3 * remaining)))
            trials[k] += 1
            try:
                out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{secs:.2f}",
                                         k, m, k2, r], timeout=secs + 15.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                break
            if n > best[0] and lib.is_valid(n, e, d, D):
                wins[k] += 1
                best = (n, e)
                step = min(0.08, step * 1.1)
            else:
                step = max(0.005, step * 0.85)

    # Phase 2: C edge-toggle grower extends the best valid graph.
    c_budget = T - (time.monotonic() - t0) - 5.0
    if c_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
