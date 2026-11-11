import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1: voltage lifts over Z_M x| Z_K2 (C simulated annealing).
#
# Base graph: K vertices on side A and K on side B. Layer l (0..d-1) is a
# permutation sig[l] of {0..K-1}, and each dart (i, sig[l][i]) carries a
# voltage g in G. The lift has vertices (block, x) with x in G, and
# A(i, x) ~ B(j, x*g) for each dart (i, j, g). Left multiplication by h is an
# automorphism, so the BFS from (b, e) for each of the 2K base blocks gives the
# whole cost. Cost = sum over blocks of unreached vertices within distance D.
# Once cost is zero, the lift is printed (duplicate edges are removed in Python).
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef unsigned long long u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K, M, K2, R, G, N, stampId;
static int *powR, *mulT, *invT, *sig, *sigInv, *volt, *voltInv, *stamp, *dist, *queue;

static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x % K2, a2 = y / K2, b2 = y % K2;
    return ((a1 + powR[b1] * a2) % M) * K2 + (b1 + b2) % K2;
}

static int bfs_visited(int src) {
    int head = 0, tail = 0;
    stampId++;
    if (stampId == 0x7ffffff0) { memset(stamp, 0, sizeof(int) * (size_t)N); stampId = 1; }
    stamp[src] = stampId; dist[src] = 0; queue[tail++] = src;
    int vis = 1;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= D_) continue;
        int blk = v / G, x = v - blk * G;
        if (blk < K) {
            for (int l = 0; l < d_; l++) {
                int idx = l * K + blk;
                int w = (K + sig[idx]) * G + mulT[x * G + volt[idx]];
                if (stamp[w] != stampId) {
                    stamp[w] = stampId; dist[w] = dv + 1; queue[tail++] = w; vis++;
                }
            }
        } else {
            int j = blk - K;
            for (int l = 0; l < d_; l++) {
                int i = sigInv[l * K + j];
                int idx = l * K + i;
                int w = i * G + mulT[x * G + voltInv[idx]];
                if (stamp[w] != stampId) {
                    stamp[w] = stampId; dist[w] = dv + 1; queue[tail++] = w; vis++;
                }
            }
        }
    }
    return vis;
}

static long long eval_all(int *blk) {
    long long tot = 0;
    for (int b = 0; b < 2 * K; b++) {
        int vis = bfs_visited(b * G);
        blk[b] = N - vis;
        tot += N - vis;
    }
    return tot;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K = atoi(argv[5]); M = atoi(argv[6]); K2 = atoi(argv[7]); R = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K < 1 || K > 64 || M < 1 || K2 < 1 || R < 0) { printf("0 0\n"); return 0; }
    G = M * K2;
    if (G < 2 || G > 3000) { printf("0 0\n"); return 0; }
    N = 2 * K * G;

    powR = malloc(sizeof(int) * (size_t)K2);
    powR[0] = 1 % M;
    for (int b = 1; b < K2; b++) powR[b] = (int)((long long)powR[b - 1] * R % M);
    if (((long long)powR[K2 - 1] * R) % M != 1 % M) { printf("0 0\n"); return 0; }

    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    invT = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        invT[x] = 0;
        for (int y = 0; y < G; y++)
            if (mulT[x * G + y] == 0) { invT[x] = y; break; }
    }

    sig = malloc(sizeof(int) * (size_t)d_ * K);
    sigInv = malloc(sizeof(int) * (size_t)d_ * K);
    volt = malloc(sizeof(int) * (size_t)d_ * K);
    voltInv = malloc(sizeof(int) * (size_t)d_ * K);
    stamp = calloc((size_t)N, sizeof(int));
    dist = malloc(sizeof(int) * (size_t)N);
    queue = malloc(sizeof(int) * (size_t)N);
    int *curB = malloc(sizeof(int) * (size_t)2 * K);
    int *newB = malloc(sizeof(int) * (size_t)2 * K);
    int *perm = malloc(sizeof(int) * (size_t)K);
    if (!powR || !mulT || !invT || !sig || !sigInv || !volt || !voltInv || !stamp || !dist || !queue || !curB || !newB || !perm) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sig[l * K + i] = perm[i];
            sigInv[l * K + perm[i]] = i;
        }
    }
    for (int idx = 0; idx < d_ * K; idx++) {
        volt[idx] = rint_(G);
        voltInv[idx] = invT[volt[idx]];
    }

    long long cost = eval_all(curB);
    const double T0 = 6.0, T1 = 0.15;
    clock_t c0 = clock();
    while (cost != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (rdbl() < 0.25) {
            if (K < 2) continue;
            int l = rint_(d_);
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int *s = sig + l * K;
            int t = s[i1]; s[i1] = s[i2]; s[i2] = t;
            sigInv[l * K + s[i1]] = i1;
            sigInv[l * K + s[i2]] = i2;
            long long nc = eval_all(newB);
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                memcpy(curB, newB, sizeof(int) * (size_t)2 * K);
            } else {
                t = s[i1]; s[i1] = s[i2]; s[i2] = t;
                sigInv[l * K + s[i1]] = i1;
                sigInv[l * K + s[i2]] = i2;
            }
        } else {
            int b = -1;
            if (rdbl() < 0.7) {
                for (int t = 0; t < 8; t++) {
                    int c = rint_(2 * K);
                    if (curB[c] > 0) { b = c; break; }
                }
            }
            if (b < 0) b = rint_(2 * K);
            int l = rint_(d_);
            int i = (b < K) ? b : sigInv[l * K + (b - K)];
            int idx = l * K + i;
            int old = volt[idx];
            int nv = rint_(G);
            if (nv == old) continue;
            volt[idx] = nv;
            voltInv[idx] = invT[nv];
            long long nc = eval_all(newB);
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                memcpy(curB, newB, sizeof(int) * (size_t)2 * K);
            } else {
                volt[idx] = old;
                voltInv[idx] = invT[old];
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    long long m = (long long)K * d_ * G;
    printf("%d %lld\n", N, m);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) {
            int idx = l * K + i;
            int tgt = K + sig[idx];
            for (int x = 0; x < G; x++) {
                printf("%d %d\n", i * G + x, tgt * G + mulT[x * G + volt[idx]]);
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine 2: bipartite edge-toggle annealer with vertex growth (grows a valid
# graph by vertex pairs while keeping every vertex within distance D).
# ----------------------------------------------------------------------------

GROW_C = r"""
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


def _group_of_order(G, rng):
    """Return (M, K2, R) with M * K2 = G and Z_M x| Z_K2 a valid semidirect product, or None."""
    options = [k2 for k2 in range(1, min(G, 40) + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(options)
    for k2 in options:
        M = G // k2
        if k2 == 1:
            return M, 1, 1
        cands = [1]
        if M > 2:
            cands += [rng.randrange(2, M) for _ in range(40)]
        for r in cands:
            if math.gcd(r, M) == 1 and pow(r, k2, M) == 1 % M:
                return M, k2, r
    return None


def _run_lift(d, D, seed, seconds, K, M, K2, R):
    """Run the C lift annealer; returns (n, edges) or (0, []) if nothing valid was found."""
    out = lib.run_c(LIFT_C, [d, D, seed, f"{seconds:.2f}", K, M, K2, R],
                    stdin_graph=None, timeout=seconds + 5.0)
    nums = out.split()
    n, m = int(nums[0]), int(nums[1])
    if n <= 0 or m <= 0:
        return 0, []
    edges = set()
    for i in range(m):
        u = int(nums[2 + 2 * i])
        v = int(nums[3 + 2 * i])
        edges.add((u, v) if u < v else (v, u))
    return n, sorted(edges)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C growth annealer from a valid graph; returns parsed output (may be (0, []))."""
    out = lib.run_c(GROW_C, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: voltage lifts over small semidirect groups, aimed just above the current best.
    lift_end = t0 + 0.6 * time_limit
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 2.0:
            break
        Kc = [k for k in (1, 2, 3, 4, 6) if best[0] // (2 * k) + 1 <= 3000]
        if not Kc:
            break
        K = rng.choice(Kc)
        Gmin = best[0] // (2 * K) + 1
        G = Gmin + rng.randrange(0, max(2, Gmin // 25))
        if G < 2 or G > 3000:
            continue
        grp = _group_of_order(G, rng)
        if grp is None:
            continue
        M, K2, R = grp
        budget = min(remaining, rng.uniform(4.0, 10.0))
        try:
            n, e = _run_lift(d, D, rng.randrange(1, 1 << 30), budget, K, M, K2, R)
        except Exception:
            continue
        consider(n, e)

    # Stage 2: C annealer grows the best valid graph by vertex pairs.
    grow_end = t0 + time_limit - 6.0
    budget = grow_end - time.monotonic()
    if budget >= 1.5:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
