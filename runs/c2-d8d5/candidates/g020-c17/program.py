import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine A: voltage-lift annealer over an explicit finite group.
#
# Input (graph text format, so lib.run_c can pass it): "G*G G*G" then the
# multiplication table as pairs (x*G+y, x*y). Args: d D seed seconds K G.
# The base graph has K vertices on each side. Layer l joins A-block i to
# B-block lay[l][i] with voltage S[l][i], so every vertex has degree d. Left
# multiplication by G is an automorphism, so distances are checked only from
# the 2K block representatives. Cost = unreached pairs + 1000 * duplicate darts.
# Output "K G" then d*K pairs "j s" (j = lay, s = voltage), or "0 0".
# ----------------------------------------------------------------------------

VOLT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int ri(int n) { return (int)(rnd() % (uint64_t)n); }
static double rd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, G_, N_;
static int *mul_, *inv_, *lay_, *S_, *ilay_, *nb_, *dist_, *que_;

static void build_nb(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++)
            ilay_[l * K_ + lay_[l * K_ + i]] = i;
    for (int i = 0; i < K_; i++)
        for (int g = 0; g < G_; g++) {
            int v = i * G_ + g;
            for (int l = 0; l < d_; l++) {
                int j = lay_[l * K_ + i];
                nb_[v * d_ + l] = (K_ + j) * G_ + mul_[g * G_ + S_[l * K_ + i]];
            }
        }
    for (int j = 0; j < K_; j++)
        for (int h = 0; h < G_; h++) {
            int v = (K_ + j) * G_ + h;
            for (int l = 0; l < d_; l++) {
                int i = ilay_[l * K_ + j];
                int s = S_[l * K_ + i];
                nb_[v * d_ + l] = i * G_ + mul_[h * G_ + inv_[s]];
            }
        }
}

static long long eval_bad(void) {
    build_nb();
    long long tot = 0;
    for (int s = 0; s < 2 * K_; s++) {
        int src = s * G_;
        for (int v = 0; v < N_; v++) dist_[v] = -1;
        int h = 0, t = 0, cnt = 1;
        que_[t++] = src;
        dist_[src] = 0;
        while (h < t) {
            int v = que_[h++];
            if (dist_[v] >= D_) continue;
            for (int l = 0; l < d_; l++) {
                int u = nb_[v * d_ + l];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    que_[t++] = u;
                    cnt++;
                }
            }
        }
        tot += N_ - cnt;
    }
    return tot;
}

static long long dups(void) {
    long long c = 0;
    for (int i = 0; i < K_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (lay_[l1 * K_ + i] == lay_[l2 * K_ + i] && S_[l1 * K_ + i] == S_[l2 * K_ + i])
                    c++;
    return c;
}

static long long cost_now(void) { return eval_bad() + 1000LL * dups(); }

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    K_ = atoi(argv[5]);
    G_ = atoi(argv[6]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (d_ < 1 || D_ < 1 || K_ < 1 || G_ < 1 || (long long)G_ * G_ != n0 || m0 != n0) {
        printf("0 0\n");
        return 0;
    }
    int GG = G_ * G_;
    mul_ = malloc(sizeof(int) * (size_t)GG);
    inv_ = malloc(sizeof(int) * (size_t)G_);
    for (int t = 0; t < GG; t++) mul_[t] = -1;
    for (int t = 0; t < m0; t++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u >= 0 && u < GG && v >= 0 && v < G_) mul_[u] = v;
    }
    int bad = 0;
    for (int t = 0; t < GG; t++) if (mul_[t] < 0) bad = 1;
    for (int y = 0; y < G_ && !bad; y++)
        if (mul_[y] != y || mul_[y * G_] != y) bad = 1;
    for (int x = 0; x < G_ && !bad; x++) {
        int f = -1;
        for (int y = 0; y < G_; y++) if (mul_[x * G_ + y] == 0) { f = y; break; }
        if (f < 0) bad = 1; else inv_[x] = f;
    }
    if (bad) { printf("0 0\n"); return 0; }

    N_ = 2 * K_ * G_;
    lay_ = malloc(sizeof(int) * (size_t)d_ * K_);
    S_ = malloc(sizeof(int) * (size_t)d_ * K_);
    ilay_ = malloc(sizeof(int) * (size_t)d_ * K_);
    int *bl = malloc(sizeof(int) * (size_t)d_ * K_);
    int *bS = malloc(sizeof(int) * (size_t)d_ * K_);
    nb_ = malloc(sizeof(int) * (size_t)N_ * d_);
    dist_ = malloc(sizeof(int) * (size_t)N_);
    que_ = malloc(sizeof(int) * (size_t)N_);
    int *perm = malloc(sizeof(int) * (size_t)K_);
    if (!lay_ || !S_ || !ilay_ || !bl || !bS || !nb_ || !dist_ || !que_ || !perm) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) perm[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = ri(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K_; i++) {
            lay_[l * K_ + i] = perm[i];
            S_[l * K_ + i] = ri(G_);
        }
    }

    long long cur = cost_now();
    long long best = cur;
    memcpy(bl, lay_, sizeof(int) * (size_t)d_ * K_);
    memcpy(bS, S_, sizeof(int) * (size_t)d_ * K_);

    const double T0 = 3.0, T1 = 0.05;
    clock_t c0 = clock();
    while (best > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        double T = T0 * pow(T1 / T0, el / tl);

        if (K_ >= 2 && rd() < 0.2) {
            int l = ri(d_), i1 = ri(K_), i2 = ri(K_);
            if (i1 == i2) continue;
            int a = l * K_ + i1, b = l * K_ + i2;
            int t = lay_[a]; lay_[a] = lay_[b]; lay_[b] = t;
            long long nc = cost_now();
            if (nc <= cur || rd() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                t = lay_[a]; lay_[a] = lay_[b]; lay_[b] = t;
            }
        } else {
            int idx = ri(d_ * K_);
            int old = S_[idx];
            int nw = ri(G_);
            if (nw == old) continue;
            S_[idx] = nw;
            long long nc = cost_now();
            if (nc <= cur || rd() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S_[idx] = old;
            }
        }
        if (cur < best) {
            best = cur;
            memcpy(bl, lay_, sizeof(int) * (size_t)d_ * K_);
            memcpy(bS, S_, sizeof(int) * (size_t)d_ * K_);
        }
    }

    if (best != 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", K_, G_);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) printf("%d %d ", bl[l * K_ + i], bS[l * K_ + i]);
        printf("\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine B: bipartite edge-toggle annealer with vertex growth (from parent).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
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
    """Run the C edge annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k2, searched in C.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) with G = m*k2 >= target for Z_m x| Z_k2, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(1, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _group_tables(m, k2, r):
    """Return (G, M) with M[x, y] = x*y for Z_m x| Z_k2, element a*k2 + b (identity 0)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return G, M


def _voltage_try(d, D, K, m, k2, r, seed, seconds):
    """Run the C voltage annealer for one group. Returns (n, edges) or None."""
    G, M = _group_tables(m, k2, r)
    pairs = [(x, v) for x, v in enumerate(M.ravel().tolist())]
    out = lib.run_c(VOLT_SOURCE, [d, D, seed, f"{seconds:.2f}", K, G],
                    stdin_graph=(G * G, pairs), timeout=seconds + 15.0)
    nums = out.split()
    if len(nums) < 2 or nums[0] == "0":
        return None
    Kc, Gc = int(nums[0]), int(nums[1])
    vals = [int(x) for x in nums[2:]]
    if Kc != K or Gc != G or len(vals) != 2 * d * K:
        return None
    edges = set()
    p = 0
    for _l in range(d):
        for i in range(K):
            j, s = vals[p], vals[p + 1]
            p += 2
            for g in range(G):
                edges.add((i * G + g, (K + j) * G + int(M[g, s])))
    return 2 * K * G, sorted(edges)


def _voltage_phase(d, D, best, rng, deadline):
    """Climb the ladder of voltage lifts; returns the best valid (n, edges) found."""
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        K = rng.choice([2, 2, 3, 3, 4, 4, 5, 6])
        base = best[0] // (2 * K)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 25 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * K * G <= best[0]:
            continue
        budget = min(3.0, remaining)
        try:
            res = _voltage_try(d, D, K, m, k2, r, rng.randrange(1, 1 << 30), budget)
        except Exception:
            break  # compile or runtime failure: keep the valid fallback
        if res is not None:
            n, e = res
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    return best


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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: voltage-lift ladder over non-cyclic groups, searched in C.
    v_end = t0 + max(1.0, min(0.5 * time_limit, time_limit - 14.0))
    best = _voltage_phase(d, D, best, rng, v_end)

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + max(1.0, min(0.62 * time_limit, time_limit - 10.0))
    if time.monotonic() < slack_end:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3: C edge annealer grows the best valid graph by vertex pairs.
    c_budget = time_limit - (time.monotonic() - t0) - 4.0
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
