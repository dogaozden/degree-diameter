import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (grow): full-graph bipartite edge-toggle annealer with vertex
# growth, inherited from the parent. Starts from a valid graph on stdin, keeps
# the best valid graph seen, and adds vertex pairs whenever the cost reaches 0.
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
# C engine 2 (NEW): orbit-reduced voltage-lift annealer.
#
# Group G = Z_M x| Z_K2 (element a*K2+b, multiplication (a,b)(c,e) =
# (a + r^b c, b+e)). Base graph: K blocks on side A and K blocks on side B,
# every block a copy of G, Dg layers. Layer l joins A-block i to B-block
# lay[l][i] (lay[l] is a permutation) through the dart x -> x * vol[l][i].
# The lift is bipartite, Dg-regular, and invariant under LEFT translation
# by G.
#
# Key fact used here: ball((i,h)) = h * ball((i,e)), so the lift has
# diameter <= D iff the ball of the identity of each of the 2K blocks covers
# all vertices. A move therefore costs 2K BFS runs, not a full bitset
# closure over all N vertices. Duplicate darts (same i, j, vol) are penalised
# so the output is always a simple graph.
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

static int Dg, DD, K, M, K2, G, N;
static int *rp, *invv, *lay, *lay0, *vol, *vol0, *inl, *nb, *dist, *qu;

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)rp[b] * c) % M;
    int b2 = (b + e) % K2;
    return (int)t * K2 + b2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nbb = (K2 - b) % K2;
    long long t = ((long long)a * rp[nbb]) % M;
    int c = (int)((M - t) % M);
    return c * K2 + nbb;
}

static long long dup_count(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dg; l1++)
            for (int l2 = l1 + 1; l2 < Dg; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i]) c++;
    return c;
}

static void build_adj(void) {
    for (int l = 0; l < Dg; l++)
        for (int i = 0; i < K; i++)
            inl[l * K + lay[l * K + i]] = i;
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < Dg; l++) {
                int idx = l * K + i;
                nb[v * Dg + l] = (K + lay[idx]) * G + gmul(x, vol[idx]);
            }
        }
    for (int j = 0; j < K; j++)
        for (int y = 0; y < G; y++) {
            int v = (K + j) * G + y;
            for (int l = 0; l < Dg; l++) {
                int i = inl[l * K + j];
                int idx = l * K + i;
                nb[v * Dg + l] = i * G + gmul(y, invv[vol[idx]]);
            }
        }
}

/* Sum over the 2K block identities of the number of vertices at distance > DD,
   plus a large penalty per duplicate dart. Zero means the lift is valid. */
static long long eval_cost(void) {
    long long dup = dup_count();
    build_adj();
    long long tot = 0;
    for (int b = 0; b < 2 * K; b++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0, src = b * G;
        dist[src] = 0;
        qu[t++] = src;
        while (h < t) {
            int v = qu[h++];
            if (dist[v] >= DD) continue;
            for (int l = 0; l < Dg; l++) {
                int u = nb[v * Dg + l];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
            }
        }
        tot += N - t;
    }
    return tot + (long long)(2 * N) * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    long long rr = atoll(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    Dg = d;
    if (d < 1 || DD < 1 || K < 1 || M < 2 || K2 < 1) { printf("0 0\n"); return 0; }
    G = M * K2;
    N = 2 * K * G;
    if (N > 20000 || Dg > 64) { printf("0 0\n"); return 0; }
    rr %= M;
    if (rr < 0) rr += M;

    rp = malloc(sizeof(int) * K2);
    rp[0] = 1 % M;
    for (int t = 1; t < K2; t++) rp[t] = (int)((long long)rp[t - 1] * rr % M);
    if (((long long)rp[K2 - 1] * rr) % M != 1 % M) { printf("0 0\n"); return 0; }

    invv = malloc(sizeof(int) * G);
    for (int s = 0; s < G; s++) invv[s] = ginv(s);
    lay = malloc(sizeof(int) * Dg * K);
    lay0 = malloc(sizeof(int) * Dg * K);
    vol = malloc(sizeof(int) * Dg * K);
    vol0 = malloc(sizeof(int) * Dg * K);
    inl = malloc(sizeof(int) * Dg * K);
    nb = malloc(sizeof(int) * (size_t)N * Dg);
    dist = malloc(sizeof(int) * N);
    qu = malloc(sizeof(int) * N);
    if (!rp || !invv || !lay || !lay0 || !vol || !vol0 || !inl || !nb || !dist || !qu) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < Dg; l++) {
        for (int i = 0; i < K; i++) lay[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = lay[l * K + i];
            lay[l * K + i] = lay[l * K + j];
            lay[l * K + j] = tmp;
        }
    }
    for (int idx = 0; idx < Dg * K; idx++) vol[idx] = rint_(G);

    long long cost = eval_cost();
    long long cost0 = cost;
    double T0 = 0.05 * (double)cost0 + 1.0, T1 = 0.3;
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        memcpy(lay0, lay, sizeof(int) * Dg * K);
        memcpy(vol0, vol, sizeof(int) * Dg * K);

        int mv = rint_(3);
        if (mv == 1 && K < 2) mv = 0;
        if (mv == 2 && Dg < 2) mv = 0;
        if (mv == 0) {
            int idx = rint_(Dg * K);
            vol[idx] = rint_(G);
        } else if (mv == 1) {
            int l = rint_(Dg);
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l * K + i1];
            lay[l * K + i1] = lay[l * K + i2];
            lay[l * K + i2] = tmp;
        } else {
            int l1 = rint_(Dg), l2 = rint_(Dg - 1);
            if (l2 >= l1) l2++;
            int i = rint_(K);
            int tmp = vol[l1 * K + i];
            vol[l1 * K + i] = vol[l2 * K + i];
            vol[l2 * K + i] = tmp;
        }

        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            memcpy(lay, lay0, sizeof(int) * Dg * K);
            memcpy(vol, vol0, sizeof(int) * Dg * K);
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    /* nb was rebuilt by the eval that produced cost == 0. */
    long long m = (long long)K * G * Dg;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < Dg; l++)
            printf("%d %d\n", v, nb[v * Dg + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

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
    """Run the C edge annealer from a valid graph; returns parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _lift_in_c(k, m, k2, r, d, D, seconds, seed):
    """Run the C voltage-lift annealer over Z_m x| Z_k2 with k base blocks per side."""
    out = lib.run_c(C_LIFT, [d, D, k, m, k2, r, seed, f"{seconds:.2f}"],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


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
            return True
        return False

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: orbit-reduced voltage-lift search in C, bandit over base sizes k.
    lift_end = t0 + 0.6 * time_limit
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        trials[k] += 1
        secs = min(rng.uniform(1.5, 3.5), remaining)
        try:
            cn, ce = _lift_in_c(k, m, k2, r, d, D, secs, rng.randrange(1, 1 << 30))
        except RuntimeError:
            continue
        if cn > 0 and consider(cn, ce):
            wins[k] += 1

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + 0.65 * time_limit
    if time.monotonic() < slack_end:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3: C edge annealer grows the best valid graph by vertex pairs.
    c_budget = time_limit - (time.monotonic() - t0) - 5.0
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
