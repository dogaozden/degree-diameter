import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage-lift annealer over Z_m x| Z_k2 (base graph of 2k blocks).
#
# Vertices are (block, group element). A-blocks 0..k-1 and B-blocks k..2k-1.
# Layer l maps A-block i to B-block perm[l][i] with voltage S[l][i]:
# (i, x) ~ (k + perm[l][i], x*S). Each B-block receives exactly d darts.
# The group acts by left multiplication as automorphisms, so the diameter
# condition reduces to BFS from the 2k identity vertices. The cost is the
# total number of vertices beyond distance D from those sources.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *pw, *perm, *pinv, *S, *Si, *dist, *que;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    long long t = ((long long)pw[b] * c + a) % m_;
    return (int)(t * k2_ + (b + e) % k2_);
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)pw[nb] * a) % m_;
    long long na = (m_ - t) % m_;
    return (int)(na * k2_ + nb);
}

static void set_s(int idx, int s) { S[idx] = s; Si[idx] = ginv(s); }

static int nbr(int v, int l) {
    int b = v / G_, x = v % G_;
    if (b < k_) {
        int j = perm[l * k_ + b];
        return (k_ + j) * G_ + gmul(x, S[l * k_ + b]);
    } else {
        int i = pinv[l * k_ + (b - k_)];
        return i * G_ + gmul(x, Si[l * k_ + i]);
    }
}

static int bfs_bad(int src) {
    int N = N_;
    for (int i = 0; i < N; i++) dist[i] = -1;
    int h = 0, t = 0, reached = 1;
    que[t++] = src;
    dist[src] = 0;
    while (h < t) {
        int v = que[h++];
        if (dist[v] >= D_) continue;
        for (int l = 0; l < d_; l++) {
            int u = nbr(v, l);
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                que[t++] = u;
                reached++;
            }
        }
    }
    return N - reached;
}

static long long total_cost(void) {
    long long c = 0;
    for (int u = 0; u < 2 * k_; u++) c += bfs_bad(u * G_);
    return c;
}

static void init_state(void) {
    for (int l = 0; l < d_; l++) {
        int p[4];
        for (int i = 0; i < k_; i++) p[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k_; i++) {
            perm[l * k_ + i] = p[i];
            pinv[l * k_ + p[i]] = i;
        }
        for (int i = 0; i < k_; i++) set_s(l * k_ + i, rint_(G_));
    }
}

static int is_new(int v, int l, int u) {
    for (int l2 = 0; l2 < l; l2++) if (nbr(v, l2) == u) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || k_ > 3 || m_ < 1 || k2_ < 1 || m_ * k2_ < 2) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    pw = malloc(sizeof(int) * (size_t)k2_);
    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    pinv = malloc(sizeof(int) * (size_t)d_ * k_);
    S = malloc(sizeof(int) * (size_t)d_ * k_);
    Si = malloc(sizeof(int) * (size_t)d_ * k_);
    dist = malloc(sizeof(int) * (size_t)N_);
    que = malloc(sizeof(int) * (size_t)N_);
    if (!pw || !perm || !pinv || !S || !Si || !dist || !que) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = (int)(((long long)pw[t - 1] * r) % m_);

    init_state();
    long long cur = total_cost();
    const double T0 = 6.0, T1 = 0.2;
    clock_t c0 = clock();
    while (cur > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        if (k_ >= 2 && rdbl() < 0.25) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int a1 = l * k_ + i1, a2 = l * k_ + i2;
            int tmp = perm[a1]; perm[a1] = perm[a2]; perm[a2] = tmp;
            pinv[l * k_ + perm[a1]] = i1;
            pinv[l * k_ + perm[a2]] = i2;
            long long nc = total_cost();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                tmp = perm[a1]; perm[a1] = perm[a2]; perm[a2] = tmp;
                pinv[l * k_ + perm[a1]] = i1;
                pinv[l * k_ + perm[a2]] = i2;
            }
        } else {
            int idx = rint_(d_ * k_);
            int s = rint_(G_);
            if (s == S[idx]) continue;
            int old = S[idx];
            set_s(idx, s);
            long long nc = total_cost();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                set_s(idx, old);
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    long long mout = 0;
    int nA = k_ * G_;
    for (int v = 0; v < nA; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr(v, l);
            if (is_new(v, l, u)) mout++;
        }
    printf("%d %lld\n", N_, mout);
    for (int v = 0; v < nA; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr(v, l);
            if (is_new(v, l, u)) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (unchanged).
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

_KS = (1, 2, 3)


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
    """Run the C annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _sample_group_exact(G, rng):
    """Return (m, k2, r) with m * k2 == G defining Z_m x| Z_k2 (r^k2 = 1 mod m)."""
    cands = [k2 for k2 in range(1, min(G, 48) + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(cands)
    for k2 in cands[:6]:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            return m, k2, rng.choice(rs)
    return G, 1, 1


def _lift_search(d, D, best, rng, end):
    """Repeatedly ask the C lift annealer for a valid lift larger than the current best."""
    fails = 0
    while fails < 14:
        remaining = end - time.monotonic()
        if remaining < 1.5:
            break
        k = rng.choice(_KS)
        n_best = best[0]
        frac = rng.uniform(0.002, 0.02)
        target = int(n_best * (1.0 + frac)) + 2 * k
        G = -(-target // (2 * k))
        m, k2, r = _sample_group_exact(G, rng)
        budget = min(remaining, 8.0)
        try:
            out = lib.run_c(LIFT_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            fails += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            fails = 0
        else:
            fails += 1
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

    # Phase 1: voltage-lift annealing in C over small semidirect groups.
    if d >= 2:
        lift_end = t0 + max(1.0, min(0.6 * time_limit, time_limit - 15.0))
        best = _lift_search(d, D, best, rng, lift_end)

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + max(1.0, min(0.7 * time_limit, time_limit - 10.0))
    if time.monotonic() < slack_end:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3: C annealer grows the best valid graph by vertex pairs.
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
