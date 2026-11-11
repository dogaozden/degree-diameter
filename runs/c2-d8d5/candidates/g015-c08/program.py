import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage-lift search over semidirect products Z_m x| Z_k2.
#
# A lift has k "A" base vertices and k "B" base vertices, each with d darts.
# Layer l gives A-vertex i a dart to B-vertex lay[l][i] (lay[l] is a
# permutation, so every B-vertex also receives exactly d darts) with voltage
# vol[l][i] in G. Lifted vertices are (i, g) and (k + j, h), with edges
# (i, g) -- (k + lay[l][i], g * vol[l][i]). The graph is bipartite, d-regular,
# and invariant under left multiplication by G, so the distance condition only
# needs one BFS per base vertex. Cost = total unreached vertices over the 2k
# representatives, plus a penalty for duplicate darts. Simulated annealing
# moves change one voltage or swap two layer entries.
#
# Input: stdin is a "graph" whose first number is the spec count S and whose
# edge list holds 2S pairs. Spec s is pairs (k, m) and (k2, r) = (2s, 2s+1).
# Output: the first valid lift found, as "n m" plus edges, or "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define MAXD 40
#define MAXK 8
#define MAXG 2000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, N_;
static int mulT[MAXG * MAXG];
static int invE[MAXG];
static int pw[MAXG];
static int lay[MAXD][MAXK], vol[MAXD][MAXK], invLay[MAXD][MAXK];
static int adjT[2 * MAXK * MAXG * MAXD];
static int vis[2 * MAXK * MAXG];
static int qu[2 * MAXK * MAXG];
static int stamp_ = 0;
static double limit_;
static clock_t c0_;

static double elapsed(void) { return (double)(clock() - c0_) / CLOCKS_PER_SEC; }

static void nbrs(int v, int *out) {
    int blk = v / G_, x = v % G_;
    if (blk < k_) {
        for (int l = 0; l < d_; l++)
            out[l] = (k_ + lay[l][blk]) * G_ + mulT[x * G_ + vol[l][blk]];
    } else {
        int j = blk - k_;
        for (int l = 0; l < d_; l++) {
            int i = invLay[l][j];
            out[l] = i * G_ + mulT[x * G_ + invE[vol[l][i]]];
        }
    }
}

static int ball(int src) {
    stamp_++;
    if (stamp_ == 0x7ffffff0) { memset(vis, 0, sizeof vis); stamp_ = 1; }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp_;
    for (int depth = 0; depth < D_; depth++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = qu[head++];
            const int *a = &adjT[v * MAXD];
            for (int t = 0; t < d_; t++) {
                int u = a[t];
                if (vis[u] != stamp_) { vis[u] = stamp_; qu[tail++] = u; }
            }
        }
    }
    return tail;
}

static long long full_cost(void) {
    for (int v = 0; v < N_; v++) nbrs(v, &adjT[v * MAXD]);
    long long tot = 0;
    for (int b = 0; b < 2 * k_; b++) tot += (long long)(N_ - ball(b * G_));
    long long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (lay[l1][i] == lay[l2][i] && vol[l1][i] == vol[l2][i]) dup++;
    return tot + 1000LL * dup;
}

static int build_group(int m, int k2, int r) {
    if (m < 1 || k2 < 1) return 0;
    long long G = (long long)m * k2;
    if (G > MAXG) return 0;
    G_ = (int)G;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { pw[b] = (int)p; p = (p * r) % m; }
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, dd = y % k2;
            mulT[x * G_ + y] = ((a + pw[b] * c) % m) * k2 + (b + dd) % k2;
        }
    }
    for (int x = 0; x < G_; x++) {
        invE[x] = -1;
        for (int y = 0; y < G_; y++)
            if (mulT[x * G_ + y] == 0) { invE[x] = y; break; }
        if (invE[x] < 0) return 0;
    }
    return 1;
}

static void swapL(int l, int a, int b) {
    int ja = lay[l][a], jb = lay[l][b];
    lay[l][a] = jb; lay[l][b] = ja;
    invLay[l][jb] = a; invLay[l][ja] = b;
}

static void randomize(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) lay[l][i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < k_; i++) invLay[l][lay[l][i]] = i;
        for (int i = 0; i < k_; i++) vol[l][i] = rint_(G_);
    }
}

static int anneal(int iters) {
    randomize();
    long long cur = full_cost();
    if (cur == 0) return 1;
    const double T0 = 30.0, T1 = 0.3;
    for (int it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() >= limit_) return 0;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int l = rint_(d_), i = rint_(k_);
        if (rint_(10) < 7) {
            int old = vol[l][i];
            int nw = rint_(G_);
            if (nw == old) continue;
            vol[l][i] = nw;
            long long nc = full_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                vol[l][i] = old;
            }
        } else {
            int i2 = rint_(k_);
            if (i2 == i) continue;
            swapL(l, i, i2);
            long long nc = full_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
                if (cur == 0) return 1;
            } else {
                swapL(l, i, i2);
            }
        }
    }
    return 0;
}

static void print_graph(void) {
    int N = 2 * k_ * G_;
    long long M = (long long)k_ * G_ * d_;
    printf("%d %lld\n", N, M);
    for (int i = 0; i < k_; i++)
        for (int g = 0; g < G_; g++)
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", i * G_ + g, (k_ + lay[l][i]) * G_ + mulT[g * G_ + vol[l][i]]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    limit_ = atof(argv[4]);
    c0_ = clock();
    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }

    int S = 0, M = 0;
    if (scanf("%d %d", &S, &M) != 2) { printf("0 0\n"); return 0; }
    int nspec = M / 2;
    if (nspec <= 0) { printf("0 0\n"); return 0; }
    int *val = malloc(sizeof(int) * (size_t)(4 * nspec));
    if (!val) { printf("0 0\n"); return 0; }
    for (int i = 0; i < 4 * nspec; i++) {
        if (scanf("%d", &val[i]) != 1) { printf("0 0\n"); return 0; }
    }

    int any_ran = 1;
    while (elapsed() < limit_ && any_ran) {
        any_ran = 0;
        for (int s = 0; s < nspec && elapsed() < limit_; s++) {
            int k = val[4 * s], m = val[4 * s + 1], k2 = val[4 * s + 2], r = val[4 * s + 3];
            if (k < 1 || k > MAXK) continue;
            if (!build_group(m, k2, r)) continue;
            k_ = k;
            N_ = 2 * k_ * G_;
            any_ran = 1;
            if (anneal(6000)) {
                print_graph();
                free(val);
                return 0;
            }
        }
    }
    free(val);
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (growth): bipartite edge-toggle annealer with vertex growth.
# Used only as a final phase on the best valid graph found.
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
    """Run the C growth annealer from a valid graph; returns parsed output (may be (0, []))."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _find_r(m, k2, rng):
    """Return r with gcd(r, m) = 1 and r^k2 = 1 mod m; r = 1 (direct product) always works."""
    if k2 == 1 or m < 3:
        return 1
    for _ in range(80):
        c = rng.randrange(2, m)
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            return c
    return 1


def _make_specs(best_n, rng, count=40):
    """Random lift specs (k, m, k2, r) whose order 2*k*G lies just above best_n."""
    specs = []
    tries = 0
    while len(specs) < count and tries < count * 10:
        tries += 1
        k = rng.choice((1, 2, 2, 3, 3, 4, 4, 5, 6))
        span = max(4, best_n // rng.choice((100, 30, 12)))
        target = best_n + 2 + rng.randrange(span)
        G = max(2, -(-target // (2 * k)))
        if G > 2000:
            continue
        divs = [x for x in range(1, 41) if G % x == 0 and G // x >= 2]
        k2 = rng.choice(divs)
        m = G // k2
        r = _find_r(m, k2, rng)
        specs.append((k, m, k2, r))
    return specs


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

    # Exact constructions for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Phase 1: C voltage-lift search over semidirect products, aimed just above best.
    lift_end = t0 + 0.60 * time_limit
    if d <= 30:
        while True:
            left = lift_end - time.monotonic()
            if left < 1.5:
                break
            specs = _make_specs(best[0], rng)
            if not specs:
                break
            pairs = []
            for k, m, k2, r in specs:
                pairs.append((k, m))
                pairs.append((k2, r))
            try:
                out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{left:.2f}"],
                                stdin_graph=(len(specs), pairs), timeout=left + 15.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                break
            if n == 0:
                break
            before = best[0]
            consider(n, e)
            if best[0] == before:
                break

    # Phase 2: use spare degree in the current best graph (cheap; often nothing).
    slack_end = t0 + 0.66 * time_limit
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
