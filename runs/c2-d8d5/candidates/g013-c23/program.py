import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: bi-Cayley (voltage) lifts over semidirect products Z_m x| Z_k2.
#
# A base graph has K black and K white vertices. Each of the d layers is a
# permutation sigma_l of the K blocks, with a group voltage s_{l,i}. The lift
# joins (black i, x) to (white sigma_l(i), x*s_{l,i}). Left multiplication is an
# automorphism, so validity only needs the ball of each of the 2K block
# representatives to cover all vertices. That check is exact. The C annealer
# (LIFT_SOURCE) searches the voltages and layer permutations with this exact cost.
#
# The graph-growing annealer (GROW_SOURCE) from the parent is kept as a final
# phase. Every result is checked with lib.is_valid, and a valid fallback is kept.
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

#define MAXD 32
#define MAXK 8

static int d_, D_, K_, K2_, M_, R_, G_, NV_;
static int *pw;
static int sig[MAXD][MAXK], vol[MAXD][MAXK];
static int *nb;          /* NV_ * MAXD */
static int *seen, *dd, *qu;
static int stamp_ = 0;

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    long long t = ((long long)a + (long long)pw[b] * c) % M_;
    return (int)t * K2_ + (b + e) % K2_;
}

static void build_nb(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) {
            int j = sig[l][i], s = vol[l][i];
            for (int x = 0; x < G_; x++) {
                int y = gmul(x, s);
                int bv = i * G_ + x;
                int wv = (K_ + j) * G_ + y;
                nb[bv * MAXD + l] = wv;
                nb[wv * MAXD + l] = bv;
            }
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig[l][i] == sig[l2][i] && vol[l][i] == vol[l2][i]) c++;
    return c;
}

/* Exact: sum over block representatives of the number of vertices not within D_. */
static long long unreached_total(void) {
    long long tot = 0;
    for (int b = 0; b < 2 * K_; b++) {
        int root = b * G_;
        stamp_++;
        int h = 0, t = 0;
        qu[t++] = root;
        seen[root] = stamp_;
        dd[root] = 0;
        while (h < t) {
            int v = qu[h++];
            if (dd[v] >= D_) continue;
            for (int l = 0; l < d_; l++) {
                int u = nb[v * MAXD + l];
                if (seen[u] != stamp_) {
                    seen[u] = stamp_;
                    dd[u] = dd[v] + 1;
                    qu[t++] = u;
                }
            }
        }
        tot += NV_ - t;
    }
    return tot;
}

static void output(void) {
    int m = 0;
    for (int v = 0; v < NV_; v++)
        for (int l = 0; l < d_; l++)
            if (nb[v * MAXD + l] > v) m++;
    printf("%d %d\n", NV_, m);
    for (int v = 0; v < NV_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nb[v * MAXD + l];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    M_ = atoi(argv[5]);
    K2_ = atoi(argv[6]);
    R_ = atoi(argv[7]);
    K_ = atoi(argv[8]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || K_ < 1 || K_ > MAXK || M_ < 1 || K2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = M_ * K2_;
    NV_ = 2 * K_ * G_;
    if (NV_ > 200000) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * (size_t)K2_);
    pw[0] = 1 % M_;
    for (int t = 1; t < K2_; t++) pw[t] = (int)((long long)pw[t - 1] * R_ % M_);
    nb = malloc(sizeof(int) * (size_t)NV_ * MAXD);
    seen = calloc((size_t)NV_, sizeof(int));
    dd = calloc((size_t)NV_, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)NV_);
    if (!pw || !nb || !seen || !dd || !qu) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        int arr[MAXK];
        for (int i = 0; i < K_; i++) arr[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = arr[i]; arr[i] = arr[j]; arr[j] = t;
        }
        for (int i = 0; i < K_; i++) {
            sig[l][i] = arr[i];
            vol[l][i] = rint_(G_);
        }
    }
    build_nb();
    long long PEN = 3;
    long long cost = unreached_total() + PEN * dupcount();
    if (cost == 0) { output(); return 0; }

    clock_t c0 = clock();
    const double T0 = 4.0, T1 = 0.25;
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int kind = 0, l = rint_(d_), i = rint_(K_), i2 = 0, oldv = 0;
        if (rdbl() < 0.6 || K_ < 2) {
            kind = 0;
            oldv = vol[l][i];
            int nv = rint_(G_);
            if (nv == oldv) continue;
            vol[l][i] = nv;
        } else {
            kind = 1;
            i2 = rint_(K_ - 1);
            if (i2 >= i) i2++;
            int t = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = t;
        }
        build_nb();
        long long nc = unreached_total() + PEN * dupcount();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) { output(); return 0; }
        } else {
            if (kind == 0) {
                vol[l][i] = oldv;
            } else {
                int t = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = t;
            }
            build_nb();
        }
    }
    printf("0 0\n");
    return 0;
}
"""


GROW_SOURCE = r"""
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
# Python glue.
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
    """Run the C graph-growing annealer from a valid graph; returns (n, edges), maybe (0, [])."""
    out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _run_lift(d, D, seed, secs, m, k2, r, k):
    """Run the C voltage-lift annealer on Z_m x| Z_k2 with k blocks; returns (n, edges) or (0, [])."""
    out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{secs:.2f}", m, k2, r, k],
                    stdin_graph=None, timeout=secs + 10.0)
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
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, list(e))
        except Exception:
            pass

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: C voltage-lift search over semidirect products, with a bandit over k.
    lift_end = t0 + max(1.0, 0.62 * time_limit)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    try:
        while True:
            secs = min(5.0, lift_end - time.monotonic())
            if secs < 0.6:
                break
            k = pick_k()
            base = best[0] // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G = m * k2
            if 2 * k * G <= best[0]:
                continue
            trials[k] += 1
            try:
                n, e = _run_lift(d, D, rng.randrange(1, 1 << 30), secs, m, k2, r, k)
            except Exception:
                continue
            if n > 0 and n > best[0]:
                wins[k] += 1
                consider(n, e)
    except Exception:
        pass

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + max(1.0, 0.7 * time_limit)
    if time.monotonic() < slack_end:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
            consider(n2, e2)
        except Exception:
            pass

    # Phase 3: C annealer grows the best valid graph by vertex pairs.
    c_budget = time_limit - (time.monotonic() - t0) - 6.0
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
