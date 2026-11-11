import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage-lift annealer over the semidirect product
# G = Z_m x| Z_k2 (element a*k2+b, multiplication (a,b)(c,e) = (a + r^b c, b+e)).
#
# Base graph: K vertices on side A and K on side B. Layer l (0..d-1) gives,
# for each A-base vertex i, one dart to B-base vertex perm[l][i] with voltage
# s[l][i]. The lift has vertices (i, x) and (K+j, y), x, y in G, and edges
#   (i, x) -- (K+j, x*s)   for every layer dart (i -> j, s).
# Left multiplication by G is an automorphism group that is transitive on each
# block, so the number of vertices at distance > D from a vertex is the same for
# every vertex in a block. The cost is therefore a BFS from the 2K block
# representatives only: sum of unreached counts + PEN * (duplicate darts).
# Moves: re-draw a voltage, or swap two base targets within a layer.
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

static int d_, D_, K, M, K2, G, N;
static int *pw, *perm, *invp, *sv, *invs, *nbr, *dist, *queue, *stamp;
static int curstamp = 0;
static long long PEN = 4;

static int gmul(int x, int y) {
    long long a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (a + (long long)pw[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)pw[nb] * a) % M;
    long long u = (M - t) % M;
    return (int)(u * K2 + nb);
}

static void build_nbr(void) {
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d_; l++) {
                int j = perm[l * K + i];
                nbr[v * d_ + l] = (K + j) * G + gmul(x, sv[l * K + i]);
            }
        }
    for (int j = 0; j < K; j++)
        for (int y = 0; y < G; y++) {
            int v = (K + j) * G + y;
            for (int l = 0; l < d_; l++) {
                int i = invp[l * K + j];
                nbr[v * d_ + l] = i * G + gmul(y, invs[l * K + i]);
            }
        }
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1 * K + i] == perm[l2 * K + i] && sv[l1 * K + i] == sv[l2 * K + i]) c++;
    return c;
}

/* Zero iff every block representative reaches all N vertices within D_ steps
   and no two darts from the same base vertex coincide. */
static long long cost_eval(void) {
    long long tot = 0;
    for (int b = 0; b < 2 * K; b++) {
        curstamp++;
        int h = 0, t = 0, src = b * G;
        queue[t++] = src;
        stamp[src] = curstamp;
        dist[src] = 0;
        while (h < t) {
            int v = queue[h++];
            if (dist[v] >= D_) continue;
            for (int l = 0; l < d_; l++) {
                int u = nbr[v * d_ + l];
                if (stamp[u] != curstamp) {
                    stamp[u] = curstamp;
                    dist[u] = dist[v] + 1;
                    queue[t++] = u;
                }
            }
        }
        tot += N - t;
    }
    return tot + PEN * dupcount();
}

static void output_graph(void) {
    printf("%d %d\n", N, K * G * d_);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d_; l++) printf("%d %d\n", v, nbr[v * d_ + l]);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    int R = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K < 1 || K > 16 || M < 2 || K2 < 1 || M > 1000000 || K2 > 1000000) {
        printf("0 0\n");
        return 0;
    }
    long long Gll = (long long)M * K2;
    if (Gll * K > 2000000LL) { printf("0 0\n"); return 0; }
    G = (int)Gll;
    N = 2 * K * G;
    R %= M;
    if (R < 0) R += M;

    pw = malloc(sizeof(int) * K2);
    perm = malloc(sizeof(int) * d_ * K);
    invp = malloc(sizeof(int) * d_ * K);
    sv = malloc(sizeof(int) * d_ * K);
    invs = malloc(sizeof(int) * d_ * K);
    nbr = malloc(sizeof(int) * (size_t)N * d_);
    dist = malloc(sizeof(int) * N);
    queue = malloc(sizeof(int) * N);
    stamp = calloc(N, sizeof(int));
    if (!pw || !perm || !invp || !sv || !invs || !nbr || !dist || !queue || !stamp) {
        printf("0 0\n");
        return 0;
    }

    pw[0] = 1 % M;
    for (int t = 1; t < K2; t++) pw[t] = (int)((long long)pw[t - 1] * R % M);
    if ((long long)pw[K2 - 1] * R % M != 1 % M) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++) {
        if (gmul(x, ginv(x)) != 0) { printf("0 0\n"); return 0; }
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = perm[l * K + i];
            perm[l * K + i] = perm[l * K + j];
            perm[l * K + j] = tmp;
        }
        for (int i = 0; i < K; i++) invp[l * K + perm[l * K + i]] = i;
        for (int i = 0; i < K; i++) {
            sv[l * K + i] = rint_(G);
            invs[l * K + i] = ginv(sv[l * K + i]);
        }
    }

    build_nbr();
    long long cur = cost_eval();
    if (cur == 0) { output_graph(); return 0; }

    const double T0 = 2.0, T1 = 0.05;
    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int l = rint_(d_);
        int swapmove = (K >= 2 && rdbl() < 0.3);
        int i1 = 0, i2 = 0, idx = 0, oldv = 0, oldinv = 0;
        if (swapmove) {
            i1 = rint_(K);
            i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l * K + i1];
            perm[l * K + i1] = perm[l * K + i2];
            perm[l * K + i2] = tmp;
            invp[l * K + perm[l * K + i1]] = i1;
            invp[l * K + perm[l * K + i2]] = i2;
        } else {
            int i = rint_(K);
            idx = l * K + i;
            oldv = sv[idx];
            oldinv = invs[idx];
            sv[idx] = rint_(G);
            invs[idx] = ginv(sv[idx]);
        }

        build_nbr();
        long long nc = cost_eval();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) { output_graph(); return 0; }
        } else {
            if (swapmove) {
                int tmp = perm[l * K + i1];
                perm[l * K + i1] = perm[l * K + i2];
                perm[l * K + i2] = tmp;
                invp[l * K + perm[l * K + i1]] = i1;
                invp[l * K + perm[l * K + i2]] = i2;
            } else {
                sv[idx] = oldv;
                invs[idx] = oldinv;
            }
            build_nbr();
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (general graphs).
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

_KS = (1, 2, 2, 3, 3, 4)


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


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16])
        m = max(2, -(-target // k2)) + rng.randrange(0, 3)
        if k2 == 1:
            return m, 1, 1
        cands = [c for c in range(1, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: C voltage-lift search over small semidirect groups.
    # Each call either returns a lift of order > current best or times out.
    lift_end = t0 + max(1.0, min(0.6 * time_limit, time_limit - 15.0))
    while time.monotonic() < lift_end - 0.3:
        K = rng.choice(_KS)
        target = best[0] // (2 * K) + 1 + rng.randrange(0, 4)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * K * m * k2 <= best[0]:
            continue
        slice_s = min(3.0, max(0.3, lift_end - time.monotonic()))
        try:
            out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}",
                                     K, m, k2, r],
                            timeout=slice_s + 15.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            continue

    # Phase 2: use spare degree in the current best graph.
    slack_end = max(time.monotonic() + 0.5, t0 + min(0.7 * time_limit, time_limit - 10.0))
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
