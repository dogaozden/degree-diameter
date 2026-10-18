import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine with two modes.
#
#   "lift" mode: simulated annealing over voltage lifts of a bipartite base
#     graph with k blocks per side, lifted over a semidirect product
#     Z_m x| Z_k2. The lift is vertex-transitive within each block (left
#     multiplication is an automorphism), so the cost needs only one BFS per
#     block: the sum of unreached vertices from each block representative.
#     Cost 0 means valid. Runs at C speed, so far more moves than the Python
#     version.
#
#   default mode: edge-toggle annealer that grows a valid graph by vertex
#     pairs (unchanged from the previous engine).
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

/* ============================ lift mode ============================ */

static int L_d, L_D, L_k, L_m, L_k2, L_G, L_NV;
static int *L_pw, *L_perm, *L_iperm, *L_S, *L_iS, *L_nbr, *L_dist, *L_q, *L_stamp;
static int L_cur_stamp = 0;

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product Z_m x| Z_k2, element a*k2 + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / L_k2, b = x % L_k2;
    int c = y / L_k2, e = y % L_k2;
    int aa = (int)(((long long)a + (long long)L_pw[b] * c) % L_m);
    return aa * L_k2 + (b + e) % L_k2;
}

static int ginv(int x) {
    int a = x / L_k2, b = x % L_k2;
    int nb = (L_k2 - b) % L_k2;
    int t = (int)(((long long)L_pw[nb] * a) % L_m);
    int na = (L_m - t) % L_m;
    return na * L_k2 + nb;
}

static void build_nbr(void) {
    int A = L_k * L_G;
    for (int v = 0; v < L_NV; v++) {
        for (int l = 0; l < L_d; l++) {
            int w;
            if (v < A) {
                int i = v / L_G, x = v % L_G;
                int j = L_perm[l * L_k + i];
                int s = L_S[l * L_k + i];
                w = (L_k + j) * L_G + gmul(x, s);
            } else {
                int t = v - A;
                int j = t / L_G, y = t % L_G;
                int i = L_iperm[l * L_k + j];
                int si = L_iS[l * L_k + i];
                w = i * L_G + gmul(y, si);
            }
            L_nbr[v * L_d + l] = w;
        }
    }
}

/* Sum over block representatives of vertices NOT within distance D. */
static long long lift_cost(void) {
    build_nbr();
    long long bad = 0;
    for (int b = 0; b < 2 * L_k; b++) {
        L_cur_stamp++;
        int h = 0, t = 0;
        int src = b * L_G;
        L_stamp[src] = L_cur_stamp;
        L_dist[src] = 0;
        L_q[t++] = src;
        int cnt = 1;
        while (h < t) {
            int v = L_q[h++];
            int dv = L_dist[v];
            if (dv >= L_D) continue;
            const int *nb = L_nbr + (size_t)v * L_d;
            for (int l = 0; l < L_d; l++) {
                int u = nb[l];
                if (L_stamp[u] != L_cur_stamp) {
                    L_stamp[u] = L_cur_stamp;
                    L_dist[u] = dv + 1;
                    L_q[t++] = u;
                    cnt++;
                }
            }
        }
        bad += L_NV - cnt;
    }
    return bad;
}

static void swap_perm(int l, int i1, int i2) {
    int *P = L_perm + l * L_k;
    int *IP = L_iperm + l * L_k;
    int t = P[i1]; P[i1] = P[i2]; P[i2] = t;
    IP[P[i1]] = i1;
    IP[P[i2]] = i2;
}

static void randomize_state(void) {
    for (int l = 0; l < L_d; l++) {
        int *P = L_perm + l * L_k;
        for (int i = 0; i < L_k; i++) P[i] = i;
        for (int i = L_k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[i]; P[i] = P[j]; P[j] = t;
        }
        for (int i = 0; i < L_k; i++) L_iperm[l * L_k + P[i]] = i;
        for (int i = 0; i < L_k; i++) {
            int s = rint_(L_G);
            L_S[l * L_k + i] = s;
            L_iS[l * L_k + i] = ginv(s);
        }
    }
}

static void print_lift_graph(void) {
    int A = L_k * L_G;
    long long cnt = 0;
    for (int v = 0; v < A; v++) {
        for (int l = 0; l < L_d; l++) {
            int w = L_nbr[v * L_d + l], dup = 0;
            for (int l2 = 0; l2 < l; l2++) {
                if (L_nbr[v * L_d + l2] == w) { dup = 1; break; }
            }
            if (!dup) cnt++;
        }
    }
    printf("%d %lld\n", L_NV, cnt);
    for (int v = 0; v < A; v++) {
        for (int l = 0; l < L_d; l++) {
            int w = L_nbr[v * L_d + l], dup = 0;
            for (int l2 = 0; l2 < l; l2++) {
                if (L_nbr[v * L_d + l2] == w) { dup = 1; break; }
            }
            if (!dup) printf("%d %d\n", v, w);
        }
    }
}

/* argv: prog lift d D k m k2 r seed seconds */
static int lift_main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    int d = atoi(argv[2]), D = atoi(argv[3]), k = atoi(argv[4]);
    int m = atoi(argv[5]), k2 = atoi(argv[6]), r = atoi(argv[7]);
    u64 seed = (u64)strtoull(argv[8], NULL, 10);
    double limit = atof(argv[9]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d < 1 || D < 1 || k < 1 || k > 16 || m < 2 || k2 < 1 || r < 0 || r >= m) {
        printf("0 0\n");
        return 0;
    }
    long long G = (long long)m * k2;
    if (G * 2 * k > 200000) { printf("0 0\n"); return 0; }
    if (gcd_(r, m) != 1) { printf("0 0\n"); return 0; }
    long long p = 1 % m;
    for (int t = 0; t < k2; t++) p = p * r % m;
    if (p != 1 % m) { printf("0 0\n"); return 0; }

    L_d = d; L_D = D; L_k = k; L_m = m; L_k2 = k2;
    L_G = (int)G;
    L_NV = 2 * k * (int)G;

    L_pw = malloc(sizeof(int) * (size_t)k2);
    L_perm = malloc(sizeof(int) * (size_t)d * k);
    L_iperm = malloc(sizeof(int) * (size_t)d * k);
    L_S = malloc(sizeof(int) * (size_t)d * k);
    L_iS = malloc(sizeof(int) * (size_t)d * k);
    L_nbr = malloc(sizeof(int) * (size_t)L_NV * d);
    L_dist = malloc(sizeof(int) * (size_t)L_NV);
    L_q = malloc(sizeof(int) * (size_t)L_NV);
    L_stamp = calloc((size_t)L_NV, sizeof(int));
    if (!L_pw || !L_perm || !L_iperm || !L_S || !L_iS || !L_nbr || !L_dist || !L_q || !L_stamp) {
        printf("0 0\n");
        return 0;
    }
    long long pw = 1 % m;
    for (int t = 0; t < k2; t++) {
        L_pw[t] = (int)pw;
        pw = pw * r % m;
    }

    randomize_state();
    long long cost = lift_cost();
    double c0f = (double)(cost > 0 ? cost : 1);
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = c0f * 0.03 * pow(0.02, frac);
        if (T < 0.3) T = 0.3;

        int l = rint_(d);
        long long c2;
        int mv = 0, a1 = 0, a2 = 0, old = 0;
        if (k >= 2 && rdbl() < 0.3) {
            mv = 1;
            int i1 = rint_(k);
            int i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            a1 = i1; a2 = i2;
            swap_perm(l, i1, i2);
            c2 = lift_cost();
        } else {
            int i = rint_(k);
            int nw = rint_(L_G);
            old = L_S[l * k + i];
            if (nw == old) continue;
            a1 = i;
            L_S[l * k + i] = nw;
            L_iS[l * k + i] = ginv(nw);
            c2 = lift_cost();
        }
        long long delta = c2 - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            if (mv) {
                swap_perm(l, a1, a2);
            } else {
                L_S[l * k + a1] = old;
                L_iS[l * k + a1] = ginv(old);
            }
        }
    }

    if (cost == 0) {
        /* Rebuild neighbours for the accepted state before printing. */
        build_nbr();
        print_lift_graph();
    } else {
        printf("0 0\n");
    }
    return 0;
}

/* ============================ grow mode ============================ */

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

static int grow_main(int argc, char **argv) {
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

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "lift") == 0) return lift_main(argc, argv);
    return grow_main(argc, argv);
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)


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
    """Run the C vertex-growing annealer from a valid graph; returns parsed output."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _lift_in_c(d, D, k, m, k2, r, seed, seconds):
    """Run the C voltage-lift annealer over Z_m x| Z_k2 with k blocks per side."""
    out = lib.run_c(C_SOURCE, ["lift", d, D, k, m, k2, r, seed, f"{seconds:.2f}"],
                    timeout=seconds + 10.0)
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
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        if math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m:
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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    T = time_limit

    # Phase 1: C-level voltage-lift search over semidirect products.
    py_end = t0 + max(1.0, min(0.55 * T, T - 15.0))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = py_end - time.monotonic()
        if remaining < 0.5:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        trials[k] += 1
        slice_s = min(4.0, remaining)
        try:
            n, e = _lift_in_c(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), slice_s)
        except Exception:
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            wins[k] += 1
            consider(n, e)

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + max(1.0, min(0.62 * T, T - 12.0))
    if time.monotonic() < slack_end - 0.5:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
            consider(n2, e2)
        except Exception:
            pass

    # Phase 3: C annealer grows the best valid graph by vertex pairs.
    c_budget = T - (time.monotonic() - t0) - 4.0
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
