import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over Z_m x| Z_k2 (new in this version).
#
# A lift has 2K blocks of size G (A-blocks 0..K-1, B-blocks K..2K-1). Layer l
# joins A-block i to B-block lay[l][i] with voltage sv[l][i]: (i,g) ~ (j, g*s).
# The group acts by left multiplication, so the reach of every vertex is
# summarised by 2K bits (one per block representative). The cost is the number
# of unreached (vertex, representative) pairs plus a penalty for duplicate darts.
# Moves change one voltage, or swap two block assignments within a layer.
# The temperature cycles four times over the budget. The first zero-cost lift
# is printed and the program exits, so Python can move on to a larger group.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 32
#define MAXK 32
#define MAXKK 60
#define PENALTY 1000LL

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K, M_, K2, R_, G, N;
static int pw[MAXKK];
static int lay[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int *nbr;
static u64 *reach, *nreach;
static u64 fullmask;

/* Group Z_M x| Z_K2, element a*K2+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, dd = y % K2;
    long long t = (long long)a + (long long)pw[b] * c;
    int aa = (int)(t % M_);
    return aa * K2 + (b + dd) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = -(long long)pw[nb] * a;
    int c = (int)(((t % M_) + M_) % M_);
    return c * K2 + nb;
}

static void set_dart(int l, int i) {
    int j = lay[l][i], s = sv[l][i];
    int si = ginv(s);
    int Ab = i * G, Bb = (K + j) * G;
    int *row = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        row[Ab + g] = Bb + h;
        row[Bb + h] = Ab + gmul(h, si);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l][i] == lay[l2][i] && sv[l][i] == sv[l2][i]) c++;
    return c;
}

/* Sum over vertices of unreached representatives (0 iff valid lift). */
static long long eval_cost(void) {
    int nb = 2 * K;
    for (int v = 0; v < N; v++) reach[v] = 0;
    for (int b = 0; b < nb; b++) reach[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = reach[v];
            for (int l = 0; l < d_; l++) x |= reach[nbr[(size_t)l * N + v]];
            nreach[v] = x;
            if (x != reach[v]) changed = 1;
        }
        u64 *tmp = reach; reach = nreach; nreach = tmp;
        if (!changed) break;
    }
    long long c = 0;
    for (int v = 0; v < N; v++) c += nb - __builtin_popcountll(reach[v]);
    return c;
}

static void print_graph(void) {
    int A = K * G;
    long long m = (long long)A * d_;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[(size_t)l * N + v]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R_ = atoi(argv[8]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || K < 1 || K > MAXK ||
        M_ < 1 || K2 < 1 || K2 > MAXKK) { printf("0 0\n"); return 0; }
    if ((long long)M_ * K2 > 100000) { printf("0 0\n"); return 0; }
    G = M_ * K2;
    N = 2 * K * G;
    if (N > 300000 || G < d_) { printf("0 0\n"); return 0; }

    nbr = malloc(sizeof(int) * (size_t)d_ * N);
    reach = malloc(sizeof(u64) * (size_t)N);
    nreach = malloc(sizeof(u64) * (size_t)N);
    if (!nbr || !reach || !nreach) { printf("0 0\n"); return 0; }

    fullmask = (2 * K >= 64) ? ~0ULL : ((1ULL << (2 * K)) - 1);
    pw[0] = 1 % M_;
    for (int t = 1; t < K2; t++)
        pw[t] = (int)((long long)pw[t - 1] * ((R_ % M_)) % M_);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rint_(G);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);

    long long cost = eval_cost() + PENALTY * dupcount();
    if (cost == 0) { print_graph(); return 0; }

    const double T0 = 10.0, T1 = 0.2;
    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit * 4.0;
        frac = frac - floor(frac);
        double T = T0 * pow(T1 / T0, frac);

        if (K >= 2 && rdbl() < 0.2) {
            int l = rint_(d_);
            int i1 = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long long nc = eval_cost() + PENALTY * dupcount();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rint_(d_);
            int i = -1;
            int c = -1;
            if (rdbl() < 0.4) {
                for (int t = 0; t < 16; t++) {
                    int v = rint_(N);
                    if (reach[v] != fullmask) { c = v / G; break; }
                }
            }
            if (c >= 0) {
                if (c < K) i = c;
                else {
                    int j = c - K;
                    for (int q = 0; q < K; q++) if (lay[l][q] == j) { i = q; break; }
                }
            }
            if (i < 0) i = rint_(K);
            int old = sv[l][i];
            int nw = rint_(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_dart(l, i);
            long long nc = eval_cost() + PENALTY * dupcount();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                sv[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost == 0) { print_graph(); return 0; }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (from parent).
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
    """Run the C vertex-pair annealer from a valid graph; returns parsed output."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
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


def _run_lift(d, D, seed, seconds, k, m, k2, r):
    """Search for a valid bi-Cayley lift of order 2*k*m*k2; returns (n, edges) or None."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 15.0)
    n, e = lib.parse_graph_text(out)
    if n <= 0 or not e:
        return None
    return n, e


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

    # Phase 1: C lift annealer over sampled semidirect groups, bandit over k.
    lift_end = t0 + max(1.0, min(0.6 * time_limit, time_limit - 12.0))
    phase = max(1.0, lift_end - t0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_end - time.monotonic()
        if remaining <= 0.5:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        slice_s = min(remaining, max(2.0, 0.2 * phase))
        trials[k] += 1
        try:
            res = _run_lift(d, D, rng.randrange(1, 1 << 30), slice_s, k, m, k2, r)
        except RuntimeError:
            res = None
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + max(1.0, min(0.5 * time_limit, time_limit - 10.0))
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
