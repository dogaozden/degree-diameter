import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New engine: bi-Cayley lift annealer in C.
#
# A lift has 2k blocks of G vertices (A-blocks 0..k-1, B-blocks k..2k-1) over the
# semidirect product Z_m x| Z_k2. Each of the d layers is a permutation T of the
# k A-blocks onto the k B-blocks, with a voltage V per (layer, A-block). The edges
# are (i, g) -- (T(i), g*V).
#
# New ideas in this engine:
#  * Left multiplication is an automorphism, so the diameter test reduces to the
#    2k block representatives. Each vertex carries one 64-bit mask over those
#    sources, and ball expansion costs N*d*D word operations per evaluation.
#  * Moves are voltage changes, target swaps inside one layer, and targeted
#    voltage changes at vertices that are still unreached.
#  * Simulated annealing runs in restarts until a zero-cost lift is found.
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
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
static int popc(u64 x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }
static long long gcdll(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }

static int d_, D_, k_, Gm_, Gk_, G_, N_;
static int *PW, *T_, *V_, *nb;
static u64 *RA, *RB;
static const long long PEN = 40;

/* Semidirect product Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / Gk_, b = x % Gk_;
    int c = y / Gk_, e = y % Gk_;
    long long t = ((long long)PW[b] * c + a) % Gm_;
    int s = b + e;
    if (s >= Gk_) s -= Gk_;
    return (int)(t * Gk_ + s);
}

static int ginv(int x) {
    int a = x / Gk_, b = x % Gk_;
    int nbb = (Gk_ - b) % Gk_;
    long long t = ((long long)PW[nbb] * a) % Gm_;
    long long v = (Gm_ - t) % Gm_;
    return (int)(v * Gk_ + nbb);
}

/* Recompute all adjacency entries that layer l touches. */
static void rebuild_layer(int l) {
    int *nbl = nb + (size_t)l * N_;
    for (int i = 0; i < k_; i++) {
        int j = T_[l * k_ + i], s = V_[l * k_ + i];
        int si = ginv(s);
        int Ai = i * G_, Bj = (k_ + j) * G_;
        for (int g = 0; g < G_; g++) {
            nbl[Ai + g] = Bj + gmul(g, s);
            nbl[Bj + g] = Ai + gmul(g, si);
        }
    }
}

/* Repeated (block, voltage) pairs for the same A-block create multi-edges. */
static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (T_[l * k_ + i] == T_[l2 * k_ + i] && V_[l * k_ + i] == V_[l2 * k_ + i]) dup++;
    return dup;
}

/* Number of (vertex, source block) pairs at distance > D_. */
static long long eval_reach(void) {
    u64 full = (1ULL << (2 * k_)) - 1;
    for (int v = 0; v < N_; v++) RA[v] = (v % G_ == 0) ? (1ULL << (v / G_)) : 0ULL;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N_; v++) {
            u64 x = RA[v];
            for (int l = 0; l < d_; l++) x |= RA[nb[(size_t)l * N_ + v]];
            RB[v] = x;
            changed |= (x != RA[v]);
        }
        u64 *tmp = RA; RA = RB; RB = tmp;
        if (!changed) break;
    }
    long long c = 0;
    for (int v = 0; v < N_; v++) c += popc(full & ~RA[v]);
    return c;
}

static long long total_cost(void) {
    return eval_reach() + PEN * (long long)dupcount();
}

static void random_init(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) T_[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = T_[l * k_ + i]; T_[l * k_ + i] = T_[l * k_ + j]; T_[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) V_[l * k_ + i] = rint_(G_);
        rebuild_layer(l);
    }
}

static void output_graph(void) {
    long long m = (long long)d_ * k_ * G_;
    printf("%d %lld\n", N_, m);
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) {
            int j = T_[l * k_ + i], s = V_[l * k_ + i];
            for (int g = 0; g < G_; g++)
                printf("%d %d\n", i * G_ + g, (k_ + j) * G_ + gmul(g, s));
        }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    Gm_ = atoi(argv[6]);
    Gk_ = atoi(argv[7]);
    long long r = atoll(argv[8]);
    if (d_ < 1 || d_ > 32 || D_ < 1 || k_ < 1 || k_ > 31 || Gm_ < 1 || Gk_ < 1) {
        printf("0 0\n"); return 0;
    }
    long long Gll = (long long)Gm_ * Gk_;
    long long Nll = 2LL * k_ * Gll;
    if (Gll > 2000000 || Nll > 4000000) { printf("0 0\n"); return 0; }
    G_ = (int)Gll;
    N_ = (int)Nll;
    r %= Gm_;
    if (r < 0) r += Gm_;
    if (gcdll(r, Gm_) != 1) { printf("0 0\n"); return 0; }

    PW = malloc(sizeof(int) * (size_t)Gk_);
    if (!PW) { printf("0 0\n"); return 0; }
    long long p = 1 % Gm_;
    for (int b = 0; b < Gk_; b++) { PW[b] = (int)p; p = (p * r) % Gm_; }
    if (p != 1 % Gm_) { printf("0 0\n"); return 0; }

    T_ = malloc(sizeof(int) * (size_t)d_ * k_);
    V_ = malloc(sizeof(int) * (size_t)d_ * k_);
    nb = malloc(sizeof(int) * (size_t)d_ * N_);
    RA = malloc(sizeof(u64) * (size_t)N_);
    RB = malloc(sizeof(u64) * (size_t)N_);
    if (!T_ || !V_ || !nb || !RA || !RB) { printf("0 0\n"); return 0; }

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 16; w++) rnd();

    const double TS = 8.0, TE = 0.3;
    const long long RUN = 20000;
    u64 full = (1ULL << (2 * k_)) - 1;
    int sT[32], sV[32];
    clock_t c0 = clock();
    int found = 0;

    while (!found) {
        if ((double)(clock() - c0) / CLOCKS_PER_SEC >= limit) break;
        random_init();
        long long cur = total_cost();
        for (long long it = 0; it < RUN && cur > 0; it++) {
            if ((it & 127) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC >= limit) break;
            double Temp = TS * pow(TE / TS, (double)it / (double)RUN);
            int l = rint_(d_);
            int base = l * k_;
            for (int i = 0; i < k_; i++) { sT[i] = T_[base + i]; sV[i] = V_[base + i]; }
            double x = rdbl();
            if (x < 0.4 || k_ == 1) {
                int i = rint_(k_);
                V_[base + i] = rint_(G_);
            } else if (x < 0.65) {
                int i1 = rint_(k_), i2 = rint_(k_ - 1);
                if (i2 >= i1) i2++;
                int t = T_[base + i1]; T_[base + i1] = T_[base + i2]; T_[base + i2] = t;
            } else {
                int i = rint_(k_);
                for (int tries = 0; tries < 40; tries++) {
                    int v = rint_(N_);
                    if (full & ~RA[v]) {
                        int bl = v / G_;
                        if (bl < k_) {
                            i = bl;
                        } else {
                            for (int q = 0; q < k_; q++)
                                if (T_[base + q] == bl - k_) { i = q; break; }
                        }
                        break;
                    }
                }
                V_[base + i] = rint_(G_);
            }
            rebuild_layer(l);
            long long nc = total_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / Temp)) {
                cur = nc;
            } else {
                for (int i = 0; i < k_; i++) { T_[base + i] = sT[i]; V_[base + i] = sV[i]; }
                rebuild_layer(l);
            }
        }
        if (cur == 0) found = 1;
    }

    if (found) output_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Parent engine: edge-toggle annealer that grows a valid graph by vertex pairs.
# ----------------------------------------------------------------------------

C_GROW_SOURCE = r"""
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

static long long bad_pairs(void) {
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
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
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
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB) {
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
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = rint_(N), y = rint_(N);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
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

_KS = (1, 2, 3, 4, 5, 6, 8)


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
    """Run the C toggle annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_GROW_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 5.0)
    return lib.parse_graph_text(out)


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer over Z_m x| Z_k2 with k blocks per side; returns (n, edges) or (0, [])."""
    out = lib.run_c(LIFT_C_SOURCE, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    import math as _m
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if _m.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if _m.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
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

    if D == 2 or d == 1:
        return best
    if d == 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    # Exact constructions for D = 3.
    pg = _best_pg(d) if D >= 3 else None
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # calibration case: exact incidence graph
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Phase 1: C lift annealer over semidirect-product groups, aiming above the current best.
    lift_end = t0 + 0.62 * time_limit
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    per_call = min(max(1.5, 0.04 * time_limit), 6.0)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        need = best[0] + 2
        target = max(2, -(-need // (2 * k)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        trials[k] += 1
        try:
            n, e = _lift_in_c(d, D, k, m, k2, r, min(per_call, remaining),
                              rng.randrange(1, 1 << 30))
        except Exception:
            continue
        if n > best[0]:
            wins[k] += 1
            consider(n, e)

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + 0.72 * time_limit
    if time.monotonic() < slack_end:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3: C toggle annealer grows the best valid graph by vertex pairs.
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
