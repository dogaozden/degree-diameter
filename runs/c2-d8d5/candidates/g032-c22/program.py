import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift search over Z_m x| Z_k2.
#
# The graph has 2k blocks of size G = m*k2 (k A-blocks, k B-blocks). Layer l
# joins A-block i to B-block perm[l][i] with voltage volt[l][i]:
# (i, x) ~ (perm, x*s). The group acts regularly on each block by left
# multiplication, so validity only needs a BFS from one representative per
# block. Cost = unreached pairs from representatives + penalty for duplicate
# edges. Stops as soon as the cost is zero and prints the lifted graph.
# ----------------------------------------------------------------------------

C_BILIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rin(int n) { return (int)(rnd() % (u64)n); }
static double rdb(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int *perm, *volt, *nbr, *pw, *stamp, *fq, *fd;
static int curstamp = 0;
static const long long PEN = 1000;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* Semidirect product Z_m x| Z_k2, element a*k2+b, (a,b)*(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    long long aa = ((long long)a + (long long)pw[b] * c) % m_;
    return (int)(aa * k2_ + (b + e) % k2_);
}

static void set_layer(int l) {
    const int *P = perm + (size_t)l * k_;
    const int *V = volt + (size_t)l * k_;
    for (int i = 0; i < k_; i++) {
        int j = P[i], s = V[i];
        for (int x = 0; x < G_; x++) {
            int a = i * G_ + x;
            int b = (k_ + j) * G_ + gmul(x, s);
            nbr[(size_t)a * d_ + l] = b;
            nbr[(size_t)b * d_ + l] = a;
        }
    }
}

static long long dupcount(void) {
    long long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++) {
            int pj = perm[l * k_ + i], sv = volt[l * k_ + i];
            for (int l2 = l + 1; l2 < d_; l2++)
                if (perm[l2 * k_ + i] == pj && volt[l2 * k_ + i] == sv) dup++;
        }
    return dup;
}

static long long unreached_from(int src) {
    curstamp++;
    int h = 0, t = 0, cnt = 1;
    fq[t] = src; fd[t] = 0; t++;
    stamp[src] = curstamp;
    while (h < t) {
        int v = fq[h], dv = fd[h];
        h++;
        if (dv >= D_) continue;
        const int *nb = nbr + (size_t)v * d_;
        for (int l = 0; l < d_; l++) {
            int u = nb[l];
            if (stamp[u] != curstamp) {
                stamp[u] = curstamp;
                fq[t] = u; fd[t] = dv + 1; t++; cnt++;
            }
        }
    }
    return (long long)(N_ - cnt);
}

static long long cost_all(void) {
    long long c = 0;
    for (int b = 0; b < 2 * k_; b++) c += unreached_from(b * G_);
    return c + PEN * dupcount();
}

static void print_graph(void) {
    long long m = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++)
            if (nbr[(size_t)v * d_ + l] > v) m++;
    printf("%d %lld\n", N_, m);
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[(size_t)v * d_ + l];
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
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 2 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    if ((long long)k_ * 2 * m_ * k2_ > 400000LL) { printf("0 0\n"); return 0; }
    r_ = ((r_ % m_) + m_) % m_;
    if (gcd_(r_, m_) != 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)k2_);
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r_ % m_);
    if ((long long)pw[k2_ - 1] * r_ % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)k_ * d_);
    volt = malloc(sizeof(int) * (size_t)k_ * d_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    stamp = calloc((size_t)N_, sizeof(int));
    fq = malloc(sizeof(int) * (size_t)N_);
    fd = malloc(sizeof(int) * (size_t)N_);
    int *tmp = malloc(sizeof(int) * (size_t)k_);
    if (!perm || !volt || !nbr || !stamp || !fq || !fd || !tmp) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) tmp[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rin(i + 1), t = tmp[i];
            tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < k_; i++) {
            perm[l * k_ + i] = tmp[i];
            volt[l * k_ + i] = rin(G_);
        }
    }
    for (int l = 0; l < d_; l++) set_layer(l);

    long long cost = cost_all();
    clock_t c0 = clock();
    const double T0 = 30.0, T1 = 0.3;

    while (cost != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rin(d_);
        int *P = perm + (size_t)l * k_;
        int *V = volt + (size_t)l * k_;
        if (k_ >= 2 && rdb() < 0.3) {
            int i1 = rin(k_), i2 = rin(k_ - 1);
            if (i2 >= i1) i2++;
            int t = P[i1]; P[i1] = P[i2]; P[i2] = t;
            set_layer(l);
            long long nc = cost_all();
            if (nc <= cost || rdb() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = P[i1]; P[i1] = P[i2]; P[i2] = t;
                set_layer(l);
            }
        } else {
            int i = rin(k_);
            int old = V[i], nw = rin(G_);
            if (nw == old) continue;
            V[i] = nw;
            set_layer(l);
            long long nc = cost_all();
            if (nc <= cost || rdb() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                V[i] = old;
                set_layer(l);
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: edge-toggle annealer with vertex growth (from the previous parent).
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
    """Run the C edge-toggle annealer from a valid graph; returns parsed output."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _group_for(G, rng):
    """Return (m, k2, r) with m * k2 == G for Z_m x| Z_k2, or None."""
    divs = [k2 for k2 in range(1, min(G, 48) + 1) if G % k2 == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            return m, 1, 1
        for _ in range(80):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def _bilift_phase(d, D, best, rng, end):
    """Repeated bi-Cayley lift searches in C, each aiming just above the current best order."""
    jump = 1.08
    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        k = rng.choice((1, 2, 2, 3, 3, 4, 4, 5, 5, 6))
        G = math.ceil((best[0] + 2) / (2.0 * k) * jump)
        g = _group_for(max(G, 2), rng)
        if g is None:
            continue
        m, k2, r = g
        slice_s = min(remaining - 0.5, max(2.0, min(6.0, remaining / 3.0)))
        try:
            out = lib.run_c(C_BILIFT, [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}",
                                       k, m, k2, r], timeout=slice_s + 10.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            n, e = 0, []
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        else:
            jump = max(1.002, 1.0 + (jump - 1.0) * 0.7)
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

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best  # exact Moore-type construction (calibration case)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n2, e2 = lib.araujo_lopez_graph(d - 2)
                if lib.is_valid(n2, e2, d, D):
                    return n2, e2
            except Exception:
                pass

    # Phase 1: C bi-Cayley lift search (new construction family, fast inner loop).
    if d >= 3:
        best = _bilift_phase(d, D, best, rng, t0 + 0.6 * time_limit)

    # Phase 2: use any spare degree.
    slack_end = t0 + 0.7 * time_limit
    n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
    consider(n2, e2)

    # Phase 3: C edge-toggle annealer grows the best valid graph by vertex pairs.
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
