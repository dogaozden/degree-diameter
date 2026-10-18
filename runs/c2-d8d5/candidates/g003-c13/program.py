import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley (voltage) lift search over Z_m x| Z_k2.
#
# The graph has 2k blocks of G = m*k2 vertices (A_0..A_{k-1}, B_0..B_{k-1}).
# Layer l (0..d-1) joins A_i to B_{perm_l(i)} with voltage S[l][i]:
# (A_i, g) ~ (B_j, g*s). Every vertex has degree d and the graph is bipartite.
# Left translations are automorphisms, so the diameter test only needs the
# 2k block identities as sources. Each vertex keeps a 2k-bit mask of sources
# within distance D. Cost = unreached (vertex, source) pairs + penalty*duplicates.
# Simulated annealing on voltages and per-layer permutations.
# Prints the lift when cost reaches 0, otherwise "0 0".
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define PEN 300LL

static int d_, D_, k_, m_, k2_, G_, N_;
static int *nb, *perm, *Sv, *pw;
static u64 *cur, *nxt;

static int mulg(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    int t = (int)(((long long)a + (long long)pw[b] * c) % m_);
    return t * k2_ + (b + e) % k2_;
}

static int invg(int s) {
    int a = s / k2_, b = s % k2_;
    int nbt = (k2_ - b) % k2_;
    int t = (int)((m_ - ((long long)pw[nbt] * a) % m_) % m_);
    return t * k2_ + nbt;
}

static void update_dart(int l, int i) {
    int j = perm[l * k_ + i];
    int s = Sv[l * k_ + i];
    int si = invg(s);
    for (int g = 0; g < G_; g++)
        nb[(size_t)(i * G_ + g) * d_ + l] = (k_ + j) * G_ + mulg(g, s);
    for (int y = 0; y < G_; y++)
        nb[(size_t)((k_ + j) * G_ + y) * d_ + l] = i * G_ + mulg(y, si);
}

static long long evaluate(void) {
    int N = N_, nbits = 2 * k_;
    u64 *a = cur, *b = nxt;
    for (int v = 0; v < N; v++) a[v] = 0;
    for (int j = 0; j < nbits; j++) a[(size_t)j * G_] |= 1ULL << j;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = a[v];
            const int *nv = nb + (size_t)v * d_;
            for (int l = 0; l < d_; l++) x |= a[nv[l]];
            b[v] = x;
            if (x != a[v]) changed = 1;
        }
        u64 *t = a; a = b; b = t;
        if (!changed) break;
    }
    cur = a; nxt = b;
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += nbits - __builtin_popcountll(a[v]);
    long long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (perm[l * k_ + i] == perm[l2 * k_ + i] && Sv[l * k_ + i] == Sv[l2 * k_ + i]) dup++;
    return unr + PEN * dup;
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
    int r = atoi(argv[8]);
    double T0 = argc > 9 ? atof(argv[9]) : 6.0;
    if (d_ < 1 || D_ < 1 || k_ < 1 || 2 * k_ > 64 || m_ < 1 || k2_ < 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    if (G_ < 2 || G_ > 100000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    if (N_ > 400000) { printf("0 0\n"); return 0; }
    r %= m_;
    if (r < 0) r += m_;
    pw = malloc(sizeof(int) * (size_t)k2_);
    if (!pw) { printf("0 0\n"); return 0; }
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = (int)((long long)pw[t - 1] * r % m_);
    if ((long long)pw[k2_ - 1] * r % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    nb = malloc(sizeof(int) * (size_t)N_ * d_);
    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    Sv = malloc(sizeof(int) * (size_t)d_ * k_);
    cur = malloc(sizeof(u64) * (size_t)N_);
    nxt = malloc(sizeof(u64) * (size_t)N_);
    if (!nb || !perm || !Sv || !cur || !nxt) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        int *p = perm + l * k_;
        for (int i = 0; i < k_; i++) p[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k_; i++) Sv[l * k_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) update_dart(l, i);

    long long cost = evaluate();
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(0.2 / T0, el / limit);
        if (k_ < 2 || rdbl() < 0.75) {
            int l = rint_(d_), i = rint_(k_);
            int idx = l * k_ + i;
            int old = Sv[idx];
            int ns = rint_(G_);
            if (ns == old) continue;
            Sv[idx] = ns;
            update_dart(l, i);
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                Sv[idx] = old;
                update_dart(l, i);
            }
        } else {
            int l = rint_(d_);
            int i1 = rint_(k_), i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *p = perm + l * k_;
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            update_dart(l, i1);
            update_dart(l, i2);
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                update_dart(l, i1);
                update_dart(l, i2);
            }
        }
    }

    if (cost == 0) {
        int A = k_ * G_;
        printf("%d %lld\n", 2 * A, (long long)A * d_);
        for (int v = 0; v < A; v++)
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", v, nb[(size_t)v * d_ + l]);
        return 0;
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (unchanged).
# ----------------------------------------------------------------------------

GROW_C = r"""
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

_K_CHOICES = (1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _random_group(G, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order G = m*k2, using r^k2 = 1 mod m."""
    divs = [t for t in range(1, G + 1) if G % t == 0]
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1 or m < 2:
        return G, 1, 1
    if m == 2:
        return 2, k2, 1
    for _ in range(100):
        r = rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return m, k2, r
    return G, 1, 1


def _lift_search(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(LIFT_C, [d, D, seed, f"{seconds:.2f}", k, m, k2, r, 6.0],
                    timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C edge-toggle annealer from a valid graph; returns parsed output."""
    out = lib.run_c(GROW_C, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # exact Moore-type construction (calibration case)
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Phase 1: C lift search over semidirect-product voltage graphs, laddering up in order.
    lift_end = t0 + 0.72 * time_limit
    slice_s = max(1.0, min(3.0, (lift_end - t0) / 20.0))
    moore = lib.moore_bound(d, D)
    target = best[0] + 2
    fails = 0
    while time.monotonic() + 1.0 < lift_end and target <= moore:
        ks = [k for k in _K_CHOICES if target % (2 * k) == 0 and target // (2 * k) >= 2]
        if not ks:
            target += 2
            continue
        k = rng.choice(ks)
        G = target // (2 * k)
        m, k2, r = _random_group(G, rng)
        sec = min(slice_s, lift_end - time.monotonic())
        if sec < 0.3:
            break
        try:
            n, e = _lift_search(d, D, k, m, k2, r, sec, rng.randrange(1, 1 << 30))
        except Exception:
            break
        before = best[0]
        consider(n, e)
        if best[0] > before:
            target = best[0] + 2 * max(1, best[0] // 200)
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                target += 2
                fails = 0

    # Phase 2: C edge-toggle growth from the best valid graph.
    grow_s = time_limit - 5.0 - (time.monotonic() - t0)
    if grow_s >= 2.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_s,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
