import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite edge-toggle annealer with vertex growth.
#
# The state is a bipartite graph with max degree d. A move toggles one
# cross-side pair (a, b): if a or b is full, one of its edges is dropped
# first. The cost is the number of ordered vertex pairs at distance > D,
# computed with bitset ball expansion. Per-vertex unreached counts are kept
# for the current state, and roughly half of the proposed endpoints are drawn
# from vertices that still have unreached pairs. Whenever the cost reaches
# zero, the current valid graph is saved and two isolated vertices (one per
# side) are added, so the search keeps growing the graph while time remains.
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
static int *bvCur, *bvNew;   /* per-vertex unreached counts: current state / candidate */
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

/* Fills out[v] = number of vertices at distance > D_ from v. Returns the sum
   over v (ordered pairs at distance > D_). Zero means the graph is valid. */
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

/* Biased endpoint choice: often pick a vertex that still has unreached pairs. */
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

    /* Bipartition by BFS; isolated vertices take the side of their root. */
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
# New construction: difference-cover search for cyclic Haar graphs.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d, so it is d-regular and
# bipartite on 2m vertices. Walks alternate +s and -s, so with D_S = S - S:
#   * a-a distance <= 2t  iff  the t-fold sumset of D_S covers Z_m,
#   * a-b distance <= 2t+1 iff  S + (t-fold sumset of D_S) covers Z_m.
# Hence the diameter test reduces to a difference-cover condition on S, which is
# cheap to evaluate with bitmask rotations. We anneal over S (with 0 fixed in S,
# since translation changes nothing) to drive the uncovered count to zero, and
# climb m upward so the order 2m beats the best order found so far.
# ----------------------------------------------------------------------------

def _rot(x, s, m, mask):
    """Bitmask x with every element i moved to (i + s) mod m."""
    s %= m
    if s == 0:
        return x
    return ((x << s) | (x >> (m - s))) & mask


def _sumset(bits, shifts, m, mask):
    """Bitmask of {x + t : x in bits, t in shifts} mod m."""
    out = 0
    for s in shifts:
        out |= _rot(bits, s, m, mask)
    return out


def _diff_cost(S, m, D, mask):
    """Number of uncovered residues in the two covering conditions for H(m, S) at diameter D."""
    shifts = sorted({(x - y) % m for x in S for y in S})
    E = 1  # {0}
    for _ in range(D // 2):
        E = _sumset(E, shifts, m, mask)
    F = 0
    for x in S:
        F |= 1 << x
    for _ in range((D - 1) // 2):
        F = _sumset(F, shifts, m, mask)
    return (m - bin(E).count("1")) + (m - bin(F).count("1"))


def _anneal_diff(d, m, D, rng, deadline):
    """Anneal a d-element S in Z_m (0 in S) with zero difference-cover cost; returns S or None."""
    if d < 2 or m < d:
        return None
    mask = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)
    cost = _diff_cost(S, m, D, mask)
    best_local = cost
    stall = 0
    patience = 1500
    T0, T1 = 2.0, 0.08
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        if stall > patience:
            S = [0] + rng.sample(range(1, m), d - 1)
            cost = _diff_cost(S, m, D, mask)
            best_local, stall = cost, 0
            continue
        i = rng.randrange(1, d)
        v = rng.randrange(1, m)
        if v in S:
            stall += 1
            continue
        old = S[i]
        S[i] = v
        c2 = _diff_cost(S, m, D, mask)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_local:
                best_local, stall = cost, 0
            else:
                stall += 1
        else:
            S[i] = old
            stall += 1
    if cost == 0:
        return sorted(S)
    return None


def _difference_phase(d, D, base_n, rng, deadline):
    """Climb m upward from base_n/2 with the difference-cover annealer; returns best valid (n, edges) or None."""
    m = max(d, base_n // 2 + 1)
    total = max(1.0, deadline - time.monotonic())
    result = None
    while time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        budget = min(remaining, max(3.0, 0.3 * total))
        S = _anneal_diff(d, m, D, rng, time.monotonic() + budget)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            if lib.is_valid(n, e, d, D):
                result = (n, e)
                m += 1
                continue
        if result is None:
            # Nothing found yet at this order: back off a little.
            m = max(d, m - max(1, m // 50))
        else:
            break
    return result


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


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

    # Phase 1: difference-cover search for cyclic Haar graphs H(m, S).
    phase_end = t0 + max(1.0, min(0.55 * time_limit, time_limit - 12.0))
    res = _difference_phase(d, D, best[0], rng, phase_end)
    if res is not None:
        consider(res[0], res[1])

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
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
