import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (u64)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d, D, K, M, K2, R, G, NV, W;
static int *mt, *adj, *vol, *sig, *pw;
static u64 *bufA, *bufB;
static clock_t t0;
static double budget;

static int time_left(void) {
    return ((double)(clock() - t0) / CLOCKS_PER_SEC) < budget;
}

/* Group Z_M x| Z_K2, element (a,b) coded a*K2+b, (a,b)(c,e) = (a + R^b c, b+e). */
static void build_group(void) {
    long long p = 1 % M;
    pw = malloc(sizeof(int) * (size_t)K2);
    for (int b = 0; b < K2; b++) {
        pw[b] = (int)p;
        p = (p * R) % M;
    }
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        for (int g = 0; g < G; g++) {
            int c = g / K2, e = g % K2;
            int na = (int)(((long long)a + (long long)pw[b] * c) % M);
            int nb = (b + e) % K2;
            mt[x * G + g] = na * K2 + nb;
        }
    }
}

static void random_base(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) sig[t * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[t * K + i];
            sig[t * K + i] = sig[t * K + j];
            sig[t * K + j] = tmp;
        }
    }
    for (int i = 0; i < K * d; i++) vol[i] = rndint(G);
}

/* A-vertex (i,x) = i*G+x, B-vertex (j,y) = K*G + j*G + y.
   Dart (i, t): A(i,x) -- B(sig_t(i), x*vol). Each vertex gets exactly d slots. */
static void build_adj(void) {
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) {
            int j = sig[t * K + i];
            int g = vol[i * d + t];
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                int b = K * G + j * G + mt[x * G + g];
                adj[a * d + t] = b;
                adj[b * d + t] = a;
            }
        }
}

/* Number of ordered pairs at distance > D. Zero means diameter <= D. */
static long long bad_cost(void) {
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)NV * (size_t)W);
    for (int v = 0; v < NV; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < NV; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(u64) * (size_t)W);
            for (int t = 0; t < d; t++) {
                const u64 *q = cur + (size_t)adj[v * d + t] * W;
                for (int w = 0; w < W; w++) o[w] |= q[w];
            }
        }
        u64 *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        int cnt = 0;
        const u64 *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += pc64(c[w]);
        bad += NV - cnt;
    }
    return bad;
}

static void print_graph(void) {
    int cap = K * G * d;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    int cnt = 0;
    for (int a = 0; a < K * G; a++) {
        int nb[64];
        for (int t = 0; t < d; t++) nb[t] = adj[a * d + t];
        for (int i = 1; i < d; i++) {
            int x = nb[i], j = i;
            while (j > 0 && nb[j - 1] > x) {
                nb[j] = nb[j - 1];
                j--;
            }
            nb[j] = x;
        }
        for (int t = 0; t < d; t++) {
            if (t > 0 && nb[t] == nb[t - 1]) continue;
            eu[cnt] = a;
            ev[cnt] = nb[t];
            cnt++;
        }
    }
    printf("%d %d\n", NV, cnt);
    for (int e = 0; e < cnt; e++) printf("%d %d\n", eu[e], ev[e]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: d D seed time K M K2 R\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || d > 64 || D < 1 || K < 1 || M < 1 || K2 < 1) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G > 1500) {
        printf("0 0\n");
        return 0;
    }
    NV = 2 * K * G;
    W = (NV + 63) / 64;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    adj = malloc(sizeof(int) * (size_t)NV * (size_t)d);
    vol = malloc(sizeof(int) * (size_t)K * (size_t)d);
    sig = malloc(sizeof(int) * (size_t)K * (size_t)d);
    bufA = malloc(sizeof(u64) * (size_t)NV * (size_t)W);
    bufB = malloc(sizeof(u64) * (size_t)NV * (size_t)W);
    build_group();

    t0 = clock();
    const int L = 2500;
    while (time_left()) {
        random_base();
        build_adj();
        long long cur = bad_cost();
        for (int it = 0; it < L && cur > 0 && time_left(); it++) {
            double frac = (double)it / (double)L;
            double T = NV * 0.5 * pow(0.01, frac);
            int idx = rndint(K * d);
            int old = vol[idx];
            int g = rndint(G);
            if (g == old) continue;
            vol[idx] = g;
            build_adj();
            long long nc = bad_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                vol[idx] = old;
                build_adj();
            }
        }
        if (cur == 0) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (degree q+1, diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d and q <= 16."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Growth steps. Each keeps diameter <= D and bipartiteness.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same neighbourhood) while neighbours have spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts of small base graphs over Z_m x| Z_k2 (run in C).
# ----------------------------------------------------------------------------

def _pick_group(G, rng):
    """Random (m, k2, r) with m * k2 = G, giving the group Z_m x| Z_k2."""
    cands = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1:
            cands.append((m, 1, 1))
            continue
        if m < 2:
            continue
        rs_ = [r for r in range(1, m)
               if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        for r in rng.sample(rs_, min(len(rs_), 2)):
            cands.append((m, k2, r))
    return rng.choice(cands) if cands else None


def _lift_phase(d, D, n_best, deadline, rng):
    """Search lifts of K+K base vertices over groups of order G, growing G while successful.

    Returns the largest valid graph found (n, edges) or None. Every result is
    checked with lib.is_valid before it is returned.
    """
    found = None
    G_state = {1: 0, 2: 0, 3: 0}
    fails = {1: 0, 2: 0, 3: 0}
    while True:
        live = [K for K in (1, 2, 3) if fails[K] < 3]
        now = time.monotonic()
        if not live or deadline - now < 4.0:
            break
        K = rng.choice(live)
        G = max(G_state[K], n_best // (2 * K) + 1)
        if 2 * K * G > 2400 or G > 1200:
            fails[K] = 3
            continue
        pick = _pick_group(G, rng)
        if pick is None:
            G_state[K] = G + 1
            continue
        m, k2, r = pick
        slice_s = min(5.0, deadline - now - 3.0)
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}",
                              K, m, k2, r],
                             timeout=slice_s + 4.0)
            n, e = lib.parse_graph_text(text)
        except Exception:
            n, e = 0, []
        if n >= 1 and n > n_best and lib.is_valid(n, e, d, D):
            found = (n, e)
            n_best = n
            G_state[K] = G + 1
            fails[K] = 0
        else:
            fails[K] += 1
            G_state[K] = G
    return found


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        for i, q in enumerate(pg_qs):
            try:
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = start + 0.85 * time_limit * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)
            except Exception:
                pass
        return best

    if D >= 4:
        # Fallback family: generalized quadrangle plus growth.
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                gq_end = start + 0.35 * time_limit
                for _ in range(40):
                    if time.monotonic() >= gq_end:
                        break
                    pn, pe = _pipeline(gq[0], gq[1], d, D, gq_end, rng)
                    consider(pn, pe)
        except Exception:
            pass

        # Main family: C voltage-lift search over small non-cyclic groups.
        try:
            lift_end = start + 0.88 * time_limit
            found = _lift_phase(d, D, best[0], lift_end, rng)
            if found is not None:
                consider(found[0], found[1])
        except Exception:
            pass

    return best
