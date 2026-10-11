import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-accelerated annealing of bipartite semidirect-product lifts.
#
# New in this version. The base has S "A" blocks and S "B" blocks with d darts
# per block (so every block has degree d). A dart (i, j, g) joins A-copy
# i*G+x to B-copy j*G+mul(x,g), where mul is the semidirect product
# Z_M x|_R Z_K (G = M*K), exactly as lib.semidirect_group and lib.group_lift
# define it. The C program anneals the voltages and B-endpoints with
# bitset BFS to count pairs at distance > D, and prints the first lift
# with zero cost. Python then saturates and grows it as before.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAX_NV 8192

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d, DIA, S, M, K, R, G, NV, WW, ND;
static int *pw, *dA, *dB, *dG, *oldA, *oldB, *oldG, *adjn, *adj;
static uint64_t *bufA, *bufB;
static clock_t T0;
static double LIMIT;

static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int group_mul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    return ((a + pw[b] * c) % M) * K + (b + e) % K;
}

static void build_graph(void) {
    int n = NV;
    memset(adjn, 0, sizeof(int) * (size_t)n);
    for (int k = 0; k < ND; k++) {
        int i = dA[k], j = dB[k], g = dG[k];
        for (int x = 0; x < G; x++) {
            int a = i * G + x;
            int b = j * G + group_mul(x, g);
            int dup = 0;
            for (int t = 0; t < adjn[a]; t++) {
                if (adj[(size_t)a * d + t] == b) { dup = 1; break; }
            }
            if (dup) continue;
            if (adjn[a] >= d || adjn[b] >= d) continue;
            adj[(size_t)a * d + adjn[a]++] = b;
            adj[(size_t)b * d + adjn[b]++] = a;
        }
    }
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIA (unreachable pairs count). */
static long cost_now(void) {
    int n = NV, w = WW;
    build_graph();
    uint64_t *cur = bufA, *nxt = bufB, *tmp;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIA; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            for (int t = 0; t < adjn[v]; t++) {
                const uint64_t *su = cur + (size_t)adj[(size_t)v * d + t] * w;
                for (int q = 0; q < w; q++) dst[q] |= su[q];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    long missing = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        const uint64_t *src = cur + (size_t)v * w;
        for (int q = 0; q < w; q++) pc += pop64(src[q]);
        missing += n - pc;
    }
    return missing / 2;
}

static void random_darts(void) {
    for (int k = 0; k < ND; k++) { dA[k] = k / d; dB[k] = k / d; }
    for (int t = ND - 1; t > 0; t--) {
        int s = rndint(t + 1);
        int tmp = dB[t]; dB[t] = dB[s]; dB[s] = tmp;
    }
    for (int k = 0; k < ND; k++) { dB[k] += S; dG[k] = rndint(G); }
}

static void output_graph(void) {
    build_graph();
    long m = 0;
    for (int v = 0; v < NV; v++) m += adjn[v];
    m /= 2;
    printf("%d %ld\n", NV, m);
    for (int v = 0; v < NV; v++) {
        for (int t = 0; t < adjn[v]; t++) {
            int u = adj[(size_t)v * d + t];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: prog d D s M k r seed budget\n"); return 1; }
    d = atoi(argv[1]); DIA = atoi(argv[2]); S = atoi(argv[3]);
    M = atoi(argv[4]); K = atoi(argv[5]); R = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    LIMIT = atof(argv[8]);
    if (d < 1 || d > 32 || DIA < 1 || S < 1 || M < 2 || K < 1 || M > MAX_NV || K > MAX_NV) {
        printf("0 0\n"); return 0;
    }
    G = M * K;
    if (G > MAX_NV) { printf("0 0\n"); return 0; }
    NV = 2 * S * G;
    if (NV > MAX_NV) { printf("0 0\n"); return 0; }
    rng_state = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rng_state == 0) rng_state = 1;
    T0 = clock();

    WW = (NV + 63) / 64;
    pw = malloc(sizeof(int) * K);
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);
    ND = S * d;
    dA = malloc(sizeof(int) * ND); dB = malloc(sizeof(int) * ND); dG = malloc(sizeof(int) * ND);
    oldA = malloc(sizeof(int) * ND); oldB = malloc(sizeof(int) * ND); oldG = malloc(sizeof(int) * ND);
    adjn = malloc(sizeof(int) * NV);
    adj = malloc(sizeof(int) * (size_t)NV * d);
    bufA = malloc(sizeof(uint64_t) * (size_t)NV * WW);
    bufB = malloc(sizeof(uint64_t) * (size_t)NV * WW);
    if (!pw || !dA || !dB || !dG || !oldA || !oldB || !oldG || !adjn || !adj || !bufA || !bufB) {
        printf("0 0\n"); return 0;
    }

    while (elapsed() < LIMIT) {
        random_darts();
        long cur = cost_now();
        double temp = 0.6;
        long best = cur;
        long stall = 0;
        while (cur > 0 && elapsed() < LIMIT && stall < 6000) {
            memcpy(oldA, dA, sizeof(int) * ND);
            memcpy(oldB, dB, sizeof(int) * ND);
            memcpy(oldG, dG, sizeof(int) * ND);
            if (ND >= 2 && rnd01() < 0.5) {
                int p = rndint(ND), q = rndint(ND);
                if (p == q) continue;
                int tmp = dB[p]; dB[p] = dB[q]; dB[q] = tmp;
            } else {
                dG[rndint(ND)] = rndint(G);
            }
            long nw = cost_now();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / temp)) {
                cur = nw;
            } else {
                memcpy(dA, oldA, sizeof(int) * ND);
                memcpy(dB, oldB, sizeof(int) * ND);
                memcpy(dG, oldG, sizeof(int) * ND);
            }
            if (cur < best) { best = cur; stall = 0; } else stall++;
            temp *= 0.9995;
            if (temp < 0.05) temp = 0.05;
        }
        if (cur == 0) { output_graph(); return 0; }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers (from the parent).
# ----------------------------------------------------------------------------

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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Voltage lifts over small groups.
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: cyclic plus Z_M x|_r Z_k with M*k = G."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    """Python fallback annealer (used only if the C engine cannot run).

    Returns (result, darts, temp): result is a valid (n, edges) or None.
    """
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return (n, e), darts, temp


def _lift_c(d, D, s, M, k, r, seed, budget):
    """Run the C lift annealer for `budget` seconds. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, s, M, k, r, seed, round(budget, 3)],
                    timeout=budget + 10.0)
    try:
        n, e = lib.parse_graph_text(out)
    except ValueError:
        return None
    return (n, e) if n > 0 else None


def _lift_phase(d, D, get_best, deadline, rng, consider):
    """Search voltage lifts whose order beats the current best.

    Each slice runs the C annealer on a random (s, G, group) configuration.
    A lift that passes the diameter test is saturated with spare-degree edges
    and then grown with extra vertices. If the C engine fails, a Python
    annealer is used for the rest of the phase.
    """
    use_c = True
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
        G = best_n // (2 * s) + 1 + rng.randrange(4)
        opts = _group_options(G)
        if not opts:
            continue
        M, k, r = rng.choice(opts)
        slice_end = min(deadline, time.monotonic() + 4.0)
        budget = slice_end - time.monotonic()
        if budget < 0.5:
            break
        res = None
        if use_c:
            try:
                res = _lift_c(d, D, s, M, k, r, rng.randrange(1, 2**31), budget)
            except RuntimeError:
                use_c = False
        if not use_c:
            try:
                _, mul, _ = lib.semidirect_group(M, k, r)
            except ValueError:
                continue
            res = _lift_search(d, D, s, G, mul, rng, slice_end)[0]
        if res is None:
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# Large-neighbourhood search and pruning (from the parent).
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.8 * time_limit, split into phases:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   L  C-accelerated voltage lift search over semidirect groups, then grown
#   C  LNS from the best valid graph
#   D  redundant-edge pruning and regrowth
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.8 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown; then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: C-accelerated voltage lifts over semidirect groups.
    if D >= 2 and time.monotonic() < at(0.72):
        _lift_phase(d, D, lambda: best_n, at(0.72), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: LNS from the best valid graph of any construction.
    if D >= 2 and time.monotonic() < at(0.88):
        _lns(best_n, best_e, d, D, at(0.88), rng, consider)

    # Phase D: prune redundant edges and regrow from the best graph.
    if D >= 2 and time.monotonic() < at(0.97):
        _prune_regrow(best_n, best_e, d, D, at(0.97), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
