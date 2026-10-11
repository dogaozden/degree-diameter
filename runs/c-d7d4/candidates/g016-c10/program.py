import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite voltage lifts over a semidirect product Z_m x| Z_k.
#
# Base: S vertices on side A and S on side B, every base vertex has exactly DEG
# darts (u, v, g). The lift has 2*S*N vertices (N = m*k), is bipartite and
# DEG-regular. Moves change one voltage or swap B-endpoints between two darts.
# The cost is the number of ordered vertex pairs at distance > DIAM, computed
# with bitsets. Output: "n m" plus edges on success, "0 0" on failure.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 4096
#define MAXW 64
#define MAXDEG 64
#define MAXL 8192

static int DIAM, DEG, S, M, K, R, N, NV, L, W;
static int *MT;
static int PW[MAXV];
static int du[MAXL], dv[MAXL], dg[MAXL];
static int nb[MAXV][MAXDEG];
static int ncnt[MAXV];
static uint64_t bufA[MAXV][MAXW];
static uint64_t bufB[MAXV][MAXW];
static uint64_t rs = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double cpu_now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    int a2 = (a + (int)(((int64_t)PW[b] * c) % M)) % M;
    int b2 = (b + e) % K;
    return a2 * K + b2;
}

static int init_darts(void) {
    static int slots[MAXL];
    int i, j, t, ok, tries;
    for (i = 0; i < L; i++) slots[i] = i / DEG;
    for (i = L - 1; i > 0; i--) {
        j = rndi(i + 1);
        t = slots[i];
        slots[i] = slots[j];
        slots[j] = t;
    }
    for (i = 0; i < L; i++) {
        du[i] = i / DEG;
        dv[i] = slots[i];
    }
    for (i = 0; i < L; i++) {
        ok = 0;
        for (tries = 0; tries < 500 && !ok; tries++) {
            dg[i] = rndi(N);
            ok = 1;
            for (j = 0; j < i; j++) {
                if (du[j] == du[i] && dv[j] == dv[i] && dg[j] == dg[i]) {
                    ok = 0;
                    break;
                }
            }
        }
        if (!ok) return 0;
    }
    return 1;
}

static int dup_at(int i) {
    int j;
    for (j = 0; j < L; j++) {
        if (j != i && du[j] == du[i] && dv[j] == dv[i] && dg[j] == dg[i]) return 1;
    }
    return 0;
}

static void build_adj(void) {
    int i, x, a, b, v;
    for (v = 0; v < NV; v++) ncnt[v] = 0;
    for (i = 0; i < L; i++) {
        for (x = 0; x < N; x++) {
            a = du[i] * N + x;
            b = (S + dv[i]) * N + MT[x * N + dg[i]];
            nb[a][ncnt[a]++] = b;
            nb[b][ncnt[b]++] = a;
        }
    }
}

static long long cost_eval(void) {
    int V = NV, v, r, w, t, u;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    uint64_t (*tmp)[MAXW];
    long long bad = 0;
    int c;
    build_adj();
    W = (V + 63) / 64;
    for (v = 0; v < V; v++) {
        for (w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < V; v++) {
            for (w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (t = 0; t < DEG; t++) {
                u = nb[v][t];
                for (w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    for (v = 0; v < V; v++) {
        c = 0;
        for (w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += V - c;
    }
    return bad;
}

static int run_search(double budget) {
    double t0 = cpu_now();
    while (cpu_now() - t0 < budget) {
        long long cur, nc;
        int stale = 0;
        if (!init_darts()) continue;
        cur = cost_eval();
        while (cur > 0 && stale < 4000 && cpu_now() - t0 < budget) {
            int i = rndi(L);
            int mode = rndi(2);
            int j = -1, og, ng, t;
            if (mode == 0) {
                og = dg[i];
                ng = rndi(N);
                if (ng == og) continue;
                dg[i] = ng;
                if (dup_at(i)) {
                    dg[i] = og;
                    continue;
                }
            } else {
                j = rndi(L);
                if (j == i || dv[j] == dv[i]) continue;
                t = dv[i];
                dv[i] = dv[j];
                dv[j] = t;
                if (dup_at(i) || dup_at(j)) {
                    t = dv[i];
                    dv[i] = dv[j];
                    dv[j] = t;
                    continue;
                }
            }
            nc = cost_eval();
            if (nc <= cur || rndi(1000) < 3) {
                cur = nc;
                if (cur < cur + 0) stale = 0;
                stale++;
                if (cur == 0) break;
            } else {
                if (mode == 0) {
                    dg[i] = og;
                } else {
                    t = dv[i];
                    dv[i] = dv[j];
                    dv[j] = t;
                }
                stale++;
            }
        }
        if (cur == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int d, a, t, x, y;
    unsigned long long seed;
    double budget;
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    (void)d;
    DIAM = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    S = atoi(argv[5]);
    M = atoi(argv[6]);
    K = atoi(argv[7]);
    R = atoi(argv[8]);
    DEG = atoi(argv[9]);
    if (S < 1 || M < 1 || K < 1 || DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    N = M * K;
    NV = 2 * S * N;
    L = S * DEG;
    if (NV > MAXV || N > MAXV || L > MAXL || (long long)N * N > 4000000LL) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    PW[0] = 1 % M;
    for (t = 1; t < K; t++) PW[t] = (int)(((int64_t)PW[t - 1] * (R % M)) % M);
    MT = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    if (!MT) {
        printf("0 0\n");
        return 0;
    }
    for (x = 0; x < N; x++) {
        for (y = 0; y < N; y++) MT[x * N + y] = gmul(x, y);
    }
    if (run_search(budget)) {
        build_adj();
        printf("%d %lld\n", NV, (long long)S * N * DEG);
        for (a = 0; a < S * N; a++) {
            for (t = 0; t < DEG; t++) printf("%d %d\n", a, nb[a][t]);
        }
    } else {
        printf("0 0\n");
    }
    free(MT);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (fallbacks and seeds).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of each other."""
    if D < 2:
        return n, edges
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
    """One randomized growth pipeline from a structured base."""
    n, e = base_n, list(base_e)
    if rng.randrange(2) == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
    n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Lift search driver (uses the C engine).
# ----------------------------------------------------------------------------

def _group_options(N, rng):
    """Candidate (m, k, r) with N = m*k: cyclic group and semidirect products Z_m x| Z_k."""
    opts = []
    for k in range(1, 13):
        if N % k:
            continue
        m = N // k
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    rng.shuffle(opts)
    return opts[:4]


def _lift_phase(d, D, best_n, rng, deadline, consider, moore):
    """Search voltage lifts over groups of growing order for several base sizes."""
    s_list = [2, 3, 4, 1]
    nxt = {s: best_n // (2 * s) + 1 for s in s_list}
    fails = {s: 0 for s in s_list}
    alive = list(s_list)
    while alive and time.monotonic() < deadline:
        s = rng.choice(alive)
        N = nxt[s]
        if 2 * s * N > moore:
            alive.remove(s)
            continue
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        budget = min(remaining - 1.0, max(3.0, remaining / 5.0))
        opts = _group_options(N, rng)
        if not opts:
            nxt[s] = N + 1
            continue
        m, k, r = rng.choice(opts)
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, rng.randrange(1 << 30), round(budget, 2), s, m, k, r, d],
                             timeout=budget + 5.0)
            n, e = lib.parse_graph_text(text)
        except (RuntimeError, ValueError):
            n, e = 0, []
        if n > 0 and lib.is_valid(n, e, d, D):
            consider(n, e)
            nxt[s] = N + 1
            fails[s] = 0
        else:
            fails[s] += 1
            if fails[s] >= 2:
                alive.remove(s)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)) grown, with a few growth trials
#   L  voltage lifts over cyclic / semidirect groups via the C engine
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), i.e. K_{d,d}, valid for every d >= 1 and D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base, grown with spare degree.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            try:
                n0, e0 = base
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
                consider(n1, e1)
            except Exception:
                pass
    if D >= 2 and best_n < moore:
        trial_end = at(0.12)
        try:
            while time.monotonic() < trial_end and best_n < moore:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)
        except Exception:
            pass

    # Phase L: voltage lifts over small groups (C engine).
    if D >= 2 and d >= 2 and best_n < moore and time.monotonic() < at(0.92):
        try:
            _lift_phase(d, D, best_n, rng, at(0.92), consider, moore)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
