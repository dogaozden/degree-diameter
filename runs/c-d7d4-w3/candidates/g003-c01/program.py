import itertools
import random
import time

import lib


# C engine: searches bi-Cayley graphs. A bi-Cayley graph over a group G with
# connection set S (|S| = d) has vertices a_x and b_x (x in G), with a_x ~ b_{x*s}
# for s in S. G acts by left multiplication, so diameter <= D only needs BFS from
# a_e and b_e. Groups are Z_M x| Z_K (element a*K+b, (a,b)(c,e) = (a + R^b c, b+e)).
C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXC 65536
#define GROUPS_PER_N 6

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int GM = 1, GK = 1;
static int pw[MAXN];

static void set_group(int M, int K, int R) {
    GM = M;
    GK = K;
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, e = y % GK;
    return ((a + pw[b] * c) % GM) * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int t = (int)(((long long)pw[nb] * a) % GM);
    return ((GM - t) % GM) * GK + nb;
}

static int N_, D_, d_;
static int S[MAXD], Si[MAXD];
static int dist_[2 * MAXN];
static int q_[2 * MAXN];

static int bfs_all(int src) {
    int V = 2 * N_;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int h = 0, t = 0;
    q_[t++] = src;
    dist_[src] = 0;
    while (h < t) {
        int v = q_[h++];
        int dv = dist_[v];
        if (dv >= D_) continue;
        for (int i = 0; i < d_; i++) {
            int w = (v < N_) ? N_ + gmul(v, S[i]) : gmul(v - N_, Si[i]);
            if (dist_[w] < 0) {
                dist_[w] = dv + 1;
                q_[t++] = w;
            }
        }
    }
    return t == V;
}

static int ck[MAXC], cr[MAXC];

static int build_cands(int N) {
    int nc = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m == 1) {
            if (nc < MAXC) { ck[nc] = k; cr[nc] = 0; nc++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nc < MAXC) { ck[nc] = k; cr[nc] = r; nc++; }
        }
    }
    return nc;
}

int main(int argc, char **argv) {
    int ch;
    while ((ch = getchar()) != EOF) {}
    if (argc < 7) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo < d) lo = d;

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 5; i++) rnd64();

    clock_t c0 = clock();
    d_ = d;
    D_ = D;

    int bestN = 0, bM = 0, bK = 0, bR = 0;
    int bS[MAXD];
    int T = 200;
    int timeup = 0;

    while (!timeup && bestN < hi) {
        if ((double)(clock() - c0) / CLOCKS_PER_SEC > budget) break;
        int any = 0;
        int startN = (lo > bestN + 1) ? lo : bestN + 1;
        if (startN > hi) break;
        for (int N = startN; N <= hi && !timeup; N++) {
            if (N < d) continue;
            int nc = build_cands(N);
            for (int i = nc - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tk = ck[i]; ck[i] = ck[j]; ck[j] = tk;
                int tr = cr[i]; cr[i] = cr[j]; cr[j] = tr;
            }
            int found = 0;
            int lim = nc < GROUPS_PER_N ? nc : GROUPS_PER_N;
            for (int g = 0; g < lim && !found && !timeup; g++) {
                int K = ck[g], R = cr[g];
                int M = N / K;
                set_group(M, K, R);
                N_ = N;
                for (int tr = 0; tr < T && !found; tr++) {
                    if ((double)(clock() - c0) / CLOCKS_PER_SEC > budget) { timeup = 1; break; }
                    for (int i = 0; i < d; i++) {
                        int x, ok;
                        do {
                            x = rndint(N);
                            ok = 1;
                            for (int j = 0; j < i; j++) if (S[j] == x) { ok = 0; break; }
                        } while (!ok);
                        S[i] = x;
                    }
                    for (int i = 0; i < d; i++) Si[i] = ginv(S[i]);
                    if (bfs_all(0) && bfs_all(N)) {
                        found = 1;
                        any = 1;
                        bestN = N; bM = M; bK = K; bR = R;
                        for (int i = 0; i < d; i++) bS[i] = S[i];
                    }
                }
            }
        }
        if (!any) T *= 3;
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    set_group(bM, bK, bR);
    N_ = bestN;
    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + gmul(x, bS[i]));
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases from the parent program.
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of the whole graph."""
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Build: bi-Cayley group search (C), then structured base and cover growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    def grow_and_consider(n, e, end):
        n2, e2 = _grow(n, e, d, D, end, rng, attempts=16)
        consider(n2, e2)

    # Stage 1 (new family): bi-Cayley graphs over non-abelian and cyclic groups, searched in C.
    if D >= 2 and d >= 2:
        lo = max(d, best_n // 2 + 1)
        hi = lib.moore_bound(d, D) // 2
        if hi >= lo:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, 0.5 * time_limit, lo, hi],
                                timeout=0.7 * time_limit)
                n, e = lib.parse_graph_text(out)
                if n >= 2 and lib.is_valid(n, e, d, D):
                    consider(n, e)
                    grow_and_consider(n, e, start + 0.65 * time_limit)
            except (RuntimeError, ValueError):
                pass

    # Stage 2: structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            grow_and_consider(n0, e0, start + 0.75 * time_limit)

    # Stage 3: spend remaining time growing the best valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        grow_and_consider(best_n, best_e, deadline)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
