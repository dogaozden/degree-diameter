import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Voltage-lift search. The graph is a lift of a bipartite base multigraph with
   B vertices per side (d darts out of each base vertex) over a group G of order
   M*K (semidirect Z_M x| Z_K, element code a*K+b). Dart e = (i, j, v) joins
   a(i,x) to b(j, x*v). Lift vertices a(i,x) = i*G+x, b(j,y) = B*G+j*G+y.
   The lift is invariant under left multiplication, so the diameter is <= D iff
   BFS from one identity vertex per base vertex reaches everything within D.
   Simulated annealing over voltages and base switches minimises the number of
   unreached (source, vertex) pairs. */

#define MAXE 512
#define MAXB 32

static int d, D, B, M, K, R, G, N, E;
static int *mt, *iv, *pw;
static int dI[MAXE], dJ[MAXE], dV[MAXE];
static int sI[MAXE], sJ[MAXE], sV[MAXE];
static int inA[MAXE], inB[MAXE];
static int *vis, *que;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double runi(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    int na = (int)(((long long)a + (long long)pw[b] * c) % M);
    return na * K + (b + e) % K;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int na = (int)(((long long)M - ((long long)pw[nb] * a) % M) % M);
    return na * K + nb;
}

static void build_group(void) {
    pw = malloc(sizeof(int) * K);
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)(((long long)pw[b - 1] * R) % M);
    mt = malloc(sizeof(int) * G * G);
    iv = malloc(sizeof(int) * G);
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) mt[x * G + y] = gmul(x, y);
        iv[x] = ginv(x);
    }
}

/* True if dart e has the same base edge and voltage as another dart. */
static int conflict(int e) {
    for (int f = 0; f < E; f++)
        if (f != e && dI[f] == dI[e] && dJ[f] == dJ[e] && dV[f] == dV[e]) return 1;
    return 0;
}

static void rebuild(void) {
    int ca[MAXB], cb[MAXB];
    memset(ca, 0, sizeof ca);
    memset(cb, 0, sizeof cb);
    for (int e = 0; e < E; e++) {
        int i = dI[e], j = dJ[e];
        inA[i * d + ca[i]] = e;
        ca[i]++;
        inB[j * d + cb[j]] = e;
        cb[j]++;
    }
}

static void save_state(void) {
    memcpy(sI, dI, sizeof(int) * E);
    memcpy(sJ, dJ, sizeof(int) * E);
    memcpy(sV, dV, sizeof(int) * E);
}

static void restore_state(void) {
    memcpy(dI, sI, sizeof(int) * E);
    memcpy(dJ, sJ, sizeof(int) * E);
    memcpy(dV, sV, sizeof(int) * E);
    rebuild();
}

static int reach_within(int src) {
    int head = 0, tail = 0, dep = 0;
    int BG = B * G;
    stamp++;
    vis[src] = stamp;
    que[tail++] = src;
    while (head < tail && dep < D) {
        int end = tail;
        while (head < end) {
            int u = que[head++];
            if (u < BG) {
                int i = u / G, x = u - i * G;
                for (int t = 0; t < d; t++) {
                    int e = inA[i * d + t];
                    int w = BG + dJ[e] * G + mt[x * G + dV[e]];
                    if (vis[w] != stamp) {
                        vis[w] = stamp;
                        que[tail++] = w;
                    }
                }
            } else {
                int q = u - BG;
                int j = q / G, y = q - j * G;
                for (int t = 0; t < d; t++) {
                    int e = inB[j * d + t];
                    int w = dI[e] * G + mt[y * G + iv[dV[e]]];
                    if (vis[w] != stamp) {
                        vis[w] = stamp;
                        que[tail++] = w;
                    }
                }
            }
        }
        dep++;
    }
    return tail;
}

static int cost(void) {
    int c = 0;
    for (int i = 0; i < B; i++) c += N - reach_within(i * G);
    for (int j = 0; j < B; j++) c += N - reach_within(B * G + j * G);
    return c;
}

static int init_structure(void) {
    int perm[MAXB];
    int e = 0;
    for (int s = 0; s < d; s++) {
        for (int i = 0; i < B; i++) perm[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int k = rint_(i + 1);
            int t = perm[i];
            perm[i] = perm[k];
            perm[k] = t;
        }
        for (int i = 0; i < B; i++) {
            dI[e] = i;
            dJ[e] = perm[i];
            dV[e] = rint_(G);
            e++;
        }
    }
    for (int tries = 0; tries < 100000; tries++) {
        int bad = 0;
        for (int f = 0; f < E; f++) {
            if (conflict(f)) {
                dV[f] = rint_(G);
                bad = 1;
            }
        }
        if (!bad) return 1;
    }
    return 0;
}

/* Propose a change in place. Returns 0 if the proposal is trivial or invalid. */
static int propose(void) {
    if (B > 1 && rint_(100) < 30) {
        int e = rint_(E), f = rint_(E);
        if (e == f || dJ[e] == dJ[f]) return 0;
        int t = dJ[e];
        dJ[e] = dJ[f];
        dJ[f] = t;
        if (conflict(e) || conflict(f)) return 0;
        return 1;
    } else {
        int e = rint_(E);
        int nv = rint_(G);
        if (nv == dV[e]) return 0;
        dV[e] = nv;
        if (conflict(e)) return 0;
        return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: d D seed time B M K R\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    B = atoi(argv[5]);
    M = atoi(argv[6]);
    K = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || D < 1 || B < 1 || B > MAXB || M < 1 || K < 1) {
        printf("0 0\n");
        return 0;
    }
    G = M * K;
    E = B * d;
    if (E > MAXE || G < 1 || G > 2000) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * B * G;
    rs = 88172645463325252ULL ^ (seed * 0x9E3779B97F4A7C15ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    build_group();
    vis = calloc(N + 1, sizeof(int));
    que = malloc(sizeof(int) * (N + 1));

    if (!init_structure()) {
        printf("0 0\n");
        return 0;
    }
    rebuild();
    int cur = cost();

    double t_end = cpu() + tl;
    double T0 = 2.0, T = T0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 63) == 0 && cpu() > t_end) break;
        it++;
        save_state();
        if (!propose()) {
            restore_state();
            continue;
        }
        rebuild();
        int nc = cost();
        int delta = nc - cur;
        if (delta <= 0 || runi() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            restore_state();
        }
        T *= 0.9999;
        if (T < 0.2) T = T0;
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", N, E * G);
    for (int e = 0; e < E; e++) {
        for (int x = 0; x < G; x++) {
            int a = dI[e] * G + x;
            int b = B * G + dJ[e] * G + mt[x * G + dV[e]];
            printf("%d %d\n", a, b);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases (projective plane, generalized quadrangle).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
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
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
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


def _local_kill(n, adj, k, rng):
    """Pick k vertices forming a connected cluster (BFS-like from a random seed vertex)."""
    v = rng.randrange(n)
    kill = {v}
    frontier = [v]
    while len(kill) < k and frontier:
        x = frontier.pop(rng.randrange(len(frontier)))
        nb = list(adj[x])
        rng.shuffle(nb)
        for u in nb:
            if len(kill) >= k:
                break
            if u not in kill:
                kill.add(u)
                frontier.append(u)
    while len(kill) < k:
        kill.add(rng.randrange(n))
    return kill


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        if rng.random() < 0.6:
            full_adj = _to_sets(cur_n, cur_e)
            kill = _local_kill(cur_n, full_adj, k, rng)
        else:
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


# ----------------------------------------------------------------------------
# Voltage-lift search (main new construction).
#
# A lift of a base bipartite multigraph with nb vertices per side over a group
# of order G = M*K gives 2*nb*G vertices. The C engine anneals the voltages and
# base wiring; a zero-cost state is a valid graph of that order.
# ----------------------------------------------------------------------------

def _lift_configs(d, lo, hi, rng):
    """Configs (N, nb, M, K, R) with lo < N <= hi and N = 2*nb*M*K, cyclic group first."""
    out = []
    for nb in range(1, 7):
        for G in range(max(d, lo // (2 * nb) + 1), hi // (2 * nb) + 1):
            N = 2 * nb * G
            if not (lo < N <= hi) or G * G > 1_000_000:
                continue
            extra = []
            for K in range(2, G):
                if G % K:
                    continue
                M = G // K
                if M < 2:
                    continue
                rs = [r for r in range(2, M) if math.gcd(r, M) == 1 and pow(r, K, M) == 1]
                rng.shuffle(rs)
                extra += [(M, K, r) for r in rs[:2]]
            rng.shuffle(extra)
            opts = [(G, 1, 1)] + extra[:5]
            out += [(N, nb, M, K, R) for M, K, R in opts]
    rng.shuffle(out)
    out.sort(key=lambda c: c[0])
    return out


def _lift_search(d, D, seed, rng, get_best, consider, deadline):
    """Try lift orders just above the current best, with short C runs per configuration."""
    tried = set()
    attempt = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        lo = get_best()
        cands = [c for c in _lift_configs(d, lo, lo + 60, rng) if c not in tried]
        if not cands:
            break
        cfg = cands[0]
        tried.add(cfg)
        _, nb, M, K, R = cfg
        slice_t = min(4.0, remaining - 1.0)
        attempt += 1
        args = [d, D, seed * 1000 + attempt, round(slice_t, 2), nb, M, K, R]
        try:
            out = lib.run_c(C_SOURCE, args, timeout=slice_t + 10.0)
        except RuntimeError:
            continue
        nums = out.split()
        if len(nums) >= 2 and int(nums[0]) > 0:
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Short structured start (generalized quadrangle or projective plane), grown cheaply.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    # Main stage: voltage-lift annealing for orders above the current best.
    if D >= 2 and d >= 2:
        _lift_search(d, D, seed, rng, lambda: best_n, consider, start + 0.55 * time_limit)

    # Polish the best graph found so far with kill-repair-regrow.
    polish_end = start + 0.88 * time_limit
    if D >= 2 and time.monotonic() < polish_end:
        _lns(best_n, list(best_e), d, D, polish_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
