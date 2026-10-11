import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold stage: bi-Cayley (bipartite group) lifts searched in C.
#
# Group G of order N (semidirect Z_M x| Z_K, element (a,b) coded a*K+b, identity 0).
# Connection set S of size d with e in S. The graph has vertices (0,x) and (1,y)
# for x,y in G, and edges (0,x)-(1,x*s) for s in S. It is d-regular and bipartite.
# Left multiplication is an automorphism, so the diameter is decided by two BFS
# runs, from (0,e) and (1,e). The C annealer minimises the number of unreached
# vertices within distance D. A zero-cost set gives a valid graph on 2N vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1600
#define MAXDEG 64
#define STALE_LIMIT 20000
#define TEMP 1.2

static int N, DEG, DIAM, MG, KG, RG;
static int *TAB;
static int *INVT;
static int S[MAXDEG], SI[MAXDEG];
static int *vstamp;
static int *queue;
static int stampc = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int irand(int n) { return (int)(rnd64() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int build_group(void) {
    int i, x, y;
    int *pw;
    if (MG < 1 || KG < 1 || RG < 0 || N != MG * KG || N > MAXG) return 0;
    if (MG > 1 && gcd_int(RG, MG) != 1) return 0;
    pw = (int *)malloc(sizeof(int) * (size_t)KG);
    if (!pw) return 0;
    pw[0] = 1 % MG;
    for (i = 1; i < KG; i++) pw[i] = (int)(((long long)pw[i - 1] * RG) % MG);
    if ((((long long)pw[KG - 1]) * RG) % MG != 1 % MG) {
        free(pw);
        return 0;
    }
    TAB = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    INVT = (int *)malloc(sizeof(int) * (size_t)N);
    if (!TAB || !INVT) {
        free(pw);
        return 0;
    }
    for (x = 0; x < N; x++) {
        int a = x / KG, b = x % KG;
        for (y = 0; y < N; y++) {
            int c = y / KG, e = y % KG;
            int first = (int)(((long long)a + ((long long)pw[b] * c) % MG) % MG);
            TAB[(size_t)x * N + y] = first * KG + (b + e) % KG;
        }
    }
    free(pw);
    for (x = 0; x < N; x++) {
        INVT[x] = -1;
        for (y = 0; y < N; y++) {
            if (TAB[(size_t)x * N + y] == 0) {
                INVT[x] = y;
                break;
            }
        }
        if (INVT[x] < 0) return 0;
    }
    return 1;
}

/* Number of vertices within distance DIAM of src. */
static int bfs_reached(int src) {
    int head = 0, tail = 0, depth = 0, cnt, i;
    stampc++;
    queue[tail++] = src;
    vstamp[src] = stampc;
    cnt = 1;
    while (depth < DIAM && head < tail) {
        int end = tail;
        while (head < end) {
            int v = queue[head++];
            int w;
            if (v < N) {
                const int *row = TAB + (size_t)v * N;
                for (i = 0; i < DEG; i++) {
                    w = N + row[S[i]];
                    if (vstamp[w] != stampc) {
                        vstamp[w] = stampc;
                        queue[tail++] = w;
                        cnt++;
                    }
                }
            } else {
                const int *row = TAB + (size_t)(v - N) * N;
                for (i = 0; i < DEG; i++) {
                    w = row[SI[i]];
                    if (vstamp[w] != stampc) {
                        vstamp[w] = stampc;
                        queue[tail++] = w;
                        cnt++;
                    }
                }
            }
        }
        depth++;
    }
    return cnt;
}

static int cost_of(void) {
    int a = bfs_reached(0);
    int b = bfs_reached(N);
    return (2 * N - a) + (2 * N - b);
}

static void set_si(void) {
    int i;
    for (i = 0; i < DEG; i++) SI[i] = INVT[S[i]];
}

/* True if v equals S[j] for some j < lim with j != skip. */
static int dup_in(int v, int lim, int skip) {
    int j;
    for (j = 0; j < lim; j++) {
        if (j != skip && S[j] == v) return 1;
    }
    return 0;
}

static void random_set(void) {
    int i;
    S[0] = 0;
    for (i = 1; i < DEG; i++) {
        int v;
        do {
            v = irand(N);
        } while (dup_in(v, i, -1));
        S[i] = v;
    }
}

static void output_graph(void) {
    int x, i;
    printf("%d %d\n", 2 * N, N * DEG);
    for (x = 0; x < N; x++) {
        const int *row = TAB + (size_t)x * N;
        for (i = 0; i < DEG; i++) printf("%d %d\n", x, N + row[S[i]]);
    }
}

int main(int argc, char **argv) {
    uint64_t seed;
    double budget, limit;
    long iter = 0;
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    seed = (uint64_t)strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    MG = atoi(argv[5]);
    KG = atoi(argv[6]);
    RG = atoi(argv[7]);
    N = MG * KG;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x51ED27A3ULL;
    if (rs == 0) rs = 1;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 2 || N < DEG || N > MAXG || !build_group()) {
        printf("0 0\n");
        return 0;
    }
    vstamp = (int *)calloc((size_t)2 * N, sizeof(int));
    queue = (int *)malloc(sizeof(int) * (size_t)2 * N);
    if (!vstamp || !queue) {
        printf("0 0\n");
        return 0;
    }
    limit = cpu_now() + budget;
    while (cpu_now() < limit) {
        int cur, best, i;
        long stale = 0;
        random_set();
        set_si();
        cur = cost_of();
        best = cur;
        while (cur > 0) {
            int old, nv, c;
            if ((iter++ & 255) == 0 && cpu_now() > limit) break;
            i = 1 + irand(DEG - 1);
            old = S[i];
            do {
                nv = irand(N);
            } while (dup_in(nv, DEG, i));
            S[i] = nv;
            SI[i] = INVT[nv];
            c = cost_of();
            if (c <= cur || urand() < exp(-(double)(c - cur) / TEMP)) {
                cur = c;
                if (cur < best) {
                    best = cur;
                    stale = 0;
                } else {
                    stale++;
                }
            } else {
                S[i] = old;
                SI[i] = INVT[old];
                stale++;
            }
            if (stale > STALE_LIMIT) break;
        }
        if (cur == 0) {
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


def _group_options(N, rng):
    """Candidate (M, K, R) with group order N = M*K: cyclic, plus semidirect Z_M x| Z_K."""
    opts = [(N, 1, 1)]
    for K in range(2, 13):
        if N % K:
            continue
        M = N // K
        if M < 2:
            continue
        units = [r for r in range(1, M)
                 if math.gcd(r, M) == 1 and pow(r, K, M) == 1 % M]
        rng.shuffle(units)
        for r in units[:2]:
            opts.append((M, K, r))
    return opts


def _bicayley_stage(d, D, seed, stage_end, state, consider, rng):
    """Sweep group orders N upward; for each, try bi-Cayley lifts found by the C annealer."""
    hi = min(lib.moore_bound(d, D) // 2, 1500)
    N = max(state["n"] // 2 + 1, d + 1)
    fails = 0
    call = 0
    while N <= hi and fails < 8:
        if time.monotonic() > stage_end - 1.0:
            return
        found = False
        for M, K, R in _group_options(N, rng):
            remaining = stage_end - time.monotonic()
            if remaining < 1.0:
                return
            per = min(2.0, max(0.6, remaining / 20.0))
            call += 1
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed * 7919 + call, f"{per:.3f}", M, K, R],
                                timeout=per + 20.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > state["n"] and lib.is_valid(n, e, d, D):
                consider(n, e)
                found = True
                break
        fails = 0 if found else fails + 1
        N = max(N + 1, state["n"] // 2 + 1)


# ----------------------------------------------------------------------------
# Parent pipeline (structured bases, twin duplication, LNS, repair).
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


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
        k = rng.choice((1, 1, 2, 3))
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _repair(d, D, n, edges, deadline, rng, consider):
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _parent_build(d, D, seed, time_limit):
    """Previous pure-Python pipeline, run on the remaining time budget."""
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.75 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point: bi-Cayley search first (bold), then the parent pipeline as a
# safety net on the remaining time. The best valid graph is always returned.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    state = {"n": 0, "e": []}
    n0, e0 = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    state["n"], state["e"] = n0, list(e0)

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, list(e)

    rng = random.Random(seed)
    if d >= 2 and D >= 2:
        try:
            _bicayley_stage(d, D, seed, start + 0.55 * time_limit, state, consider, rng)
        except Exception:
            pass

    remaining = start + 0.86 * time_limit - time.monotonic()
    if remaining > 1.0:
        try:
            n2, e2 = _parent_build(d, D, seed, remaining)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(state["n"], state["e"], d, D):
        return lib.haar_graph(d, range(d))
    return state["n"], list(state["e"])
