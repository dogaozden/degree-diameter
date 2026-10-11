import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine for Cayley-type bipartite graphs (Haar-type lifts over a group G).
#
# Vertices a_x, b_y (x, y in G). Edge a_x -- b_{x s} for s in S, |S| = d.
# The graph is bipartite, d-regular, and each side is transitive under left
# multiplication, so its diameter equals max(ecc(a_e), ecc(b_e)). The C side
# hill-climbs over S to make both eccentricities at most D.
#
# Input (via lib.run_c's stdin graph format): header "m me" with m = |G| and
# me = m*m + m, followed by pairs (x*m+y, x*y) for the multiplication table and
# pairs (m*m+y, y^-1) for inverses. Output: "FOUND" and S, or "FAIL best".
# ----------------------------------------------------------------------------

_CAY_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int m, d, Dd;
static int *mul, *invt, *Sv, *Si, *adj, *fr, *nx;
static unsigned char *seen;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }

static int in_S(int t, int upto) {
    for (int i = 0; i < upto; i++)
        if (Sv[i] == t) return 1;
    return 0;
}

static void build_adj(void) {
    for (int k = 0; k < d; k++) Si[k] = invt[Sv[k]];
    for (int x = 0; x < m; x++)
        for (int k = 0; k < d; k++)
            adj[x * d + k] = m + mul[x * m + Sv[k]];
    for (int y = 0; y < m; y++)
        for (int k = 0; k < d; k++)
            adj[(m + y) * d + k] = mul[y * m + Si[k]];
}

static int unreached(int src) {
    int n = 2 * m;
    memset(seen, 0, (size_t)n);
    seen[src] = 1;
    fr[0] = src;
    int fn = 1;
    int cnt = 1;
    for (int r = 0; r < Dd && fn > 0; r++) {
        int nn = 0;
        for (int i = 0; i < fn; i++) {
            int v = fr[i];
            for (int k = 0; k < d; k++) {
                int w = adj[v * d + k];
                if (!seen[w]) {
                    seen[w] = 1;
                    nx[nn++] = w;
                }
            }
        }
        cnt += nn;
        int *t = fr;
        fr = nx;
        nx = t;
        fn = nn;
    }
    return n - cnt;
}

static int cost(void) {
    build_adj();
    return unreached(0) + unreached(m);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    Dd = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 1ULL;
    double tl = atof(argv[4]);
    int n, me;
    if (scanf("%d %d", &n, &me) != 2) return 3;
    m = n;
    if (d < 1 || Dd < 1 || m < d + 1 || m > 4000 || me != m * m + m) {
        printf("FAIL -1\n");
        return 0;
    }
    mul = malloc(sizeof(int) * (size_t)m * (size_t)m);
    invt = malloc(sizeof(int) * (size_t)m);
    Sv = malloc(sizeof(int) * (size_t)d);
    Si = malloc(sizeof(int) * (size_t)d);
    adj = malloc(sizeof(int) * (size_t)2 * m * d);
    fr = malloc(sizeof(int) * (size_t)2 * m);
    nx = malloc(sizeof(int) * (size_t)2 * m);
    seen = malloc((size_t)2 * m);
    if (!mul || !invt || !Sv || !Si || !adj || !fr || !nx || !seen) return 4;
    for (int i = 0; i < me; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) return 5;
        if (a < m * m) mul[a] = b;
        else if (a - m * m < m) invt[a - m * m] = b;
    }

    double deadline = now() + tl;
    int best = 1 << 30;
    int found = 0;
    while (!found && now() < deadline) {
        for (int i = 0; i < d; i++) {
            int t;
            do { t = rndi(m); } while (in_S(t, i));
            Sv[i] = t;
        }
        int c = cost();
        int stagn = 0;
        while (c > 0 && stagn < 3000 && now() < deadline) {
            int i = rndi(d);
            int t;
            do { t = rndi(m); } while (in_S(t, d));
            int old = Sv[i];
            Sv[i] = t;
            int c2 = cost();
            if (c2 <= c) {
                if (c2 < c) stagn = 0;
                else stagn++;
                c = c2;
            } else {
                Sv[i] = old;
                stagn++;
            }
        }
        if (c < best) best = c;
        if (c == 0) found = 1;
    }
    if (found) {
        printf("FOUND\n");
        for (int i = 0; i < d; i++) printf("%d ", Sv[i]);
        printf("\n");
    } else {
        printf("FAIL %d\n", best);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Parent construction pipeline (proven baseline and fallback).
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
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


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
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
# New construction: Cayley-type bipartite graphs over groups of order N.
# Graph order 2N, degree d, searched by the C engine for diameter <= D.
# ----------------------------------------------------------------------------

def _groups(N, rng):
    """Up to four group structures of order N: cyclic, plus a few semidirect products Z_m x| Z_k."""
    out = [lib.cyclic_group(N)]
    cands = []
    for k in range(2, 13):
        if N % k:
            continue
        mm = N // k
        if mm < 2:
            continue
        for r in range(1, mm):
            if math.gcd(r, mm) == 1 and pow(r, k, mm) == 1 % mm:
                cands.append((mm, k, r))
    rng.shuffle(cands)
    for mm, k, r in cands[:3]:
        try:
            out.append(lib.semidirect_group(mm, k, r))
        except ValueError:
            pass
    return out


def _parse_S(text, N, d):
    tok = text.split()
    if not tok or tok[0] != "FOUND":
        return None
    try:
        S = [int(t) for t in tok[1:]]
    except ValueError:
        return None
    if len(S) != d or len(set(S)) != d or any(not 0 <= s < N for s in S):
        return None
    return S


def _cayley_stage(d, D, cur_n, deadline, seed, consider):
    """Search Cayley-type bipartite graphs of order 2N > cur_n with diameter <= D."""
    lo = max(cur_n // 2 + 1, d + 1)
    hi = min(lib.moore_bound(d, D) // 2, 600)
    if lo > hi:
        return
    rng = random.Random(seed ^ 0x5F3759DF)
    for N in range(lo, hi + 1):
        left = deadline - time.monotonic()
        if left < 0.5:
            break
        per_order = left / (hi - N + 1)
        groups = _groups(N, rng)
        per_group = per_order / len(groups)
        for _, mul, inv in groups:
            if deadline - time.monotonic() < 0.2:
                return
            tbl = [mul(x, y) for x in range(N) for y in range(N)]
            ivs = [inv(x) for x in range(N)]
            pairs = [(i, v) for i, v in enumerate(tbl)]
            pairs += [(N * N + y, ivs[y]) for y in range(N)]
            try:
                out = lib.run_c(_CAY_C, [d, D, seed + N, round(per_group, 3)],
                                stdin_graph=(N, pairs), timeout=per_group + 5.0)
            except RuntimeError:
                return
            S = _parse_S(out, N, d)
            if S is None:
                continue
            edges = [(x, N + mul(x, s)) for x in range(N) for s in S]
            consider(2 * N, edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    state = {"n": n0, "e": list(e0)}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, list(e)
            return True
        return False

    # Stage 1: proven parent pipeline (baseline and valid starting order).
    try:
        pn, pe = _parent_build(d, D, seed, 0.5 * time_limit)
        consider(pn, pe)
    except Exception:
        pass

    # Stage 2: Cayley-type bipartite search for orders above the current best.
    if D >= 2 and d >= 3:
        try:
            _cayley_stage(d, D, state["n"], start + 0.9 * time_limit, seed, consider)
        except Exception:
            pass

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, list(e)
