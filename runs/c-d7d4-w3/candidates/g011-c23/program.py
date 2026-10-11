import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite degree-preserving annealing that minimises the number of
# vertex pairs at distance > D. Input and output use the lib text format.
# Output is always the best edge set seen (cost 0 means valid).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXM (MAXN * MAXD / 2)

static int n, d, D, m;
static int deg[MAXN];
static int adjv[MAXN][MAXD];
static int col[MAXN];
static int eu[MAXM], ev[MAXM];
static int beu[MAXM], bev[MAXM], bm;
static int qbuf[MAXN], dep[MAXN];
static unsigned seen[MAXN];
static unsigned stamp = 0;
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (unsigned long long)k); }

static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int i = 0; i < deg[v]; i++)
        if (adjv[v][i] == old) { adjv[v][i] = nw; return; }
}

/* Edge i = (a,b) with a on side 0, j = (c,e). Result: i = (a,e), j = (c,b).
   Applying it again to the result restores the original pair. */
static void sw(int i, int j) {
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    repl(a, b, e);
    repl(b, a, c);
    repl(c, e, b);
    repl(e, c, a);
    eu[i] = a; ev[i] = e;
    eu[j] = c; ev[j] = b;
}

static void del_edge_idx(int i) {
    int a = eu[i], b = ev[i];
    for (int k = 0; k < deg[a]; k++)
        if (adjv[a][k] == b) { adjv[a][k] = adjv[a][deg[a] - 1]; deg[a]--; break; }
    for (int k = 0; k < deg[b]; k++)
        if (adjv[b][k] == a) { adjv[b][k] = adjv[b][deg[b] - 1]; deg[b]--; break; }
    m--;
    eu[i] = eu[m];
    ev[i] = ev[m];
}

static long cost_full(void) {
    long bad = 0;
    for (int s = 0; s < n; s++) {
        if (++stamp == 0) { memset(seen, 0, sizeof(seen)); stamp = 1; }
        int h = 0, t = 0, cnt = 1;
        qbuf[t++] = s;
        seen[s] = stamp;
        dep[s] = 0;
        while (h < t) {
            int v = qbuf[h++];
            if (dep[v] >= D) continue;
            for (int k = 0; k < deg[v]; k++) {
                int u = adjv[v][k];
                if (seen[u] != stamp) {
                    seen[u] = stamp;
                    dep[u] = dep[v] + 1;
                    qbuf[t++] = u;
                    cnt++;
                }
            }
        }
        bad += n - cnt;
    }
    return bad;
}

static int bip(void) {
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int h = 0, t = 0;
        col[s] = 0;
        qbuf[t++] = s;
        while (h < t) {
            int v = qbuf[h++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjv[v][k];
                if (col[u] == -1) { col[u] = 1 - col[v]; qbuf[t++] = u; }
                else if (col[u] == col[v]) return 0;
            }
        }
    }
    return 1;
}

static void fix_degrees(void) {
    for (int v = 0; v < n; v++) {
        while (deg[v] > d) {
            int u = adjv[v][rndi(deg[v])];
            int idx = -1;
            for (int i = 0; i < m; i++)
                if ((eu[i] == v && ev[i] == u) || (eu[i] == u && ev[i] == v)) { idx = i; break; }
            if (idx < 0) break;
            del_edge_idx(idx);
        }
    }
}

/* Add random edges between deficient opposite-side vertices. Adding never raises the cost. */
static int saturate(int tries) {
    int added = 0;
    for (int t = 0; t < tries && m < MAXM; t++) {
        int a = rndi(n), b = rndi(n);
        if (col[a] == 1 && col[b] == 0) { int tmp = a; a = b; b = tmp; }
        if (col[a] != 0 || col[b] != 1) continue;
        if (deg[a] >= d || deg[b] >= d) continue;
        if (has_edge(a, b)) continue;
        eu[m] = a; ev[m] = b; m++;
        adjv[a][deg[a]++] = b;
        adjv[b][deg[b]++] = a;
        added++;
    }
    return added;
}

static void save_best(void) {
    bm = m;
    memcpy(beu, eu, sizeof(int) * (size_t)m);
    memcpy(bev, ev, sizeof(int) * (size_t)m);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);

    int n_in, m_in;
    if (scanf("%d %d", &n_in, &m_in) != 2) { printf("0 0\n"); return 0; }
    n = n_in;
    if (n <= 0 || n > MAXN || d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    m = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= MAXD || deg[v] >= MAXD || m >= MAXM) continue;
        if (has_edge(u, v)) continue;
        eu[m] = u; ev[m] = v; m++;
        adjv[u][deg[u]++] = v;
        adjv[v][deg[v]++] = u;
    }
    if (!bip()) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++)
        if (col[eu[i]] == 1) { int t = eu[i]; eu[i] = ev[i]; ev[i] = t; }

    fix_degrees();
    saturate(40 * n);
    long cur = cost_full();
    long best = cur;
    save_best();

    double t0 = wall();
    double T0 = 0.6, T = T0;
    long it = 0, last_imp = 0;
    while (best > 0 && m >= 2 && wall() - t0 < budget) {
        it++;
        int i = rndi(m), j = rndi(m);
        if (i == j) continue;
        int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
        if (a == c || b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        sw(i, j);
        long nc = cost_full();
        long dl = nc - cur;
        if (dl <= 0 || rndf() < exp(-(double)dl / T)) {
            cur = nc;
            if (saturate(8) > 0) cur = cost_full();
            if (cur < best) {
                best = cur;
                save_best();
                last_imp = it;
            }
        } else {
            sw(i, j);
        }
        T *= 0.9995;
        if (T < 0.05) T = 0.05;
        if (it - last_imp > 3000) { T = T0; last_imp = it; }
    }
    fprintf(stderr, "best %ld iters %ld\n", best, it);

    printf("%d %d\n", n, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
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


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """Dense structured graph with degree >= d, thinned later into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared graph helpers.
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
            for attempt in range(60):
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
# Thin a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Voltage lifts over small (semidirect) groups, used as C repair starts.
# ----------------------------------------------------------------------------

def _group_options(G):
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


def _lift_round(d, D, best_n, rng):
    """Random d-regular bipartite lift with more than best_n vertices, or None."""
    s = rng.choice((1, 2, 2, 3, 3, 4))
    G = best_n // (2 * s) + 1 + rng.randrange(3)
    opts = _group_options(G)
    if not opts:
        return None
    M, k, r = rng.choice(opts)
    try:
        _, mul, _ = lib.semidirect_group(M, k, r)
    except ValueError:
        return None
    darts = _random_darts(s, d, G, rng)
    return lib.group_lift(2 * s, darts, G, mul)


# ----------------------------------------------------------------------------
# Extension: add vertices to a valid graph; C repairs the degree excess and
# the diameter defects.
# ----------------------------------------------------------------------------

def _extend_round(d, D, n, e, rng):
    adj = _to_sets(n, e)
    color = _bipartition(n, adj)
    cur_n = n
    edges = list(e)
    for _ in range(rng.choice((1, 1, 2, 3))):
        c = rng.randrange(2)
        opp = [v for v in range(cur_n) if color[v] != c]
        rng.shuffle(opp)
        opp.sort(key=lambda v: len(adj[v]) >= d)  # deficient vertices first
        nb = opp[:d]
        v_new = cur_n
        cur_n += 1
        color.append(c)
        adj.append(set(nb))
        for u in nb:
            adj[u].add(v_new)
            edges.append((u, v_new))
    return cur_n, edges


def _c_repair(n, edges, d, D, budget, seed):
    """Run the C annealer. Returns (n, edges) or None. The result still needs lib.is_valid."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 6.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.88 * time_limit:
#   A  structured base (W(q) or PG(2,q)), grown, then twin/grow trials
#   B  thinned dense graph (degree reduction + vertex deletion), D >= 3
#   R  repeated C repair: lift starts or extended best graph, then regrow
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.88 * time_limit

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
        n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense graph, repeated.
    if D >= 3 and time.monotonic() < at(0.25):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re_ = raw
            while time.monotonic() < at(0.25):
                r = _deletion_trial(d, D, rn, re_, rng, at(0.25))
                if r is None:
                    break
                consider(*r)

    # Phase R: C-driven repair from lifts and extensions of the best valid graph.
    while D >= 2 and time.monotonic() < at(0.97):
        remaining = at(0.97) - time.monotonic()
        slice_ = min(4.0, remaining - 0.5)
        if slice_ < 0.8:
            break
        if rng.random() < 0.35:
            cand = _lift_round(d, D, best_n, rng)
        else:
            cand = _extend_round(d, D, best_n, best_e, rng)
        if cand is None:
            continue
        res = _c_repair(cand[0], cand[1], d, D, slice_, rng.randrange(1 << 30))
        if res is None:
            continue
        n2, e2 = res
        if lib.is_valid(n2, e2, d, D):
            consider(n2, e2)
            n3, e3 = _grow(n2, _saturate_edges(n2, e2, d, rng), d, D, at(0.97), rng)
            consider(n3, e3)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
