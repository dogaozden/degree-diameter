import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# State: a bipartite graph with max degree DG and diameter bound D. Every
# accepted state is valid (cost = 0). Moves:
#   add:  attach a new vertex to a greedy cover of one side, fill spare
#         degree, then repair the diameter with degree-preserving switches.
#   kill: delete 1-3 vertices (clustered or scattered), fill, repair,
#         then regrow with add moves.
# The best valid graph is printed at the end. Python validates it again.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1200
#define MAXDG 64
#define MAXW 20
#define ANN_ADD 600
#define ANN_KILL 300

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int nb[MAXN][MAXDG];
} State;

static int N, D, DG;
static int nbr[MAXN][MAXDG];
static int deg[MAXN];
static int col[MAXN];
static unsigned char mark[MAXN];
static uint64_t B1[MAXN][MAXW];
static uint64_t B2[MAXN][MAXW];
static int nw;
static uint64_t rng_s = 88172645463325252ULL;
static double t_end;
static State SNAP, S2, BEST;

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static int rnd(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nbr[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nbr[u][deg[u]++] = v;
    nbr[v][deg[v]++] = u;
}

static void rem_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nbr[u][i] == v) {
            nbr[u][i] = nbr[u][--deg[u]];
            return;
        }
}

static void rem_edge(int u, int v) {
    rem_one(u, v);
    rem_one(v, u);
}

/* B1[v] = bitset of vertices within distance r of v. */
static void balls(int r) {
    nw = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) B1[v][w] = 0;
        B1[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) B2[v][w] = B1[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nbr[v][i];
                for (int w = 0; w < nw; w++) B2[v][w] |= B1[u][w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < nw; w++) B1[v][w] = B2[v][w];
    }
}

/* Number of unordered pairs at distance > D. */
static int cost(void) {
    balls(D);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(B1[v][w]);
        bad += N - c;
    }
    return (int)(bad / 2);
}

static void copy_out(State *s) {
    s->n = N;
    for (int v = 0; v < N; v++) {
        s->deg[v] = deg[v];
        s->col[v] = col[v];
        memcpy(s->nb[v], nbr[v], sizeof(int) * deg[v]);
    }
}

static void copy_in(const State *s) {
    N = s->n;
    for (int v = 0; v < N; v++) {
        deg[v] = s->deg[v];
        col[v] = s->col[v];
        memcpy(nbr[v], s->nb[v], sizeof(int) * deg[v]);
    }
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int def0[MAXN], def1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= DG) continue;
        if (col[v] == 0) def0[n0++] = v;
        else def1[n1++] = v;
    }
    if (n0 == 0 || n1 == 0) return;
    long maxtries = 20L * (n0 + n1) + 100;
    for (long t = 0; t < maxtries; t++) {
        int a = def0[rnd(n0)];
        int b = def1[rnd(n1)];
        if (deg[a] < DG && deg[b] < DG && !has_edge(a, b)) add_edge(a, b);
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static int anneal(int iters) {
    static int side0[MAXN];
    int cur = cost();
    int n0 = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == 0) side0[n0++] = v;
    if (n0 < 2) return cur == 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now_s() > t_end) break;
        int a = side0[rnd(n0)];
        if (deg[a] == 0) continue;
        int b = nbr[a][rnd(deg[a])];
        int c = side0[rnd(n0)];
        if (c == a || deg[c] == 0) continue;
        int e = nbr[c][rnd(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        rem_edge(a, b);
        rem_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        int cn = cost();
        if (cn <= cur || (cn == cur + 1 && rnd01() < 0.1)) {
            cur = cn;
        } else {
            rem_edge(a, e);
            rem_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

/* Delete vertex x; the last vertex is moved into slot x. Marks follow vertices. */
static void remove_vertex(int x) {
    while (deg[x] > 0) rem_edge(x, nbr[x][deg[x] - 1]);
    int last = N - 1;
    if (x != last) {
        while (deg[last] > 0) {
            int y = nbr[last][deg[last] - 1];
            rem_edge(last, y);
            add_edge(x, y);
        }
        col[x] = col[last];
        mark[x] = mark[last];
    }
    mark[last] = 0;
    N--;
}

/* Add one vertex joined to a greedy cover of one side, then fill and repair. */
static int add_move(void) {
    static int cand[MAXN];
    if (N + 1 >= MAXN) return 0;
    int s = rnd(2);
    int v = N++;
    col[v] = 1 - s;
    deg[v] = 0;
    mark[v] = 0;
    balls(D - 1);
    int nwn = (N + 63) / 64;
    uint64_t cov[MAXW];
    for (int w = 0; w < nwn; w++) cov[w] = 0;
    int nca = 0;
    for (int u = 0; u < v; u++)
        if (col[u] == s) cand[nca++] = u;
    int chosen[MAXDG];
    int nc = 0;
    for (int k = 0; k < DG && nca > 0; k++) {
        int best = -1;
        long bestkey = -1;
        for (int i = 0; i < nca; i++) {
            int c = cand[i];
            int used = 0;
            for (int j = 0; j < nc; j++)
                if (chosen[j] == c) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < nwn; w++) g += pc64(B1[c][w] & ~cov[w]);
            long key = (long)g * 8 + rnd(8);
            if (key > bestkey) { bestkey = key; best = c; }
        }
        if (best < 0 || bestkey < 8) break;
        if (deg[best] >= DG) {
            int t = nbr[best][rnd(deg[best])];
            rem_edge(best, t);
        }
        add_edge(best, v);
        chosen[nc++] = best;
        for (int w = 0; w < nwn; w++) cov[w] |= B1[best][w];
    }
    if (nc == 0) { N--; return 0; }
    fill();
    return anneal(ANN_ADD);
}

/* Remove k vertices (clustered or scattered), fill, repair. */
static int kill_move(int k, int local) {
    int kl[8];
    int cnt = 0;
    if (N < k + 6) return 0;
    if (local) {
        int x = rnd(N);
        mark[x] = 1;
        kl[cnt++] = x;
        int tries = 0;
        while (cnt < k && tries < 60) {
            tries++;
            int y = kl[rnd(cnt)];
            if (deg[y] == 0) continue;
            int z = nbr[y][rnd(deg[y])];
            if (!mark[z]) {
                mark[z] = 1;
                kl[cnt++] = z;
            }
        }
    } else {
        while (cnt < k) {
            int z = rnd(N);
            if (!mark[z]) {
                mark[z] = 1;
                kl[cnt++] = z;
            }
        }
    }
    for (;;) {
        int id = -1;
        for (int u = 0; u < N; u++)
            if (mark[u]) { id = u; break; }
        if (id < 0) break;
        remove_vertex(id);
    }
    fill();
    return anneal(ANN_KILL);
}

static State SNAP_DUMMY;

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DG = d;
    if (DG < 1 || DG > MAXDG || D < 1) { printf("0 0\n"); return 0; }
    rng_s = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_s == 0) rng_s = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 300) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (has_edge(u, v) || deg[u] >= DG || deg[v] >= DG) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = nbr[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (cost() != 0 || budget <= 0) {
        printf("0 0\n");
        return 0;
    }

    t_end = now_s() + budget;
    copy_out(&BEST);
    int bestN = N;
    while (now_s() < t_end) {
        copy_out(&SNAP);
        if (rnd(100) < 30) {
            int k = 1 + rnd(3);
            int local = rnd(100) < 60;
            if (!kill_move(k, local)) {
                copy_in(&SNAP);
                continue;
            }
        }
        int fails = 0;
        while (fails < 3 && now_s() < t_end && N < MAXN - 4) {
            copy_out(&S2);
            if (add_move()) fails = 0;
            else {
                copy_in(&S2);
                fails++;
            }
        }
        if (N > bestN) {
            bestN = N;
            copy_out(&BEST);
        } else if (N < bestN - 3) {
            copy_in(&BEST);
        }
    }

    copy_in(&BEST);
    int em = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nbr[u][i] > u) em++;
    printf("%d %d\n", N, em);
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nbr[u][i] > u) printf("%d %d\n", u, nbr[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and growth helpers.
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _spare_matching_base(n0, e0, d, rng, keep_free):
    """Add cross-side point-line edges into spare slots, leaving keep_free points unmatched."""
    n = n0
    half = n // 2
    adj = _to_sets(n, e0)
    rounds = d - max(len(a) for a in adj)
    for _ in range(max(0, rounds)):
        order = [p for p in range(half) if len(adj[p]) < d]
        rng.shuffle(order)
        target = max(0, len(order) - keep_free)
        count = 0
        for p in order:
            if count >= target:
                break
            cands = [L for L in range(half, n) if len(adj[L]) < d and L not in adj[p]]
            if not cands:
                continue
            L = rng.choice(cands)
            adj[p].add(L)
            adj[L].add(p)
            count += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


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


# ----------------------------------------------------------------------------
# Entry point.
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

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    base_is_gq = False
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is not None:
            base_is_gq = True
        else:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.14 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Spare-slot matching on the quadrangle base, with varied free slots kept for growth.
    if base_is_gq and D >= 4:
        spare_end = start + 0.18 * time_limit
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    # Main search in C: kill, repair and regrow from the best valid graph.
    if D >= 2 and 3 <= d <= 64:
        c_deadline = start + 0.84 * time_limit
        budget = c_deadline - time.monotonic()
        if budget > 0.5:
            hard = start + 0.95 * time_limit - time.monotonic()
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=(best_n, best_e),
                                 timeout=max(0.5, hard))
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
