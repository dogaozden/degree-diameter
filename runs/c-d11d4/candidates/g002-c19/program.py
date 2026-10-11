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

typedef struct { int n; int *col, *deg, *adj; } State;

static int d, D, NMAX, W, N;
static int *col, *deg, *adj, *tmpl;
static u64 *bufA, *bufB;
static u64 rs = 88172645463325252ULL;
static double budget_s;
static struct timespec t_start;

static u64 rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return (double)(t.tv_sec - t_start.tv_sec) + 1e-9 * (double)(t.tv_nsec - t_start.tv_nsec);
}

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void st_alloc(State *s) {
    s->n = 0;
    s->col = malloc(sizeof(int) * NMAX);
    s->deg = malloc(sizeof(int) * NMAX);
    s->adj = malloc(sizeof(int) * (size_t)NMAX * d);
}
static void st_save(State *s) {
    s->n = N;
    memcpy(s->col, col, sizeof(int) * N);
    memcpy(s->deg, deg, sizeof(int) * N);
    memcpy(s->adj, adj, sizeof(int) * (size_t)N * d);
}
static void st_load(const State *s) {
    N = s->n;
    memcpy(col, s->col, sizeof(int) * N);
    memcpy(deg, s->deg, sizeof(int) * N);
    memcpy(adj, s->adj, sizeof(int) * (size_t)N * d);
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long long eval_bad(void) {
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(u64) * W);
            for (int i = 0; i < deg[v]; i++) {
                const u64 *t = cur + (size_t)adj[v * d + i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const u64 *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) tot += popc(s[w]);
    }
    return ((long long)N * N - tot) / 2;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u * d + i] == v) return 1;
    return 0;
}
static void remove_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u * d + i] == v) {
            adj[u * d + i] = adj[u * d + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void add_edge(int u, int v) {
    adj[u * d + deg[u]++] = v;
    adj[v * d + deg[v]++] = u;
}
static void remove_edge(int u, int v) {
    remove_from(u, v);
    remove_from(v, u);
}

/* Random vertex of colour c with spare degree, not equal to or adjacent to a. */
static int pick_partner(int a, int c) {
    int cnt = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == c && deg[v] < d && v != a && !has_edge(a, v)) tmpl[cnt++] = v;
    if (cnt == 0) return -1;
    return tmpl[rndint(cnt)];
}

/* Add one vertex joined to d vertices of the opposite colour, stealing edges when needed,
   then fill spare degree greedily. Bipartiteness is kept. */
static void add_vertex(void) {
    int c = rndint(2);
    int x = N++;
    col[x] = c;
    deg[x] = 0;
    int cnt = 0;
    for (int v = 0; v < x; v++) if (col[v] == 1 - c) tmpl[cnt++] = v;
    int want = d < cnt ? d : cnt;
    for (int k = 0; k < want; k++) {
        int j = k + rndint(cnt - k);
        int t = tmpl[k]; tmpl[k] = tmpl[j]; tmpl[j] = t;
        int y = tmpl[k];
        if (deg[y] >= d) {
            int z = adj[y * d + rndint(deg[y])];
            remove_edge(y, z);
        }
        add_edge(x, y);
    }
    for (int a = 0; a < N; a++) {
        if (a == x || col[a] != c || deg[a] >= d) continue;
        int b = pick_partner(a, 1 - c);
        if (b >= 0) add_edge(a, b);
    }
}

/* Remove a random edge and reconnect one endpoint to a random deficient vertex. */
static int rewire_move(void) {
    int u = rndint(N);
    if (deg[u] == 0) return 0;
    int v = adj[u * d + rndint(deg[u])];
    remove_edge(u, v);
    int anchor = (rnd() & 1) ? u : v;
    int p = pick_partner(anchor, 1 - col[anchor]);
    if (p < 0) {
        add_edge(u, v);
        return 0;
    }
    add_edge(anchor, p);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    timespec_get(&t_start, TIME_UTC);
    if (d < 2 || D < 2) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) { printf("0 0\n"); return 0; }
    NMAX = n0 + 400;
    W = (NMAX + 63) / 64;
    col = malloc(sizeof(int) * NMAX);
    deg = calloc(NMAX, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)NMAX * d);
    tmpl = malloc(sizeof(int) * NMAX);
    bufA = malloc(sizeof(u64) * (size_t)NMAX * W);
    bufB = malloc(sizeof(u64) * (size_t)NMAX * W);
    int *eu = malloc(sizeof(int) * (m0 + 1));
    int *ev = malloc(sizeof(int) * (m0 + 1));

    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        int a = eu[i], b = ev[i];
        if (a < 0 || a >= n0 || b < 0 || b >= n0 || a == b || deg[a] >= d || deg[b] >= d ||
            has_edge(a, b)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(a, b);
    }

    N = n0;
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        tmpl[qt++] = s;
        while (qh < qt) {
            int u = tmpl[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u * d + i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    tmpl[qt++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    State best, undo;
    st_alloc(&best);
    st_alloc(&undo);
    long long cb = eval_bad();
    int have_valid = 0;
    if (cb == 0) { st_save(&best); have_valid = 1; }
    long long bestcb = cb;
    long stall = 0;
    const long STALL = 4000;
    const double T0 = 8.0, T1 = 0.3;

    while (elapsed() < budget_s) {
        if (cb == 0) {
            st_save(&best);
            have_valid = 1;
            if (N >= NMAX) break;
            add_vertex();
            cb = eval_bad();
            bestcb = cb;
            stall = 0;
            continue;
        }
        st_save(&undo);
        if (!rewire_move()) continue;
        long long nb = eval_bad();
        long long delta = nb - cb;
        double T = T0 * pow(T1 / T0, (double)stall / (double)STALL);
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cb = nb;
        } else {
            st_load(&undo);
        }
        if (cb < bestcb) { bestcb = cb; stall = 0; }
        else stall++;
        if (stall > STALL && have_valid) {
            st_load(&best);
            cb = eval_bad();
            bestcb = cb;
            stall = 0;
        }
    }

    if (cb == 0) { st_save(&best); have_valid = 1; }
    if (!have_valid) { printf("0 0\n"); return 0; }
    long m = 0;
    for (int v = 0; v < best.n; v++) if (best.col[v] == 0) m += best.deg[v];
    printf("%d %ld\n", best.n, m);
    for (int v = 0; v < best.n; v++) {
        if (best.col[v] != 0) continue;
        for (int i = 0; i < best.deg[v]; i++)
            printf("%d %d\n", v, best.adj[v * d + i]);
    }
    return 0;
}
"""


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, order 2(q+1)(q^2+1).
    """
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


def _gq_qs(d, count):
    """Largest prime powers q (q <= 16, q + 1 <= d), up to `count` of them, largest first."""
    return [q for q in range(d - 1, 1, -1) if q <= 16 and lib.is_prime_power(q)][:count]


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
    """Greedy set cover of `full` by at most d candidate vertices, or None."""
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


def _cover_ls(cands, ball, full, d, rng, iters):
    """Swap-based local search for a cover of `full` by at most d candidates, or None."""
    pool = list(cands)
    if not pool:
        return None

    def unc(cov):
        return (full & ~cov).bit_count()

    chosen = []
    covered = 0
    for _ in range(d):
        best, bg = None, -1
        for s in rng.sample(pool, min(len(pool), 80)):
            g = (ball[s] & ~covered).bit_count()
            if g > bg:
                bg, best = g, s
        if best is None:
            break
        chosen.append(best)
        covered |= ball[best]
    cur = unc(covered)
    for _ in range(iters):
        if cur == 0:
            break
        if len(chosen) < d:
            i, rest = None, covered
        else:
            i = rng.randrange(len(chosen))
            rest = 0
            for j, s in enumerate(chosen):
                if j != i:
                    rest |= ball[s]
        best, bu = None, None
        for c in rng.sample(pool, min(len(pool), 60)):
            if c in chosen:
                continue
            u = unc(rest | ball[c])
            if bu is None or u < bu:
                bu, best = u, c
        if best is None:
            continue
        if i is None:
            chosen.append(best)
        elif bu <= cur:
            chosen[i] = best
        else:
            continue
        covered = rest | ball[best]
        cur = unc(covered)
    return chosen if cur == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of each other."""
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
                if attempt < 30:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 150)
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
    """Extend by cover vertices, then saturate edges. Both preserve the diameter bound."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Stage 1: algebraic starts, grown by cover extension in a bounded time slice.
    ext_deadline = start + 0.3 * time_limit
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    if D >= 4:
        qs = _gq_qs(d, 2)
        if qs:
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(qs):
                gn, ge = _gq_w(q)
                consider(gn, ge)
                slice_end = t0 + span * (i + 1) / len(qs)
                n2, e2 = _grow(gn, ge, d, D, slice_end, rng)
                consider(n2, e2)

    # Stage 2: simulated annealing in C that repairs bad pairs and adds vertices
    # from valid states. Starts from the best graph found so far.
    c_deadline = start + 0.9 * time_limit
    timeout = c_deadline - time.monotonic()
    budget = timeout - 2.0
    if best_n < lib.moore_bound(d, D) and budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=timeout)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
