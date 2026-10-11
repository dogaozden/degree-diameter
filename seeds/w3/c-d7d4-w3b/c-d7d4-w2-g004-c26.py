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
#include <time.h>

#define MAXN 1100
#define MAXD 16
#define W 18

typedef uint64_t Row[W];
typedef struct {
    int n;
    int adj[MAXN][MAXD];
    int deg[MAXN];
    int side[MAXN];
} State;

static State G, ACC, BEST, SNAP;
static int DEGB, DIAM;
static Row BX[MAXN], BY[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }
static int popc64(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void save(State *s) { memcpy(s, &G, sizeof(State)); }
static void load(const State *s) { memcpy(&G, s, sizeof(State)); }

static int has_edge(int a, int b) {
    for (int j = 0; j < G.deg[a]; j++) if (G.adj[a][j] == b) return 1;
    return 0;
}
static void rep(int x, int old, int nw) {
    for (int j = 0; j < G.deg[x]; j++) if (G.adj[x][j] == old) { G.adj[x][j] = nw; return; }
}
static void unlink_(int x, int y) {
    for (int j = 0; j < G.deg[x]; j++)
        if (G.adj[x][j] == y) { G.adj[x][j] = G.adj[x][--G.deg[x]]; return; }
}
static void add_edge(int a, int b) {
    G.adj[a][G.deg[a]++] = b;
    G.adj[b][G.deg[b]++] = a;
}
static void remove_vertex(int x) {
    for (int j = 0; j < G.deg[x]; j++) unlink_(G.adj[x][j], x);
    G.deg[x] = 0;
    int last = G.n - 1;
    if (x != last) {
        for (int j = 0; j < G.deg[last]; j++) rep(G.adj[last][j], last, x);
        memcpy(G.adj[x], G.adj[last], sizeof(G.adj[x]));
        G.deg[x] = G.deg[last];
        G.side[x] = G.side[last];
    }
    G.deg[last] = 0;
    G.n--;
}

/* Bitsets of all vertices within distance r of each vertex. */
static Row *balls(int r) {
    int wn = (G.n + 63) / 64;
    Row *c = BX, *x = BY;
    for (int v = 0; v < G.n; v++) {
        memset(c[v], 0, sizeof(Row));
        c[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < G.n; v++) {
            memcpy(x[v], c[v], sizeof(Row));
            for (int j = 0; j < G.deg[v]; j++) {
                const uint64_t *src = c[G.adj[v][j]];
                for (int w = 0; w < wn; w++) x[v][w] |= src[w];
            }
        }
        Row *t = c; c = x; x = t;
    }
    return c;
}

/* Number of unordered pairs at distance > DIAM. */
static long cost(void) {
    Row *b = balls(DIAM);
    int wn = (G.n + 63) / 64;
    long bad = 0;
    for (int v = 0; v < G.n; v++) {
        int pc = 0;
        for (int w = 0; w < wn; w++) pc += popc64(b[v][w]);
        bad += G.n - pc;
    }
    return bad / 2;
}

/* Add cross-side edges between deficient vertices (never hurts distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < G.n; v++) {
        if (G.deg[v] >= DEGB) continue;
        if (G.side[v] == 0) L[nl++] = v; else R[nr++] = v;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1), t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && G.deg[a] < DEGB; j++) {
            int b = R[j];
            if (G.deg[b] < DEGB && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long anneal(int iters, double end) {
    static int s0[MAXN];
    long cur = cost();
    int ns = 0;
    for (int v = 0; v < G.n; v++) if (G.side[v] == 0) s0[ns++] = v;
    if (ns < 2) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > end) break;
        int a = s0[rndi(ns)];
        int c = s0[rndi(ns)];
        if (c == a || G.deg[a] == 0 || G.deg[c] == 0) continue;
        int b = G.adj[a][rndi(G.deg[a])];
        int e = G.adj[c][rndi(G.deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        rep(a, b, e); rep(c, e, b); rep(b, a, c); rep(e, c, a);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndi(10) == 0)) {
            cur = nw;
        } else {
            rep(a, e, b); rep(c, b, e); rep(b, c, a); rep(e, a, c);
        }
    }
    return cur;
}

/* Add one vertex on side t, joined to a greedy cover of the other side. Returns 1 on success. */
static int grow_one(int t) {
    if (G.n >= MAXN - 2) return 0;
    Row *b = balls(DIAM - 1);
    int wn = (G.n + 63) / 64;
    uint64_t unc[W];
    memset(unc, 0, sizeof(unc));
    for (int v = 0; v < G.n; v++) unc[v >> 6] |= 1ULL << (v & 63);
    int chosen[MAXD], nc = 0;
    for (int k = 0; k < DEGB; k++) {
        int bs = -1;
        long bsc = -1;
        for (int s = 0; s < G.n; s++) {
            if (G.side[s] != 1 - t || G.deg[s] >= DEGB) continue;
            int g = 0;
            for (int w = 0; w < wn; w++) g += popc64(b[s][w] & unc[w]);
            if (g == 0) continue;
            long sc = (long)g * 64 + rndi(64);
            if (sc > bsc) { bsc = sc; bs = s; }
        }
        if (bs < 0) break;
        chosen[nc++] = bs;
        for (int w = 0; w < wn; w++) unc[w] &= ~b[bs][w];
    }
    if (nc == 0) return 0;
    int v = G.n++;
    G.side[v] = t;
    G.deg[v] = 0;
    for (int i = 0; i < nc; i++) add_edge(chosen[i], v);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEGB = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    double end = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    memset(&G, 0, sizeof(G));
    if (n0 > 0 && n0 <= MAXN - 4 && DEGB >= 1 && DEGB <= MAXD) {
        G.n = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
            if (G.deg[u] >= DEGB || G.deg[v] >= DEGB || has_edge(u, v)) continue;
            add_edge(u, v);
        }
        for (int v = 0; v < G.n; v++) G.side[v] = -1;
        static int q[MAXN];
        for (int s = 0; s < G.n; s++) {
            if (G.side[s] != -1) continue;
            G.side[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int u = q[qh++];
                for (int j = 0; j < G.deg[u]; j++) {
                    int w = G.adj[u][j];
                    if (G.side[w] == -1) { G.side[w] = 1 - G.side[u]; q[qt++] = w; }
                }
            }
        }
    } else if (DEGB >= 2 && DEGB <= MAXD && DIAM >= 2) {
        G.n = 2 * DEGB;
        for (int a = 0; a < DEGB; a++)
            for (int b = DEGB; b < 2 * DEGB; b++) add_edge(a, b);
        for (int v = 0; v < G.n; v++) G.side[v] = v >= DEGB ? 1 : 0;
    } else {
        printf("0 0\n");
        return 0;
    }

    save(&BEST);
    save(&ACC);
    if (DIAM >= 2) {
        while (now() < end) {
            load(&ACC);
            if (G.n < 8) break;
            int k = 1 + rndi(3);
            for (int i = 0; i < k; i++) remove_vertex(rndi(G.n));
            fill();
            if (anneal(300, end) != 0) continue;
            int fails = 0;
            while (fails < 2 && now() < end) {
                save(&SNAP);
                int t = rndi(2);
                if (!(grow_one(t) || grow_one(1 - t))) break;
                fill();
                if (anneal(500, end) == 0) fails = 0;
                else { load(&SNAP); fails++; }
            }
            if (G.n >= ACC.n - 1) save(&ACC);
            if (G.n > BEST.n) save(&BEST);
            if (ACC.n < BEST.n - 3) memcpy(&ACC, &BEST, sizeof(State));
        }
    }

    load(&BEST);
    int m = 0;
    for (int v = 0; v < G.n; v++)
        for (int j = 0; j < G.deg[v]; j++) if (G.adj[v][j] > v) m++;
    printf("%d %d\n", G.n, m);
    for (int v = 0; v < G.n; v++)
        for (int j = 0; j < G.deg[v]; j++)
            if (G.adj[v][j] > v) printf("%d %d\n", v, G.adj[v][j]);
    return 0;
}
'''


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
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=200):
    """Add vertices whose neighbourhoods cover all vertices within distance D-1 of a neighbour."""
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
    """Join deficient opposite-side vertices in random order (keeps validity)."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
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
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    table = [[0] * N for _ in range(N)]
    for x in range(N):
        a1, b1 = divmod(x, k)
        row = table[x]
        for y in range(N):
            c, d2 = divmod(y, k)
            row[y] = ((a1 + pw[b1] * c) % m) * k + (b1 + d2) % k
    return table


def _bicayley_adj(N, table, S):
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        row = table[g]
        for s in S:
            b = N + row[s]
            adj[g].append(b)
            adj[b].append(g)
    return adj


def _cayley_cost(adj, D):
    total = 0
    N2 = len(adj)
    N = N2 // 2
    for src in (0, N):
        dist = [-1] * N2
        dist[src] = 0
        frontier = [src]
        cnt = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _climb(N, table, d, D, rng, iters, deadline):
    S = rng.sample(range(N), d)
    cur = _cayley_cost(_bicayley_adj(N, table, S), D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in S:
            continue
        newS = list(S)
        newS[i] = cand
        c2 = _cayley_cost(_bicayley_adj(N, table, newS), D)
        if c2 <= cur or (c2 == cur + 1 and rng.random() < 0.05):
            S, cur = newS, c2
    return S if cur == 0 else None


def _bicayley_search(d, D, rng, deadline, consider, lo_n):
    """Try bi-Cayley graphs (n = 2N) that beat lo_n vertices."""
    lo = max(d, lo_n // 2 + 1)
    hi = lib.moore_bound(d, D) // 2
    N = lo
    while N <= hi and time.monotonic() < deadline:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:4]:
            if time.monotonic() >= deadline:
                break
            table = _group_table(m, k, r)
            S = _climb(N, table, d, D, rng, 200, deadline)
            if S is not None:
                edges = [(g, N + table[g][s]) for g in range(N) for s in S]
                consider(2 * N, edges)
                break
        N += 1


# ----------------------------------------------------------------------------
# Build: structured base and twins/bi-Cayley in Python, then C kill-repair-regrow.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    def at(frac):
        return start + frac * time_limit

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)

    if D >= 2:
        while time.monotonic() < at(0.16):
            n, e = _trial(base_n, base_e, d, D, rng, at(0.16))
            consider(n, e)

    if D >= 2 and d >= 2 and time.monotonic() < at(0.2):
        _bicayley_search(d, D, rng, at(0.2), consider, best_n)

    if D >= 2 and d >= 2:
        remaining = at(0.85) - time.monotonic()
        budget = 0.85 * remaining - 1.0
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
