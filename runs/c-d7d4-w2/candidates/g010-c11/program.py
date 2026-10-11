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

#define MAXN 4096
#define MAXW 64
#define MAXDEG 64
#define ITER 2500

static int d_, D_;
static int n;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];

static int sn;
static int sdeg[MAXN];
static int sside[MAXN];
static int sadj[MAXN][MAXDEG];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static void shuffle_i(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Number of ordered-free unordered pairs at distance > D_ (unreachable counts). */
static long cost(void) {
    int W = (n + 63) / 64;
    uint64_t *A = bufA, *B = bufB;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * W;
            const uint64_t *av = A + (size_t)v * W;
            for (int w = 0; w < W; w++) bv[w] = av[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *au = A + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
        }
        uint64_t *t = A;
        A = B;
        B = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        const uint64_t *av = A + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += popc(av[w]);
        total += n - pc;
    }
    return total / 2;
}

static int pick_side(int s) {
    for (int t = 0; t < 1000; t++) {
        int v = rndi(n);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Simulated annealing over degree-preserving bipartite double-edge switches. */
static long anneal(long cur, int iters, double T0, double T1, double tend) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > tend) break;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int s = rndi(2);
        int a = pick_side(s), c = pick_side(s);
        if (a < 0 || c < 0 || a == c) continue;
        int b = adj[a][rndi(deg[a])];
        int e = adj[c][rndi(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost();
        long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

/* Add spare-degree edges between deficient opposite-side vertices (never hurts). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_i(L, nl);
    shuffle_i(R, nr);
    for (int i = 0; i < nl; i++)
        for (int j = 0; j < nr; j++) {
            int a = L[i], b = R[j];
            if (deg[a] < d_ && deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
}

/* Append one vertex on a random side, joined to d vertices of the other side. */
static void add_vertex(void) {
    static int cand[MAXN], full[MAXN];
    int c = rndi(2);
    int v = n++;
    deg[v] = 0;
    side[v] = c;
    int nc = 0, nf = 0;
    for (int u = 0; u < v; u++) {
        if (side[u] != 1 - c) continue;
        if (deg[u] < d_) cand[nc++] = u;
        else full[nf++] = u;
    }
    shuffle_i(cand, nc);
    shuffle_i(full, nf);
    int k = 0;
    for (int i = 0; i < nc && k < d_; i++) {
        add_edge(v, cand[i]);
        k++;
    }
    for (int i = 0; i < nf && k < d_; i++) {
        int u = full[i];
        int x = adj[u][rndi(deg[u])];
        remove_edge(u, x);
        add_edge(v, u);
        k++;
    }
}

static void save(void) {
    sn = n;
    memcpy(sdeg, deg, sizeof(int) * n);
    memcpy(sside, side, sizeof(int) * n);
    for (int v = 0; v < n; v++) memcpy(sadj[v], adj[v], sizeof(int) * deg[v]);
}

static void restore(void) {
    n = sn;
    memcpy(deg, sdeg, sizeof(int) * n);
    memcpy(side, sside, sizeof(int) * n);
    for (int v = 0; v < n; v++) memcpy(adj[v], sadj[v], sizeof(int) * deg[v]);
}

static void emit(void) {
    long m = 0;
    for (int v = 0; v < sn; v++) m += sdeg[v];
    printf("%d %ld\n", sn, m / 2);
    for (int v = 0; v < sn; v++)
        for (int i = 0; i < sdeg[v]; i++) {
            int u = sadj[v][i];
            if (v < u) printf("%d %d\n", v, u);
        }
}

static void load_input(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    n = 0;
    memset(deg, 0, sizeof(deg));
    if (n0 >= 2 && n0 <= MAXN - 64) {
        n = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
            if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) continue;
            add_edge(u, v);
        }
    }
    int ok = (n > 0);
    for (int v = 0; v < n; v++) side[v] = -1;
    static int queue[MAXN];
    for (int s = 0; ok && s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    ok = 0;
                    break;
                }
            }
            if (!ok) break;
        }
    }
    if (!ok) {
        memset(deg, 0, sizeof(deg));
        n = 2 * d_;
        for (int v = 0; v < n; v++) side[v] = (v < d_) ? 0 : 1;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++) add_edge(i, d_ + j);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (d_ < 2 || d_ > MAXDEG || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < 20; i++) rnd();
    load_input();

    double tend = now() + budget;
    long cur = cost();
    int valid = (cur == 0);
    if (valid) save();

    while (now() < tend) {
        if (!valid) {
            cur = anneal(cur, 5000, 1.0, 0.05, tend);
            if (cur == 0) {
                valid = 1;
                save();
            }
            continue;
        }
        if (n >= MAXN - 2) break;
        add_vertex();
        fill();
        cur = cost();
        cur = anneal(cur, ITER, 0.8, 0.03, tend);
        if (cur == 0) {
            save();
        } else {
            restore();
        }
        cur = 0;
    }
    emit();
    return 0;
}
'''


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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small semidirect products (Python seeding phase).
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    """All (m, k, r) with the semidirect product Z_m x|_r Z_k of order N = m*k."""
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
    """Multiplication table of Z_m x|_r Z_k; element (a, b) is coded a*k + b, identity 0."""
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
    """Adjacency lists of the bi-Cayley graph: a_g = g, b_x = N + x, a_g ~ b_{g*s}."""
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        row = table[g]
        ag = adj[g]
        for s in S:
            b = N + row[s]
            ag.append(b)
            adj[b].append(g)
    return adj


def _cayley_cost(adj, D):
    """Vertices farther than D from a_e or from b_e (both sources)."""
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
    """Hill-climb a d-element generating set S minimising the Cayley cost. Returns S or None."""
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
    """Search bi-Cayley graphs of increasing order N (n = 2N) that beat lo_n vertices."""
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
# Main pipeline: structured seed -> bi-Cayley seed -> C annealing that grows
# the graph one vertex at a time while keeping every accepted state valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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

    if D >= 2 and d >= 3:
        # Phase A: structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
        base = None
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * T, rng)
            consider(n1, e1)

        tend = start + 0.12 * T
        for _ in range(3):
            if time.monotonic() >= tend:
                break
            n, e = _duplicate_twins(best_n, best_e, d, rng)
            e = _saturate_edges(n, e, d, rng)
            n, e = _grow(n, e, d, D, tend, rng, attempts=30)
            consider(n, e)

        # Phase B: bi-Cayley seeds over small groups.
        _bicayley_search(d, D, rng, start + 0.2 * T, consider, best_n)

    # Phase C: C annealing from the best valid graph found so far.
    if D >= 2 and d >= 3 and best_n < lib.moore_bound(d, D):
        remaining = start + 0.92 * T - time.monotonic()
        if remaining > 2.5:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining - 2.0:.2f}"],
                                stdin_graph=(best_n, best_e),
                                timeout=max(1.0, start + 0.95 * T - time.monotonic()))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
