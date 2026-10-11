import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving growth with bipartite annealing.
#
# Input: a bipartite graph with max degree DEG (or "0 0" for K_{DEG,DEG}).
# Loop: copy the current valid graph, scramble it a little, insert a vertex
# pair (remove DEG disjoint edges x_i-y_i, add a-y_i and x_i-b), fill spare
# degree, then anneal with double-edge switches that minimise the number of
# vertex pairs at distance > DIAM. A zero-cost state is kept as the new
# current graph. Distances use 64-bit bitsets. Only valid graphs are printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define ITERS 2000

typedef struct {
    int n, nl, nr;
    int dg[MAXN];
    int col[MAXN];
    int lefts[MAXN];
    int rights[MAXN];
    int nb[MAXN][MAXD];
} State;

static State SC, SW;
static uint64_t R0[MAXN][MAXW];
static uint64_t R1[MAXN][MAXW];
static int DEG, DIAM;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const State *s, int u, int v) {
    for (int k = 0; k < s->dg[u]; k++)
        if (s->nb[u][k] == v) return 1;
    return 0;
}

static void repl(State *s, int v, int old, int nw) {
    for (int k = 0; k < s->dg[v]; k++)
        if (s->nb[v][k] == old) { s->nb[v][k] = nw; return; }
}

static void add_adj(State *s, int u, int v) { s->nb[u][s->dg[u]++] = v; }

static void del_adj(State *s, int u, int v) {
    for (int k = 0; k < s->dg[u]; k++)
        if (s->nb[u][k] == v) {
            s->nb[u][k] = s->nb[u][s->dg[u] - 1];
            s->dg[u]--;
            return;
        }
}

/* edges (a,b),(c,e) with a,c left and b,e right become (a,e),(c,b). */
static int do_switch(State *s, int a, int b, int c, int e) {
    if (a == c || b == e) return 0;
    if (has_edge(s, a, e) || has_edge(s, c, b)) return 0;
    repl(s, a, b, e);
    repl(s, b, a, c);
    repl(s, c, e, b);
    repl(s, e, c, a);
    return 1;
}

/* Number of ordered-free vertex pairs at distance > DIAM. */
static long cost(const State *s) {
    int n = s->n;
    int W = (n + 63) >> 6;
    uint64_t (*A)[MAXW] = R0;
    uint64_t (*B)[MAXW] = R1;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) A[v][w] = 0;
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < DIAM; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) B[v][w] = A[v][w];
            for (int k = 0; k < s->dg[v]; k++) {
                int u = s->nb[v][k];
                for (int w = 0; w < W; w++) B[v][w] |= A[u][w];
            }
        }
        uint64_t (*t)[MAXW] = A;
        A = B;
        B = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(A[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int pick_switch(const State *s, int *a, int *b, int *c, int *e) {
    if (s->nl == 0) return 0;
    *a = s->lefts[rndi(s->nl)];
    if (s->dg[*a] == 0) return 0;
    *b = s->nb[*a][rndi(s->dg[*a])];
    *c = s->lefts[rndi(s->nl)];
    if (s->dg[*c] == 0) return 0;
    *e = s->nb[*c][rndi(s->dg[*c])];
    return 1;
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int anneal(State *s, int iters, double T0, double T1, double deadline) {
    if (s->nl == 0) return 0;
    long cur = cost(s);
    double T = T0;
    double f = pow(T1 / T0, 1.0 / (double)iters);
    for (int it = 0; it < iters && cur > 0; it++, T *= f) {
        if ((it & 127) == 0 && now() > deadline) break;
        int a, b, c, e;
        if (!pick_switch(s, &a, &b, &c, &e)) continue;
        if (!do_switch(s, a, b, c, e)) continue;
        long nw = cost(s);
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            do_switch(s, a, e, c, b);
        }
    }
    return cur == 0;
}

/* Add edges between deficient opposite-side vertices. Never increases cost. */
static void fill(State *s) {
    int L[MAXN], R[MAXN], nL = 0, nR = 0;
    for (int i = 0; i < s->nl; i++)
        if (s->dg[s->lefts[i]] < DEG) L[nL++] = s->lefts[i];
    for (int i = 0; i < s->nr; i++)
        if (s->dg[s->rights[i]] < DEG) R[nR++] = s->rights[i];
    shuffle(L, nL);
    shuffle(R, nR);
    for (int i = 0; i < nL; i++) {
        int a = L[i];
        for (int j = 0; j < nR; j++) {
            if (s->dg[a] >= DEG) break;
            int b = R[j];
            if (s->dg[b] < DEG && !has_edge(s, a, b)) {
                add_adj(s, a, b);
                add_adj(s, b, a);
            }
        }
    }
}

/* Degree-preserving insertion of one new left vertex a and right vertex b. */
static int insert_pair(State *s) {
    int perm[MAXN];
    int L = s->nl;
    if (L == 0) return 0;
    memcpy(perm, s->lefts, sizeof(int) * (size_t)L);
    shuffle(perm, L);
    int xs[MAXD], ys[MAXD], m = 0;
    for (int i = 0; i < L && m < DEG; i++) {
        int x = perm[i];
        if (s->dg[x] == 0) continue;
        int y = s->nb[x][rndi(s->dg[x])];
        int dup = 0;
        for (int j = 0; j < m; j++)
            if (ys[j] == y) { dup = 1; break; }
        if (dup) continue;
        xs[m] = x;
        ys[m] = y;
        m++;
    }
    if (m < DEG) return 0;
    if (s->n + 2 > MAXN) return 0;
    int a = s->n, b = s->n + 1;
    s->n += 2;
    s->col[a] = 0;
    s->col[b] = 1;
    s->dg[a] = 0;
    s->dg[b] = 0;
    s->lefts[s->nl++] = a;
    s->rights[s->nr++] = b;
    for (int i = 0; i < m; i++) {
        int x = xs[i], y = ys[i];
        del_adj(s, x, y);
        del_adj(s, y, x);
        add_adj(s, a, y);
        add_adj(s, y, a);
        add_adj(s, x, b);
        add_adj(s, b, x);
    }
    return 1;
}

static void scramble(State *s, int p) {
    int a, b, c, e;
    for (int i = 0; i < p; i++)
        if (pick_switch(s, &a, &b, &c, &e)) do_switch(s, a, b, c, e);
}

/* Neutral moves only: keeps a valid state valid, diversifies the plateau. */
static void walk(State *s, int steps) {
    int a, b, c, e;
    for (int i = 0; i < steps; i++) {
        if (!pick_switch(s, &a, &b, &c, &e)) continue;
        if (!do_switch(s, a, b, c, e)) continue;
        if (cost(s) != 0) do_switch(s, a, e, c, b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = now() + budget;
    if (DEG < 1 || DEG > MAXD - 2 || DIAM < 1) {
        printf("1 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    State *s = &SC;
    memset(s, 0, sizeof(State));
    int ok = 1;
    if (n0 == 0) {
        s->n = 2 * DEG;
        for (int i = 0; i < DEG; i++)
            for (int j = 0; j < DEG; j++) {
                add_adj(s, i, DEG + j);
                add_adj(s, DEG + j, i);
            }
        for (int v = 0; v < s->n; v++) s->col[v] = (v < DEG) ? 0 : 1;
    } else {
        if (n0 < 1 || n0 > MAXN - 2 || m0 < 0) {
            ok = 0;
        } else {
            s->n = n0;
            for (int i = 0; i < m0 && ok; i++) {
                int u, v;
                if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
                if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
                if (s->dg[u] >= DEG || s->dg[v] >= DEG || has_edge(s, u, v)) { ok = 0; break; }
                add_adj(s, u, v);
                add_adj(s, v, u);
            }
        }
        if (ok) {
            static int q[MAXN];
            for (int v = 0; v < s->n; v++) s->col[v] = -1;
            for (int st = 0; st < s->n; st++) {
                if (s->col[st] >= 0) continue;
                s->col[st] = 0;
                int head = 0, tail = 0;
                q[tail++] = st;
                while (head < tail) {
                    int u = q[head++];
                    for (int k = 0; k < s->dg[u]; k++) {
                        int v = s->nb[u][k];
                        if (s->col[v] < 0) {
                            s->col[v] = 1 - s->col[u];
                            q[tail++] = v;
                        } else if (s->col[v] == s->col[u]) {
                            ok = 0;
                        }
                    }
                }
            }
        }
    }
    if (!ok) {
        printf("1 0\n");
        return 0;
    }

    s->nl = 0;
    s->nr = 0;
    for (int v = 0; v < s->n; v++) {
        if (s->col[v] == 0) s->lefts[s->nl++] = v;
        else s->rights[s->nr++] = v;
    }

    if (cost(s) != 0) {
        if (!anneal(s, 20000, 0.5, 0.05, deadline)) {
            printf("1 0\n");
            return 0;
        }
    }

    int fails = 0;
    while (now() < deadline) {
        memcpy(&SW, &SC, sizeof(State));
        scramble(&SW, 1 + rndi(8));
        if (!insert_pair(&SW)) {
            fails++;
            if (fails % 25 == 0) walk(&SC, 300);
            continue;
        }
        fill(&SW);
        if (anneal(&SW, ITERS, 0.6, 0.05, deadline)) {
            memcpy(&SC, &SW, sizeof(State));
            fails = 0;
        } else {
            fails++;
            if (fails % 25 == 0) walk(&SC, 300);
        }
    }

    State *o = &SC;
    int m = 0;
    for (int i = 0; i < o->nl; i++) m += o->dg[o->lefts[i]];
    printf("%d %d\n", o->n, m);
    for (int i = 0; i < o->nl; i++) {
        int v = o->lefts[i];
        for (int k = 0; k < o->dg[v]; k++) printf("%d %d\n", v, o->nb[v][k]);
    }
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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
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
    """Dense structured graph (degree may exceed d), later thinned into a valid graph."""
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Swap-based local search for a cover of `full` by at most d candidates."""
    if not cands:
        return None
    k = min(d, len(cands))
    cur = rng.sample(cands, k)

    def cov(S):
        c = 0
        for s in S:
            c |= ball[s]
        return c

    cur_cov = cov(cur)
    cur_score = cur_cov.bit_count()
    for it in range(iters):
        if cur_cov == full:
            return cur
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        inn = rng.choice(cands)
        if inn in cur:
            continue
        trial = cur[:]
        trial[i] = inn
        t_cov = cov(trial)
        t_score = t_cov.bit_count()
        if t_score >= cur_score or rng.random() < 0.02:
            cur, cur_cov, cur_score = trial, t_cov, t_score
    return cur if cur_cov == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover deficient vertices."""
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
            if not chosen and time.monotonic() < deadline:
                chosen = _cover_search(cands, ball, full, d, rng, 1500, deadline)
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


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

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
    """Delete the worst vertices in batches until the diameter bound holds."""
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
# C refinement: anneal-based vertex insertion from the best graph so far.
# ----------------------------------------------------------------------------

def _c_refine(d, D, seed, graph, budget):
    """Run the C engine from `graph` for `budget` seconds. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=graph,
                        timeout=budget + 15.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver. Usable span = 0.9 * time_limit - 3 s.
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C annealing engine from the best valid graph until the end of the span
# Every candidate passes lib.is_valid before it is kept. The Haar graph is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = 0.9 * time_limit - 3.0

    def at(f):
        return start + f * span

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= bound:
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
        n1, e1 = _grow(n0, e0, d, D, at(0.03), rng)
        consider(n1, e1)
    if D >= 2 and best_n < bound:
        trial_end = at(0.08)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if best_n >= bound:
        return best_n, list(best_e)

    # Phase B: thinned dense graph, repeated.
    if D >= 2 and time.monotonic() < at(0.16):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            end_b = at(0.16)
            while time.monotonic() < end_b:
                r = _deletion_trial(d, D, rn, re, rng, end_b)
                if r is None:
                    break
                consider(*r)

    if best_n >= bound:
        return best_n, list(best_e)

    # Phase C: C annealing engine from the best valid graph.
    if D >= 2 and d <= 30 and best_n < bound:
        budget = at(1.0) - time.monotonic() - 1.0
        if budget >= 3.0:
            res = _c_refine(d, D, seed, (best_n, best_e), budget)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
