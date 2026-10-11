import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Works on a bipartite graph with max degree d, keeping the side of every
# vertex. Two moves:
#   * degree-preserving edge switches (a-b, c-e -> a-e, c-b), annealed to
#     minimise the number of vertex pairs at distance > D;
#   * growth: remove d disjoint edges and add one vertex on each side
#     (a joined to the d right ends, b joined to the d left ends). Degrees stay
#     the same. After each growth the annealer runs until cost 0 (a valid graph
#     with two more vertices) or gives up, and then the best graph is restored.
# Costs are computed exactly with bitset balls.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)
#define ITERS 6000

typedef struct { int a, b; } Ed;   /* a: colour-0 end, b: colour-1 end */

static int D, DEG, N, NE;
static Ed E[MAXE];
static Ed BE[MAXE];
static Ed INP[MAXE];
static int BN = 0, BNE = 0;
static int nd[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static int col[MAXN];
static int mark[MAXN];
static int stamp = 1;
static uint64_t bitA[MAXN][MAXW], bitB[MAXN][MAXW];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static clock_t T0;
static double LIMIT;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long cost_eval(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = bitA;
    uint64_t (*nxt)[MAXW] = bitB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < nd[v]; i++) {
                const uint64_t *src = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long s = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        s += N - c;
    }
    return s / 2;
}

static void nb_del(int u, int v) {
    for (int i = 0; i < nd[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][nd[u] - 1];
            nd[u]--;
            return;
        }
    }
}

static void nb_rep(int u, int old, int nw) {
    for (int i = 0; i < nd[u]; i++) {
        if (nb[u][i] == old) { nb[u][i] = nw; return; }
    }
}

static void add_edge(int a, int b) {   /* a colour 0, b colour 1 */
    A[a][b] = 1; A[b][a] = 1;
    nb[a][nd[a]++] = b;
    nb[b][nd[b]++] = a;
    E[NE].a = a; E[NE].b = b;
    NE++;
}

/* Switch edges p=(a,b), q=(c,e) into (a,e), (c,b). Calling it again with the
   same p, q undoes it. Returns 0 if the switch is illegal. */
static int try_switch(int p, int q) {
    int a = E[p].a, b = E[p].b, c = E[q].a, e = E[q].b;
    if (a == c || b == e) return 0;
    if (A[a][e] || A[c][b]) return 0;
    A[a][b] = 0; A[b][a] = 0;
    A[c][e] = 0; A[e][c] = 0;
    A[a][e] = 1; A[e][a] = 1;
    A[c][b] = 1; A[b][c] = 1;
    nb_rep(a, b, e);
    nb_rep(e, c, a);
    nb_rep(c, e, b);
    nb_rep(b, a, c);
    E[p].b = e;
    E[q].b = b;
    return 1;
}

/* Load a graph; returns 0 if it is not bipartite or breaks the degree bound. */
static int rebuild(int n, const Ed *ed, int m) {
    static int qu[MAXN];
    if (n < 0 || n > MAXN - 8 || m < 0 || m > MAXE) return 0;
    N = n; NE = 0;
    memset(A, 0, sizeof(A));
    for (int v = 0; v < n; v++) { nd[v] = 0; col[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u = ed[i].a, v = ed[i].b;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (A[u][v]) return 0;
        if (nd[u] >= DEG || nd[v] >= DEG) return 0;
        A[u][v] = 1; A[v][u] = 1;
        nb[u][nd[u]++] = v;
        nb[v][nd[v]++] = u;
    }
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int i = 0; i < nd[u]; i++) {
                int v = nb[u][i];
                if (col[v] == -1) { col[v] = 1 - col[u]; qu[t++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    for (int i = 0; i < m; i++) {
        int u = ed[i].a, v = ed[i].b;
        if (col[u] == 0) { E[NE].a = u; E[NE].b = v; }
        else { E[NE].a = v; E[NE].b = u; }
        NE++;
    }
    return 1;
}

/* Add edges between deficient vertices on opposite sides (never raises cost). */
static void saturate(void) {
    static int Ls[MAXN], Rs[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (nd[v] >= DEG) continue;
        if (col[v] == 0) Ls[nl++] = v; else Rs[nr++] = v;
    }
    if (nl == 0 || nr == 0) return;
    long tries = 40L * (nl + nr);
    for (long t = 0; t < tries && NE < MAXE - 2; t++) {
        int x = Ls[rndi(nl)], y = Rs[rndi(nr)];
        if (nd[x] < DEG && nd[y] < DEG && !A[x][y]) add_edge(x, y);
    }
}

/* Growth: remove DEG disjoint edges, add vertices a (side 0) and b (side 1). */
static int grow_once(void) {
    static int ord[MAXE];
    int chosen[MAXDEG];
    if (N + 2 > MAXN - 2) return 0;
    if (NE < DEG || NE + DEG >= MAXE - 4) return 0;
    int ok = 0;
    for (int attempt = 0; attempt < 40 && !ok; attempt++) {
        for (int i = 0; i < NE; i++) ord[i] = i;
        for (int i = NE - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
        }
        stamp++;
        int k = 0;
        for (int i = 0; i < NE && k < DEG; i++) {
            int p = ord[i], x = E[p].a, y = E[p].b;
            if (mark[x] == stamp || mark[y] == stamp) continue;
            mark[x] = stamp; mark[y] = stamp;
            chosen[k++] = p;
        }
        if (k == DEG) ok = 1;
    }
    if (!ok) return 0;
    int xs[MAXDEG], ys[MAXDEG];
    for (int i = 0; i < DEG; i++) {
        xs[i] = E[chosen[i]].a;
        ys[i] = E[chosen[i]].b;
    }
    /* sort chosen indices in decreasing order so swap-with-last is safe */
    for (int i = 1; i < DEG; i++) {
        int t = chosen[i], j = i - 1;
        while (j >= 0 && chosen[j] < t) { chosen[j + 1] = chosen[j]; j--; }
        chosen[j + 1] = t;
    }
    for (int i = 0; i < DEG; i++) {
        int p = chosen[i];
        int a = E[p].a, b = E[p].b;
        A[a][b] = 0; A[b][a] = 0;
        nb_del(a, b);
        nb_del(b, a);
        E[p] = E[NE - 1];
        NE--;
    }
    int a = N, b = N + 1;
    N += 2;
    nd[a] = 0; nd[b] = 0;
    col[a] = 0; col[b] = 1;
    for (int i = 0; i < DEG; i++) add_edge(a, ys[i]);
    for (int i = 0; i < DEG; i++) add_edge(xs[i], b);
    return 1;
}

static void save_best(void) {
    BN = N;
    BNE = NE;
    memcpy(BE, E, sizeof(Ed) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    T0 = clock();
    LIMIT = budget;
    DEG = d;
    if (d < 1 || d > MAXDEG - 2 || D < 1) { printf("0 0\n"); return 0; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 == 0) {
        n0 = 2 * d; m0 = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                INP[m0].a = i; INP[m0].b = d + j; m0++;
            }
    } else {
        if (n0 < 0 || n0 > MAXN - 8 || m0 < 0 || m0 > MAXE) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m0; i++) {
            if (scanf("%d %d", &INP[i].a, &INP[i].b) != 2) { printf("0 0\n"); return 0; }
        }
    }

    if (!rebuild(n0, INP, m0)) { printf("0 0\n"); return 0; }
    if (cost_eval() != 0) { printf("0 0\n"); return 0; }
    saturate();
    save_best();

    while (elapsed() < LIMIT) {
        if (!grow_once()) break;
        saturate();
        long cur = cost_eval();
        int it = 0;
        while (cur > 0 && it < ITERS) {
            if ((it & 127) == 0 && elapsed() > LIMIT) break;
            it++;
            int p = rndi(NE), q = rndi(NE);
            if (p == q || !try_switch(p, q)) continue;
            long nc = cost_eval();
            long delta = nc - cur;
            double temp = 0.7 * pow(0.15, (double)it / ITERS);
            if (delta <= 0 || rndu() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                try_switch(p, q);   /* revert */
            }
        }
        if (cur == 0) {
            save_best();
        } else if (!rebuild(BN, BE, BNE)) {
            break;
        }
    }

    printf("%d %d\n", BN, BNE);
    for (int i = 0; i < BNE; i++) printf("%d %d\n", BE[i].a, BE[i].b);
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


# ----------------------------------------------------------------------------
# Python helpers for structured growth.
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
# Driver. The span is 0.92 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials (Python)
#   C  NEW: C engine. Degree-preserving growth with annealed edge switches,
#      started from the best Python graph. Returns its best valid graph.
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = 0.92 * time_limit

    def at(f):
        return start + f * span

    rng = random.Random(seed)
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best_n, list(best_e)

    # Phase A: structured base, grown, then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.12), rng)
        consider(n1, e1)
    if best_n >= moore:
        return best_n, list(best_e)

    if D >= 2:
        base_n, base_e = best_n, list(best_e)
        trial_end = at(0.2)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
            if best_n >= moore:
                break
    if best_n >= moore:
        return best_n, list(best_e)

    # Phase C: C engine from the best graph so far.
    if D >= 2 and d >= 2:
        remaining = start + span - time.monotonic()
        budget = remaining - 3.0   # margin for compilation and parsing
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=remaining - 1.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
