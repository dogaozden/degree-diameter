import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: kill / add / anneal search on bipartite graphs with degree <= d and
# diameter <= D. Bad pairs are counted with bitset balls. Moves are
# degree-preserving bipartite double-edge switches (Metropolis on bad pairs),
# greedy cover vertices, and single-vertex kills. A state is kept only when it is
# valid, and the walk is anchored to within a few vertices of its best.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000
#define MAXW ((MAXN + 63) / 64)
#define MAXD 64
#define ADJCAP (MAXN * MAXD)
#define TEMP 0.3

typedef uint64_t Row[MAXW];

static int DEG, DIAM;
static int nv;
static int dg[MAXN];
static int col[MAXN];
static int adjv[ADJCAP];
static Row SA[MAXN], SB[MAXN], CB[MAXN];

typedef struct {
    int n;
    int dg[MAXN];
    int col[MAXN];
    int adj[ADJCAP];
} State;

static State SNAP, BEST;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++)
        if (adjv[a * DEG + i] == b) return 1;
    return 0;
}

static void rm_half(int a, int b) {
    int *p = &adjv[a * DEG];
    for (int i = 0; i < dg[a]; i++) {
        if (p[i] == b) {
            p[i] = p[dg[a] - 1];
            dg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adjv[a * DEG + dg[a]] = b;
    dg[a]++;
    adjv[b * DEG + dg[b]] = a;
    dg[b]++;
}

static void remove_edge(int a, int b) {
    rm_half(a, b);
    rm_half(b, a);
}

/* res[v] = bitmask of vertices within distance radius of v. */
static void balls(int radius, Row *res) {
    int w = (nv + 63) >> 6;
    Row *cur = SA, *nxt = SB, *tmp;
    for (int v = 0; v < nv; v++) {
        for (int k = 0; k < w; k++) cur[v][k] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < radius; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt[v];
            uint64_t *c = cur[v];
            for (int k = 0; k < w; k++) o[k] = c[k];
            const int *a = &adjv[v * DEG];
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *s = cur[a[i]];
                for (int k = 0; k < w; k++) o[k] |= s[k];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    for (int v = 0; v < nv; v++)
        for (int k = 0; k < w; k++) res[v][k] = cur[v][k];
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long cost_now(void) {
    int w = (nv + 63) >> 6;
    balls(DIAM, CB);
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(CB[v][k]);
        bad += nv - c;
    }
    return bad / 2;
}

static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < nv; v++) {
        if (dg[v] < DEG) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && dg[a] < DEG; j++) {
            int b = R[j];
            if (dg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add a vertex on `side` joined to a greedy cover of the other side's balls. */
static void add_vertex(int side) {
    int old = nv;
    if (old + 1 >= MAXN) return;
    int w = (old + 63) >> 6;
    balls(DIAM - 1, CB);
    uint64_t covered[MAXW];
    for (int k = 0; k < w; k++) covered[k] = 0;
    int chosen[MAXD];
    int nc = 0;
    for (int step = 0; step < DEG; step++) {
        long long bestScore = -1;
        int bs = -1;
        for (int s = 0; s < old; s++) {
            if (col[s] != 1 - side) continue;
            int used = 0;
            for (int i = 0; i < nc; i++)
                if (chosen[i] == s) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(CB[s][k] & ~covered[k]);
            if (g == 0) continue;
            long long score = (long long)g * 4096 + (long long)(rnd() % 4096);
            if (score > bestScore) {
                bestScore = score;
                bs = s;
            }
        }
        if (bs < 0) break;
        chosen[nc++] = bs;
        for (int k = 0; k < w; k++) covered[k] |= CB[bs][k];
    }
    if (nc == 0) return;
    int v = nv++;
    col[v] = side;
    dg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (dg[s] >= DEG) {
            int t = adjv[s * DEG + rint_(dg[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* Delete vertex x, relabelling the last vertex to x. */
static void remove_vertex(int x) {
    while (dg[x] > 0) remove_edge(x, adjv[x * DEG]);
    int last = nv - 1;
    if (x != last) {
        for (int i = 0; i < dg[last]; i++) {
            int z = adjv[last * DEG + i];
            int *p = &adjv[z * DEG];
            for (int j = 0; j < dg[z]; j++) {
                if (p[j] == last) { p[j] = x; break; }
            }
        }
        for (int i = 0; i < dg[last]; i++) adjv[x * DEG + i] = adjv[last * DEG + i];
        dg[x] = dg[last];
        col[x] = col[last];
    }
    dg[last] = 0;
    nv--;
}

/* Metropolis double-edge switches (degrees and sides kept). Returns final cost. */
static long long anneal(long long cur, int iters, double T) {
    static int L0[MAXN];
    int nl = 0;
    for (int v = 0; v < nv; v++)
        if (col[v] == 0 && dg[v] > 0) L0[nl++] = v;
    if (nl < 2) return cur;
    for (int it = 0; it < iters; it++) {
        if (cur == 0) break;
        int a = L0[rint_(nl)];
        int c = L0[rint_(nl)];
        if (a == c || dg[a] == 0 || dg[c] == 0) continue;
        int b = adjv[a * DEG + rint_(dg[a])];
        int e = adjv[c * DEG + rint_(dg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost_now();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static int colour_graph(void) {
    static int stk[MAXN];
    for (int v = 0; v < nv; v++) col[v] = -1;
    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < dg[u]; i++) {
                int w = adjv[u * DEG + i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void save_state(State *st) {
    st->n = nv;
    memcpy(st->dg, dg, sizeof(int) * (size_t)nv);
    memcpy(st->col, col, sizeof(int) * (size_t)nv);
    memcpy(st->adj, adjv, sizeof(int) * (size_t)nv * (size_t)DEG);
}

static void load_state(const State *st) {
    nv = st->n;
    memcpy(dg, st->dg, sizeof(int) * (size_t)nv);
    memcpy(col, st->col, sizeof(int) * (size_t)nv);
    memcpy(adjv, st->adj, sizeof(int) * (size_t)nv * (size_t)DEG);
}

static void print_state(const State *st) {
    long long m = 0;
    for (int v = 0; v < st->n; v++) m += st->dg[v];
    m /= 2;
    printf("%d %lld\n", st->n, m);
    for (int v = 0; v < st->n; v++)
        for (int i = 0; i < st->dg[v]; i++) {
            int u = st->adj[v * DEG + i];
            if (u > v) printf("%d %d\n", v, u);
        }
}

static double elapsed(clock_t t0) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();
    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 > MAXN - 400) {
        printf("0 0\n");
        return 0;
    }
    if (n0 <= 0 || m0 <= 0) {
        nv = 2;
        dg[0] = dg[1] = 0;
        col[0] = 0;
        col[1] = 1;
        add_edge(0, 1);
    } else {
        nv = n0;
        for (int v = 0; v < nv; v++) dg[v] = 0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || u >= nv || v < 0 || v >= nv || u == v) continue;
            if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) continue;
            add_edge(u, v);
        }
        if (!colour_graph()) {
            printf("0 0\n");
            return 0;
        }
    }

    clock_t t0 = clock();
    long long c = cost_now();
    if (c != 0) c = anneal(c, 20000, TEMP);
    if (c != 0) {
        printf("0 0\n");
        return 0;
    }
    save_state(&BEST);
    save_state(&SNAP);
    int best_n = nv;

    while (elapsed(t0) < limit) {
        load_state(&SNAP);
        int r = rint_(100);
        if (r < 65) {
            add_vertex(rint_(2));
        } else if (nv > 4) {
            int k = 1 + rint_(2);
            for (int j = 0; j < k && nv > 4; j++) remove_vertex(rint_(nv));
        }
        fill_edges();
        long long cc = cost_now();
        cc = anneal(cc, 300, TEMP);
        if (cc == 0 && nv >= best_n - 3) {
            save_state(&SNAP);
            if (nv > best_n) {
                best_n = nv;
                save_state(&BEST);
            }
        }
    }
    print_state(&BEST);
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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for the structured start (cover growth and saturation).
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
    """Add vertices whose neighbourhoods are cover sets of the other side (keeps diameter <= D)."""
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
    """Join deficient opposite-side vertices greedily (only shortens distances)."""
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
    """Alternate cover-vertex extension and saturation until neither helps."""
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


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.9 * time_limit
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

    # Structured start: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, t0 + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Main search in C, started from the best valid graph so far.
    # Skip when the start already meets the Moore bound (nothing to gain).
    if D >= 2 and 2 <= d <= 60 and best_n < lib.moore_bound(d, D):
        budget = end - time.monotonic() - 1.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=budget + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
