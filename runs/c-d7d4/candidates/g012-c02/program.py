import itertools
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

static int d, D, W, NMAX, n;
static int *adj, *deg, *col;
static u64 *ballA, *ballB, *covB, *covered;
static int *snapAdj, *snapDeg, *snapCol, snapN;
static int *bestAdj, *bestDeg, *bestCol, bestN;
static int *isch, *Lbuf, *Rbuf, *Qbuf;
static u64 rs = 88172645463325252ULL;
static double budget;
static clock_t t0;
static const int ITERS = 800;

static u64 rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (u64)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int time_left(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC < budget;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a * d + k] == b) return 1;
    return 0;
}

static void del_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a * d + k] == b) {
            adj[a * d + k] = adj[a * d + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) { del_half(a, b); del_half(b, a); }

static void add_edge(int a, int b) {
    if (deg[a] >= d || deg[b] >= d) return;  /* callers guarantee room */
    adj[a * d + deg[a]++] = b;
    adj[b * d + deg[b]++] = a;
}

/* Bitmask balls of radius r; returns whichever buffer holds the result. */
static u64 *compute_balls(int r) {
    u64 *cur = ballA, *nxt = ballB;
    memset(cur, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(u64) * W);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *o = cur + (size_t)adj[v * d + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= o[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    return cur;
}

/* Number of unordered pairs at distance greater than D (unreachable included). */
static long cost_full(void) {
    u64 *b = compute_balls(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const u64 *x = b + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(x[w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Attach a new vertex on side s to a greedy cover of the existing vertices.
   Neighbours at full degree lose one random edge to make room. */
static int grow_one(int s) {
    if (n >= NMAX || n < 1) return 0;
    u64 *b = compute_balls(D - 1);
    memcpy(covB, b, sizeof(u64) * (size_t)n * W);
    memset(covered, 0, sizeof(u64) * W);
    for (int i = 0; i < n; i++) isch[i] = 0;
    int cap = d < 60 ? d : 60;
    int chosen[64];
    int nch = 0;
    while (nch < cap) {
        int best = -1, bestg = 0, ties = 0;
        for (int u = 0; u < n; u++) {
            if (col[u] != 1 - s || isch[u]) continue;
            const u64 *x = covB + (size_t)u * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(x[w] & ~covered[w]);
            if (g > bestg) { bestg = g; best = u; ties = 1; }
            else if (g == bestg && g > 0) { ties++; if (rndi(ties) == 0) best = u; }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        isch[best] = 1;
        for (int w = 0; w < W; w++) covered[w] |= covB[(size_t)best * W + w];
    }
    if (nch == 0) return 0;
    int v = n;
    n++;
    col[v] = s;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int u = chosen[i];
        if (deg[u] >= d) {
            int t = adj[u * d + rndi(deg[u])];
            del_edge(u, t);
        }
        add_edge(u, v);
    }
    return 1;
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices; only shortens distances. */
static void fill(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) Lbuf[nl++] = v; else Rbuf[nr++] = v;
        }
    }
    shuffle_int(Lbuf, nl);
    shuffle_int(Rbuf, nr);
    for (int i = 0; i < nl; i++) {
        int a = Lbuf[i];
        for (int j = 0; j < nr && deg[a] < d; j++) {
            int b = Rbuf[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static int pick_side(int s) {
    for (int t = 0; t < 200; t++) {
        int x = rndi(n);
        if (col[x] == s) return x;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs.
   Returns 0 when the graph becomes valid. */
static long anneal(int iters) {
    fill();
    long cur = cost_full();
    for (int it = 0; it < iters && cur > 0; it++) {
        if (!time_left()) break;
        double T = 0.6 * (1.0 - (double)it / iters) + 0.05;
        int a = pick_side(0), c = pick_side(0);
        if (a < 0 || c < 0 || a == c || deg[a] == 0 || deg[c] == 0) continue;
        int b = adj[a * d + rndi(deg[a])];
        int e = adj[c * d + rndi(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost_full();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

/* Delete vertex x; the last vertex takes its index. */
static void remove_vertex(int x) {
    while (deg[x] > 0) {
        int t = adj[x * d + deg[x] - 1];
        del_edge(x, t);
    }
    int y = n - 1;
    if (x != y) {
        for (int k = 0; k < deg[y]; k++) {
            int u = adj[y * d + k];
            for (int j = 0; j < deg[u]; j++) {
                if (adj[u * d + j] == y) { adj[u * d + j] = x; break; }
            }
        }
        deg[x] = deg[y];
        col[x] = col[y];
        memcpy(adj + (size_t)x * d, adj + (size_t)y * d, sizeof(int) * d);
    }
    deg[y] = 0;
    n--;
}

static void save_to(int *A, int *Dg, int *C, int *pn) {
    memcpy(A, adj, sizeof(int) * (size_t)n * d);
    memcpy(Dg, deg, sizeof(int) * (size_t)n);
    memcpy(C, col, sizeof(int) * (size_t)n);
    *pn = n;
}

static void restore(const int *A, const int *Dg, const int *C, int pn) {
    n = pn;
    memcpy(adj, A, sizeof(int) * (size_t)n * d);
    memcpy(deg, Dg, sizeof(int) * (size_t)n);
    memcpy(col, C, sizeof(int) * (size_t)n);
}

static int color_graph(void) {
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        Qbuf[qt++] = s;
        while (qh < qt) {
            int u = Qbuf[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * d + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; Qbuf[qt++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

static void set_kdd(void) {
    for (int v = 0; v < NMAX; v++) deg[v] = 0;
    n = 2 * d;
    for (int i = 0; i < d; i++) { col[i] = 0; col[d + i] = 1; }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(i, d + j);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    budget = atof(argv[4]);
    t0 = clock();
    for (int i = 0; i < 10; i++) rnd64();

    int nin = 0, min = 0;
    if (scanf("%d %d", &nin, &min) != 2) { nin = 0; min = 0; }
    if (min < 0) min = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min > 0 ? min : 1));
    int *ev = malloc(sizeof(int) * (size_t)(min > 0 ? min : 1));
    int mcount = 0;
    for (int i = 0; i < min; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u >= 0 && v >= 0 && u < nin && v < nin && u != v) {
            eu[mcount] = u;
            ev[mcount] = v;
            mcount++;
        }
    }

    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1 || d == 1) { printf("2 1\n0 1\n"); return 0; }

    double mo;
    if (d == 2) {
        mo = 2.0 * D;
    } else {
        mo = 0.0;
        double pw = 1.0;
        for (int i = 0; i < D; i++) { mo += pw; pw *= (d - 1); }
        mo *= 2.0;
    }
    int cap = 6000;
    int moore = (int)(mo > cap ? cap : mo);
    NMAX = (moore > nin ? moore : nin) + 2;
    W = (NMAX + 63) / 64;

    adj = calloc((size_t)NMAX * d, sizeof(int));
    deg = calloc(NMAX, sizeof(int));
    col = calloc(NMAX, sizeof(int));
    ballA = calloc((size_t)NMAX * W, sizeof(u64));
    ballB = calloc((size_t)NMAX * W, sizeof(u64));
    covB = calloc((size_t)NMAX * W, sizeof(u64));
    covered = calloc(W, sizeof(u64));
    snapAdj = calloc((size_t)NMAX * d, sizeof(int));
    snapDeg = calloc(NMAX, sizeof(int));
    snapCol = calloc(NMAX, sizeof(int));
    bestAdj = calloc((size_t)NMAX * d, sizeof(int));
    bestDeg = calloc(NMAX, sizeof(int));
    bestCol = calloc(NMAX, sizeof(int));
    isch = calloc(NMAX, sizeof(int));
    Lbuf = calloc(NMAX, sizeof(int));
    Rbuf = calloc(NMAX, sizeof(int));
    Qbuf = calloc(NMAX, sizeof(int));

    int ok = 0;
    if (nin > 0 && mcount > 0 && nin <= NMAX) {
        ok = 1;
        n = nin;
        for (int v = 0; v < n; v++) deg[v] = 0;
        for (int i = 0; i < mcount && ok; i++) {
            int u = eu[i], v = ev[i];
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
        if (ok) ok = color_graph();
    }
    if (!ok) set_kdd();

    long c0 = cost_full();
    if (c0 > 0) c0 = anneal(20000);
    if (c0 > 0) set_kdd();

    save_to(bestAdj, bestDeg, bestCol, &bestN);

    while (time_left()) {
        save_to(snapAdj, snapDeg, snapCol, &snapN);
        int mode = rndi(4);
        int good = 0;
        if (mode < 2) {
            if (grow_one(rndi(2))) good = (anneal(ITERS) == 0);
        } else {
            int k = 1 + rndi(2);
            for (int i = 0; i < k && n > k; i++) remove_vertex(rndi(n));
            for (int i = 0; i < k; i++) grow_one(rndi(2));
            if (n >= snapN) good = (anneal(ITERS) == 0);
        }
        if (good) {
            if (n > bestN) save_to(bestAdj, bestDeg, bestCol, &bestN);
        } else {
            restore(snapAdj, snapDeg, snapCol, snapN);
        }
    }

    long m = 0;
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestDeg[v]; k++)
            if (bestAdj[v * d + k] > v) m++;
    printf("%d %ld\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestDeg[v]; k++) {
            int u = bestAdj[v * d + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


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
    """Generalized quadrangle W(q) for the largest prime power q (q <= 16) with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twins(n, edges, d, rng):
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree.

    Twins keep all distances, so the diameter bound (D >= 2) is preserved.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    for _ in range(3):
        order = list(range(n))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d or any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertex pairs (only shortens distances)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    left = [v for v in range(n) if v not in adj or True]
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
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            out.append((a, b))
    return out


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _twins(n0, e0, d, rng)
        e1 = _saturate(n1, e1, d, rng)
        consider(n1, e1)

    elapsed = time.monotonic() - t_start
    budget = 0.82 * time_limit - elapsed - 1.5
    if budget >= 1.0 and d >= 2 and D >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e), timeout=budget + 5.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
