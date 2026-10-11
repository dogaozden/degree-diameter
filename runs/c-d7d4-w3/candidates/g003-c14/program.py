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

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)
#define ITERS 3000L
#define STALL_RESET 400

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXD];
} G;

static G cur, work, best;
static int DD = 4, DM = 3;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t TA[MAXN * MAXW], TB[MAXN * MAXW];

static inline uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static inline double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static inline int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) if (g->nb[a][i] == b) return 1;
    return 0;
}
static void del_nb(G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->nb[a][i] == b) {
            g->nb[a][i] = g->nb[a][--g->deg[a]];
            return;
        }
    }
}
static void del_edge(G *g, int a, int b) { del_nb(g, a, b); del_nb(g, b, a); }
static void add_edge(G *g, int a, int b) {
    g->nb[a][g->deg[a]++] = b;
    g->nb[b][g->deg[b]++] = a;
}

/* ball[v] = bitset of vertices within distance r of v. Returns TA or TB (valid until next call). */
static uint64_t *ballsR(const G *g, int r) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *cu = TA, *nx = TB;
    memset(cu, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cu[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx + (size_t)v * W;
            memcpy(o, cu + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cu + (size_t)g->nb[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cu; cu = nx; nx = t;
    }
    return cu;
}

/* Number of unordered pairs at distance > DD (unreachable pairs included). */
static long cost_of(const G *g) {
    int n = g->n, W = (n + 63) >> 6;
    const uint64_t *b = ballsR(g, DD);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(b[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i]; x[i] = x[j]; x[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (never hurts the diameter). */
static void fill(G *g) {
    static int L[MAXN], R[MAXN];
    int n = g->n, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] < DM) {
            if (g->side[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && g->deg[a] < DM; j++) {
            int b = R[j];
            if (g->deg[b] < DM && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* Propose a degree-preserving bipartite switch a-b, c-e -> a-e, c-b. */
static int propose(const G *g, int *pa, int *pb, int *pc, int *pe) {
    int n = g->n;
    for (int tries = 0; tries < 20; tries++) {
        int a = rndi(n);
        if (g->side[a] != 0 || g->deg[a] == 0) continue;
        int c = rndi(n);
        if (g->side[c] != 0 || g->deg[c] == 0 || c == a) continue;
        int b = g->nb[a][rndi(g->deg[a])];
        int e = g->nb[c][rndi(g->deg[c])];
        if (b == e || has_edge(g, a, e) || has_edge(g, c, b)) continue;
        *pa = a; *pb = b; *pc = c; *pe = e;
        return 1;
    }
    return 0;
}
static void apply_switch(G *g, int a, int b, int c, int e) {
    del_edge(g, a, b);
    del_edge(g, c, e);
    add_edge(g, a, e);
    add_edge(g, c, b);
}
static void undo_switch(G *g, int a, int b, int c, int e) {
    del_edge(g, a, e);
    del_edge(g, c, b);
    add_edge(g, a, b);
    add_edge(g, c, e);
}

static void perturb(G *g, int k) {
    for (int i = 0; i < k; i++) {
        int a, b, c, e;
        if (propose(g, &a, &b, &c, &e)) apply_switch(g, a, b, c, e);
    }
}

/* Simulated annealing on switches minimising bad pairs. Returns remaining cost (0 = valid). */
static long anneal(G *g, long iters, double T0, double T1, double deadline) {
    long cc = cost_of(g);
    for (long it = 0; it < iters && cc > 0; it++) {
        if ((it & 63) == 0 && now() > deadline) break;
        int a, b, c, e;
        if (!propose(g, &a, &b, &c, &e)) continue;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        apply_switch(g, a, b, c, e);
        long nc = cost_of(g);
        long dl = nc - cc;
        if (dl <= 0 || rndf() < exp(-(double)dl / T)) {
            cc = nc;
        } else {
            undo_switch(g, a, b, c, e);
        }
    }
    return cc;
}

static int covered_all(const uint64_t *cov, int n) {
    int W = (n + 63) >> 6;
    for (int w = 0; w < W; w++) {
        uint64_t m = ~0ULL;
        if (w == W - 1 && (n & 63)) m = (1ULL << (n & 63)) - 1;
        if ((cov[w] & m) != m) return 0;
    }
    return 1;
}

/* Append a vertex on side c, joined to a greedy cover of the opposite side. */
static int add_vertex(G *g, int c) {
    int n = g->n;
    if (n + 1 >= MAXN) return 0;
    int W = (n + 63) >> 6;
    const uint64_t *b = ballsR(g, DD - 1);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nc = 0;
    for (int p = 0; p < DM; p++) {
        int best_s = -1;
        long bestsc = -1;
        for (int s = 0; s < n; s++) {
            if (g->side[s] == c) continue;
            int inch = 0;
            for (int i = 0; i < nc; i++) if (chosen[i] == s) { inch = 1; break; }
            if (inch) continue;
            long gain = 0;
            for (int w = 0; w < W; w++) gain += popc(b[(size_t)s * W + w] & ~cov[w]);
            long sc = gain * 64 + rndi(64);
            if (sc > bestsc) { bestsc = sc; best_s = s; }
        }
        if (best_s < 0) break;
        chosen[nc++] = best_s;
        for (int w = 0; w < W; w++) cov[w] |= b[(size_t)best_s * W + w];
        if (covered_all(cov, n)) break;
    }
    int v = n;
    g->n = n + 1;
    g->side[v] = c;
    g->deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (g->deg[s] >= DM) {
            int t = g->nb[s][rndi(g->deg[s])];
            del_edge(g, s, t);
        }
        add_edge(g, v, s);
    }
    return 1;
}

/* Delete vertex k, moving the last vertex into its slot. */
static void remove_vertex(G *g, int k) {
    while (g->deg[k] > 0) del_edge(g, k, g->nb[k][0]);
    int L = g->n - 1;
    if (k != L) {
        for (int i = 0; i < g->deg[L]; i++) {
            int u = g->nb[L][i];
            for (int j = 0; j < g->deg[u]; j++) {
                if (g->nb[u][j] == L) { g->nb[u][j] = k; break; }
            }
        }
        g->deg[k] = g->deg[L];
        memcpy(g->nb[k], g->nb[L], sizeof(int) * g->deg[L]);
        g->side[k] = g->side[L];
    }
    g->deg[L] = 0;
    g->n = L;
}

static void gcopy(G *dst, const G *src) {
    int n = src->n;
    dst->n = n;
    memcpy(dst->side, src->side, sizeof(int) * n);
    memcpy(dst->deg, src->deg, sizeof(int) * n);
    for (int i = 0; i < n; i++) memcpy(dst->nb[i], src->nb[i], sizeof(int) * src->deg[i]);
}

static void read_start(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    memset(&cur, 0, sizeof cur);
    if (n0 <= 0) {
        cur.n = 2 * DM;
        for (int v = 0; v < cur.n; v++) cur.side[v] = (v < DM) ? 0 : 1;
        for (int a = 0; a < DM; a++)
            for (int b = DM; b < 2 * DM; b++) add_edge(&cur, a, b);
        return;
    }
    cur.n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (cur.deg[u] >= DM || cur.deg[v] >= DM || has_edge(&cur, u, v)) continue;
        add_edge(&cur, u, v);
    }
    static int col[MAXN], q[MAXN];
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < cur.deg[x]; i++) {
                int y = cur.nb[x][i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
            }
        }
    }
    for (int v = 0; v < n0; v++) cur.side[v] = col[v];
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DM = d < 1 ? 1 : (d > MAXD ? MAXD : d);
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();

    double t_end = now() + budget;
    read_start();

    int have_best = 0;
    if (cost_of(&cur) == 0) {
        gcopy(&best, &cur);
        have_best = 1;
    } else {
        if (anneal(&cur, 20000, 1.0, 0.05, t_end) == 0) {
            gcopy(&best, &cur);
            have_best = 1;
        }
    }

    long stall = 0;
    while (now() < t_end) {
        gcopy(&work, &cur);
        int r = rndi(10);
        int target = cur.n;
        int ok = 1;
        if (r < 5) {
            if (!add_vertex(&work, rndi(2))) ok = 0;
        } else if (r < 8) {
            int k = 1 + rndi(3);
            for (int i = 0; i < k && work.n > 2; i++) remove_vertex(&work, rndi(work.n));
            while (ok && work.n < target) {
                if (!add_vertex(&work, rndi(2))) ok = 0;
            }
        } else {
            perturb(&work, 4 + rndi(12));
        }
        if (!ok) continue;
        fill(&work);
        long left = anneal(&work, ITERS, 1.0, 0.08, t_end);
        if (left == 0) {
            if (!have_best || work.n > best.n) {
                gcopy(&best, &work);
                have_best = 1;
            }
            gcopy(&cur, &work);
            stall = 0;
        } else if (++stall > STALL_RESET && have_best) {
            gcopy(&cur, &best);
            stall = 0;
        }
    }

    const G *out = have_best ? &best : &cur;
    long m = 0;
    for (int v = 0; v < out->n; v++)
        for (int i = 0; i < out->deg[v]; i++)
            if (out->nb[v][i] > v) m++;
    printf("%d %ld\n", out->n, m);
    for (int v = 0; v < out->n; v++)
        for (int i = 0; i < out->deg[v]; i++)
            if (out->nb[v][i] > v) printf("%d %d\n", v, out->nb[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

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


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Cheap Python-side densification (both steps keep validity).
# ----------------------------------------------------------------------------

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


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices greedily in random order."""
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


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins while neighbours have spare degree (keeps distances and bipartiteness)."""
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


def _prepare_base(d, D, rng):
    """Best valid starting graph among the structured constructions, densified."""
    cands = []
    if D >= 4:
        g = _best_gq(d)
        if g is not None:
            cands.append(g)
    if D >= 3:
        g = _best_pg(d)
        if g is not None:
            cands.append(g)
    cands.append(lib.haar_graph(d, range(d)))

    best = None
    for n, e in cands:
        if not lib.is_valid(n, e, d, D):
            continue
        if best is None or n > best[0]:
            best = (n, list(e))
        e1 = _saturate_edges(n, e, d, rng)
        if lib.is_valid(n, e1, d, D) and n > best[0]:
            best = (n, e1)
        if D >= 2:
            n2, e2 = _duplicate_twins(n, e1, d, rng)
            e2 = _saturate_edges(n2, e2, d, rng)
            if lib.is_valid(n2, e2, d, D) and n2 > best[0]:
                best = (n2, e2)
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    rng = random.Random(seed)
    base = _prepare_base(d, D, rng)
    if base is None:
        base = fallback
    best_n, best_e = base

    if D < 2 or d < 2 or d > 31:
        return best_n, list(best_e)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best_n, list(best_e)

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(best_n, best_e), timeout=time_limit * 0.9)
        n, e = lib.parse_graph_text(out)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
