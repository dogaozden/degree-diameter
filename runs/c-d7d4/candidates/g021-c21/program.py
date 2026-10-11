import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2400
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 64
#define ANN 1500
#define BADCAP 60

typedef uint64_t row_t[MAXW];

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXDEG];
} State;

static int dmax, Dlim;
static int n;
static int side[MAXN], deg[MAXN], nb[MAXN][MAXDEG];
static row_t bufA[MAXN], bufB[MAXN];
static char chosenf[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double budget;
static clock_t t0;
static State stA, stB, stBest;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) {
    return ((double)(clock() - t0)) / CLOCKS_PER_SEC >= budget;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (nb[u][i] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
    }
}
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Bitset balls of radius r; returns the buffer holding them. */
static row_t *balls(int r) {
    int W = (n + 63) >> 6;
    row_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, (size_t)W * 8);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], (size_t)W * 8);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        row_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > Dlim. */
static long cost(void) {
    int W = (n + 63) >> 6;
    row_t *B = balls(Dlim);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(B[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add a vertex on side s joined to a greedy cover of the other side. */
static int add_vertex(void) {
    if (n + 2 >= MAXN) return 0;
    int s = rnd(2);
    int W = (n + 63) >> 6;
    row_t *B = balls(Dlim - 1);
    row_t cov;
    memset(cov, 0, sizeof cov);
    int chosen[MAXDEG];
    int nc = 0;
    for (int k = 0; k < dmax; k++) {
        int best = -1;
        double bs = -1.0;
        for (int w = 0; w < n; w++) {
            if (side[w] == s || chosenf[w]) continue;
            int g = 0;
            for (int x = 0; x < W; x++) g += popc(B[w][x] & ~cov[x]);
            double sc = g + 0.5 * rnd01();
            if (sc > bs) { bs = sc; best = w; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        chosenf[best] = 1;
        for (int x = 0; x < W; x++) cov[x] |= B[best][x];
    }
    for (int i = 0; i < nc; i++) chosenf[chosen[i]] = 0;
    if (nc == 0) return 0;
    int v = n++;
    side[v] = s;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int w = chosen[i];
        if (deg[w] >= dmax) {
            int t = nb[w][rnd(deg[w])];
            del_edge(w, t);
        }
        add_edge(v, w);
    }
    return 1;
}

/* Add cross-side edges between deficient vertices (only shrinks distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    for (int pass = 0; pass < 3; pass++) {
        int nl = 0, nr = 0;
        for (int v = 0; v < n; v++) {
            if (deg[v] < dmax) {
                if (side[v] == 0) L[nl++] = v; else R[nr++] = v;
            }
        }
        shuffle(L, nl);
        shuffle(R, nr);
        for (int i = 0; i < nl; i++) {
            int a = L[i];
            for (int j = 0; j < nr && deg[a] < dmax; j++) {
                int b = R[j];
                if (deg[b] < dmax && !has_edge(a, b)) add_edge(a, b);
            }
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static int anneal(int iters) {
    long cur = cost();
    if (cur > BADCAP) return 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        int a = rnd(n);
        if (side[a] != 0 || deg[a] == 0) continue;
        int b = nb[a][rnd(deg[a])];
        int c = rnd(n);
        if (c == a || side[c] != 0 || deg[c] == 0) continue;
        int e = nb[c][rnd(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.1)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

/* Swap-remove vertex x, keeping labels 0..n-1 compact. */
static void remove_vertex(int x) {
    while (deg[x] > 0) del_edge(x, nb[x][0]);
    int L = n - 1;
    if (x != L) {
        for (int i = 0; i < deg[L]; i++) {
            int u = nb[L][i];
            for (int j = 0; j < deg[u]; j++) {
                if (nb[u][j] == L) { nb[u][j] = x; break; }
            }
        }
        side[x] = side[L];
        deg[x] = deg[L];
        memcpy(nb[x], nb[L], sizeof nb[L]);
    }
    n--;
}

static void kill_random(int k) {
    for (int i = 0; i < k && n > 3; i++) remove_vertex(rnd(n));
}

static void save_to(State *s) {
    s->n = n;
    memcpy(s->side, side, sizeof(int) * (size_t)n);
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->nb, nb, sizeof(int) * MAXDEG * (size_t)n);
}

static void load_from(const State *s) {
    n = s->n;
    memcpy(side, s->side, sizeof(int) * (size_t)n);
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(nb, s->nb, sizeof(int) * MAXDEG * (size_t)n);
}

static int read_start(void) {
    int m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 8 || m < 0) return 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) return 0;
        nb[u][deg[u]++] = v;
        nb[v][deg[v]++] = u;
    }
    return 1;
}

/* Two-colour the graph; returns 0 if it is not bipartite. */
static int color_ok(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void output_live(void) {
    long m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) m++;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) printf("%d %d\n", u, nb[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    Dlim = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    budget = atof(argv[4]);
    t0 = clock();

    if (!read_start()) {
        printf("0 0\n");
        return 0;
    }
    if (dmax > MAXDEG || dmax < 1 || Dlim < 2 || !color_ok() || cost() != 0) {
        output_live();
        return 0;
    }

    save_to(&stBest);
    int bestn = n;
    while (!timeup()) {
        save_to(&stA);
        int acc = 0;
        if (rnd(10) < 6) {
            if (add_vertex()) {
                fill();
                acc = anneal(ANN);
            }
        } else {
            kill_random(1 + rnd(3));
            fill();
            if (anneal(ANN)) {
                int fails = 0;
                while (fails < 3 && !timeup()) {
                    save_to(&stB);
                    if (add_vertex()) {
                        fill();
                        if (anneal(ANN)) { fails = 0; continue; }
                    }
                    load_from(&stB);
                    fails++;
                }
                acc = (n >= stA.n - 1);
            }
        }
        if (!acc) {
            load_from(&stA);
            continue;
        }
        if (n > bestn) {
            bestn = n;
            save_to(&stBest);
        } else if (n < bestn - 2 && rnd(2) == 0) {
            load_from(&stBest);
        }
    }
    load_from(&stBest);
    output_live();
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers: cover growth, saturation, twin duplication.
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within reach of a side."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover-vertex growth and saturation until nothing changes."""
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
            nbrs = adj[v]
            if not nbrs or len(nbrs) > d:
                continue
            if any(len(adj[u]) >= d for u in nbrs):
                continue
            w = len(adj)
            adj.append(set(nbrs))
            for u in nbrs:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
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

    def elapsed():
        return time.monotonic() - t_start

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        consider(base[0], base[1])
        best_n0, best_e0 = best_n, list(best_e)
    if D >= 2:
        n1, e1 = _grow(best_n, best_e, d, D, t_start + 0.12 * time_limit, rng)
        consider(n1, e1)
        nt, et = _duplicate_twins(best_n, best_e, d, rng)
        et = _saturate_edges(nt, et, d, rng)
        n2, e2 = _grow(nt, et, d, D, t_start + 0.18 * time_limit, rng)
        consider(n2, e2)

    # Main search in C: add-vertex and kill-repair-regrow with annealed repair.
    remaining = 0.92 * time_limit - elapsed() - 2.0
    if D >= 2 and remaining > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{max(0.2, remaining - 0.3):.2f}"],
                            stdin_graph=(best_n, best_e), timeout=remaining + 0.5)
            n3, e3 = lib.parse_graph_text(out)
            consider(n3, e3)
        except Exception:
            # Fall back to Python cover growth with the remaining time.
            while elapsed() < 0.85 * time_limit:
                n4, e4 = _duplicate_twins(best_n, best_e, d, rng)
                e4 = _saturate_edges(n4, e4, d, rng)
                n4, e4 = _grow(n4, e4, d, D, t_start + 0.85 * time_limit, rng)
                consider(n4, e4)
                break

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
