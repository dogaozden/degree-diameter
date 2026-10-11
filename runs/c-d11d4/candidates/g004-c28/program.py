import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: random walk over VALID bipartite graphs (max degree d, diameter <= D).
#   * saturate: add edges between deficient opposite-side vertices (always valid).
#   * cover: try to add a new vertex whose neighbours (<= d, deficient, opposite
#     side) have radius-(D-1) balls covering every existing vertex. Found by
#     simulated annealing over the neighbour set. Always valid.
#   * perturb: remove random edges and do 2-switches, keeping a state only if the
#     full diameter check still passes. This frees degree so covers can appear.
# The state is never invalid, so the output is always valid (Python re-checks).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW 64
#define MOVES 2000
#define PERT 4
#define SWITCHES 4
#define DEBRUIJN 0x03f79d71b4cb0a89ULL

typedef uint64_t row_t[MAXW];

static int d, D, R, CAP, W, n;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int color[MAXN];
static row_t bufX[MAXN];
static row_t bufY[MAXN];
static int cnt[MAXN];
static char inS[MAXN];
static int tab64[64];
static uint64_t rs;
static clock_t t0;
static double tl;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int ctz64(uint64_t x) {
    return tab64[((x & (~x + 1)) * DEBRUIJN) >> 58];
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void del_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void colour(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int h = 0, tq = 0;
        q[tq++] = s;
        while (h < tq) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (color[w] == -1) { color[w] = 1 - color[u]; q[tq++] = w; }
            }
        }
    }
}

/* Radius-r balls as bitsets; returns the buffer holding the result. */
static row_t *compute_balls(int r) {
    row_t *cur = bufX, *nxt = bufY;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int j = 0; j < W; j++) nxt[v][j] |= cur[u][j];
            }
        }
        row_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    return cur;
}

static int full_valid(void) {
    row_t *B = compute_balls(D);
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int j = 0; j < W; j++) c += pc64(B[v][j]);
        if (c != n) return 0;
    }
    return 1;
}

static void bits_add(const uint64_t *row, int *unc) {
    for (int j = 0; j < W; j++) {
        uint64_t x = row[j];
        while (x) {
            uint64_t low = x & (~x + 1);
            int w = (j << 6) + ctz64(low);
            x ^= low;
            if (cnt[w] == 0) (*unc)--;
            cnt[w]++;
        }
    }
}

static void bits_rem(const uint64_t *row, int *unc) {
    for (int j = 0; j < W; j++) {
        uint64_t x = row[j];
        while (x) {
            uint64_t low = x & (~x + 1);
            int w = (j << 6) + ctz64(low);
            x ^= low;
            cnt[w]--;
            if (cnt[w] == 0) (*unc)++;
        }
    }
}

/* Try to add one vertex on side c whose neighbours cover all vertices by radius-R balls. */
static int cover_attempt(int c, row_t *B, int moves) {
    if (n >= CAP) return 0;
    static int pool[MAXN];
    int np = 0;
    for (int v = 0; v < n; v++) if (color[v] != c && deg[v] < d) pool[np++] = v;
    if (np == 0) return 0;
    int k = np < d ? np : d;
    shuffle_int(pool, np);
    memset(cnt, 0, sizeof(int) * (size_t)n);
    memset(inS, 0, (size_t)n);
    int S[MAXD];
    for (int i = 0; i < k; i++) { S[i] = pool[i]; inS[S[i]] = 1; }
    int unc = n;
    for (int i = 0; i < k; i++) bits_add(B[S[i]], &unc);
    for (int it = 0; it < moves && unc > 0; it++) {
        double T = 1.0 + (0.02 - 1.0) * (double)it / (double)moves;
        int i = rndint(k);
        int t = pool[rndint(np)];
        if (inS[t]) continue;
        int s = S[i];
        int old = unc;
        bits_rem(B[s], &unc);
        bits_add(B[t], &unc);
        int delta = unc - old;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            inS[s] = 0; inS[t] = 1; S[i] = t;
        } else {
            bits_rem(B[t], &unc);
            bits_add(B[s], &unc);
        }
    }
    if (unc != 0) return 0;
    int v = n;
    color[v] = c;
    deg[v] = 0;
    n++;
    for (int i = 0; i < k; i++) add_edge(S[i], v);
    return 1;
}

static void saturate(void) {
    static int L[MAXN], Rr[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (color[v] == 0) L[nl++] = v; else Rr[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(Rr, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d; j++) {
            int b = Rr[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void try_remove(void) {
    int a = rndint(n);
    if (deg[a] == 0) return;
    int b = adj[a][rndint(deg[a])];
    del_edge(a, b);
    if (!full_valid()) add_edge(a, b);
}

static void try_switch(void) {
    int a = rndint(n);
    if (deg[a] == 0) return;
    int b = adj[a][rndint(deg[a])];
    int c = rndint(n);
    if (deg[c] == 0) return;
    int e = adj[c][rndint(deg[c])];
    if (a == c || b == e) return;
    if (color[a] != color[c]) return;
    if (has_edge(a, e) || has_edge(c, b)) return;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    if (!full_valid()) {
        del_edge(a, e);
        del_edge(c, b);
        add_edge(a, b);
        add_edge(c, e);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    for (int i = 0; i < 64; i++) tab64[((1ULL << i) * DEBRUIJN) >> 58] = i;
    t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 <= 0 || n0 > MAXN || d < 1 || d >= MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    R = D - 1;
    CAP = n0 + n0 / 2 + 64;
    if (CAP > MAXN) CAP = MAXN;
    if (CAP > MAXW * 64) CAP = MAXW * 64;
    W = (CAP + 63) / 64;
    colour();

    if (!full_valid()) {
        /* Start is not valid: echo it, the caller will reject or ignore it. */
        int m = 0;
        for (int v = 0; v < n; v++) m += deg[v];
        printf("%d %d\n", n, m / 2);
        for (int v = 0; v < n; v++)
            for (int i = 0; i < deg[v]; i++)
                if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
        return 0;
    }

    while (elapsed() < tl) {
        row_t *B = compute_balls(R);
        int first = rndint(2);
        int success = 0;
        for (int q = 0; q < 2 && !success; q++) {
            int c = (q == 0) ? first : 1 - first;
            if (cover_attempt(c, B, MOVES)) success = 1;
        }
        if (success) {
            saturate();
            continue;
        }
        for (int p = 0; p < PERT && elapsed() < tl; p++) try_remove();
        for (int p = 0; p < SWITCHES && elapsed() < tl; p++) try_switch();
    }

    int m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    printf("%d %d\n", n, m / 2);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (starts and a cheap fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); degree q + 1, diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q <= 11 to bound build time."""
    for q in range(d - 1, 1, -1):
        if q <= 11 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same neighbourhood) while neighbours have spare degree. Keeps diameter."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


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
    """Greedy cover of `full` by at most d candidate balls; returns chosen list or None."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within radius D-1."""
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
    """Greedily join deficient opposite-side vertices. Only adds edges, so diameter is kept."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration: already at the Moore bound, nothing to improve.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Python starts: twin growth, then a bounded cover growth on the best start.
    tw_deadline = min(deadline, time.monotonic() + 0.1 * time_limit)
    tn, te = _twin_grow(best[0], best[1], d, rng, tw_deadline)
    consider(tn, te)

    cg_deadline = min(deadline, start + 0.3 * time_limit)
    if time.monotonic() < cg_deadline:
        n2, e2 = _extend_cover(best[0], best[1], d, D, cg_deadline, rng)
        consider(n2, e2)
        n3, e3 = _saturate_edges(n2, e2, d, rng)
        consider(n3, e3)

    # Main step: C random walk with cover additions and perturbations, from the best start.
    rem = deadline - time.monotonic() - 1.5
    if rem >= 2.0 and best_n <= 4000:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(rem, 2)],
                            stdin_graph=best, timeout=rem + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
