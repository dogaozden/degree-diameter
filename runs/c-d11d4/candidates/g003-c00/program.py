import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: randomized cover-based vertex insertion with edge saturation.
# A new vertex v joined to a set S keeps all old distances (it only shortens
# paths) and has dist(v, w) <= D exactly when w lies within D-1 of S. Adding
# edges also only shortens distances. So every step keeps the graph valid.
# The engine re-verifies the final graph and falls back to its input if the
# check fails.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static int D_DEG = 0, D_DIAM = 0;
static int n = 0, ncap = 0, W = 0;
static int *deg = NULL, *dcap = NULL, *color = NULL;
static int *candbuf = NULL, *gains = NULL, *chosen = NULL;
static char *used = NULL;
static int **adj = NULL;
static u64 *ball = NULL, *tmpb = NULL, *cov = NULL;
static u64 rs = 88172645463325252ULL;
static double deadline = 0.0;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return k <= 0 ? 0 : (int)(rnd() % (u64)k); }
static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void ensure_cap(int need) {
    if (need <= ncap) return;
    int nc = ncap ? ncap : 64;
    while (nc < need) nc *= 2;
    deg = realloc(deg, sizeof(int) * (size_t)nc);
    dcap = realloc(dcap, sizeof(int) * (size_t)nc);
    adj = realloc(adj, sizeof(int *) * (size_t)nc);
    color = realloc(color, sizeof(int) * (size_t)nc);
    candbuf = realloc(candbuf, sizeof(int) * (size_t)nc);
    gains = realloc(gains, sizeof(int) * (size_t)nc);
    chosen = realloc(chosen, sizeof(int) * (size_t)nc);
    used = realloc(used, (size_t)nc);
    for (int i = ncap; i < nc; i++) {
        deg[i] = 0; dcap[i] = 0; adj[i] = NULL; color[i] = 0;
    }
    ncap = nc;
    W = (ncap + 63) / 64;
    free(ball); free(tmpb); free(cov);
    ball = malloc(sizeof(u64) * (size_t)ncap * (size_t)W);
    tmpb = malloc(sizeof(u64) * (size_t)ncap * (size_t)W);
    cov = malloc(sizeof(u64) * (size_t)W);
}

static void add_arc(int u, int v) {
    if (deg[u] == dcap[u]) {
        dcap[u] = dcap[u] ? 2 * dcap[u] : 16;
        adj[u] = realloc(adj[u], sizeof(int) * (size_t)dcap[u]);
    }
    adj[u][deg[u]++] = v;
}

static void add_edge(int u, int v) { add_arc(u, v); add_arc(v, u); }

static int adjacent(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void compute_balls(int r) {
    size_t sz = (size_t)n * (size_t)W;
    memset(ball, 0, sizeof(u64) * sz);
    for (int v = 0; v < n; v++) ball[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = tmpb + (size_t)v * W;
            const u64 *src = ball + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const u64 *o = ball + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= o[w];
            }
        }
        u64 *t = ball; ball = tmpb; tmpb = t;
    }
}

static int covers_all(const u64 *b) {
    int cnt = 0;
    for (int w = 0; w < W; w++) cnt += popc(b[w]);
    return cnt == n;
}

static int bipartize(void) {
    int *st = malloc(sizeof(int) * (size_t)(n + 1));
    for (int v = 0; v < n; v++) color[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp) {
            int u = st[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (color[v] == -1) { color[v] = 1 - color[u]; st[sp++] = v; }
                else if (color[v] == color[u]) ok = 0;
            }
        }
    }
    free(st);
    return ok;
}

static int valid_state(void) {
    for (int v = 0; v < n; v++) if (deg[v] > D_DEG) return 0;
    if (!bipartize()) return 0;
    compute_balls(D_DIAM);
    for (int v = 0; v < n; v++) if (!covers_all(ball + (size_t)v * W)) return 0;
    return 1;
}

/* Randomized greedy cover of all n vertices by balls (radius D-1) of
   candidates on colour c. Returns number of chosen vertices, or -1. */
static int try_cover(int c, int *out) {
    int ncand = 0;
    for (int v = 0; v < n; v++)
        if (color[v] == c && deg[v] < D_DEG) candbuf[ncand++] = v;
    if (ncand == 0) return -1;
    memset(used, 0, (size_t)ncand);
    memset(cov, 0, sizeof(u64) * (size_t)W);
    int covered = 0, k = 0;
    while (covered < n && k < D_DEG) {
        int bestg = 0;
        for (int i = 0; i < ncand; i++) {
            if (used[i]) { gains[i] = 0; continue; }
            const u64 *b = ball + (size_t)candbuf[i] * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(b[w] & ~cov[w]);
            gains[i] = g;
            if (g > bestg) bestg = g;
        }
        if (bestg == 0) break;
        int thr = bestg;
        if (bestg > 1 && rndi(3) == 0) thr = bestg - 1;
        int cnt = 0, pick = -1;
        for (int i = 0; i < ncand; i++) {
            if (!used[i] && gains[i] >= thr) {
                cnt++;
                if (rndi(cnt) == 0) pick = i;
            }
        }
        if (pick < 0) break;
        used[pick] = 1;
        int s = candbuf[pick];
        out[k++] = s;
        const u64 *b = ball + (size_t)s * W;
        covered = 0;
        for (int w = 0; w < W; w++) { cov[w] |= b[w]; covered += popc(cov[w]); }
    }
    return covered == n ? k : -1;
}

static int try_add(int c) {
    for (int att = 0; att < 40; att++) {
        if (now_sec() >= deadline) return 0;
        int k = try_cover(c, chosen);
        if (k > 0) {
            int v = n;
            ensure_cap(n + 1);
            n = n + 1;
            color[v] = 1 - c;
            for (int i = 0; i < k; i++) add_edge(chosen[i], v);
            return 1;
        }
    }
    return 0;
}

static void saturate(void) {
    int *L = malloc(sizeof(int) * (size_t)(n + 1));
    int *R = malloc(sizeof(int) * (size_t)(n + 1));
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < D_DEG) {
            if (color[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < D_DEG; j++) {
            int b = R[j];
            if (deg[b] >= D_DEG || adjacent(a, b)) continue;
            add_edge(a, b);
        }
    }
    free(L);
    free(R);
}

static void print_adj(void) {
    long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    double t0 = now_sec();
    D_DEG = atoi(argv[1]);
    D_DIAM = atoi(argv[2]);
    rs ^= (u64)(atoll(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    deadline = t0 + atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int readok = 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { readok = 0; m0 = i; break; }
    }

    ensure_cap(n0 + 1);
    n = n0;
    int ok = readok;
    for (int i = 0; i < m0 && ok; i++) {
        int u = iu[i], v = iv[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjacent(u, v)) ok = 0;
        else add_edge(u, v);
    }
    if (ok) ok = valid_state();
    if (!ok) {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    while (now_sec() < deadline) {
        saturate();
        compute_balls(D_DIAM - 1);
        int first = rndi(2);
        int grown = 0;
        for (int t = 0; t < 2 && !grown; t++) {
            if (try_add(t == 0 ? first : 1 - first)) grown = 1;
        }
        if (!grown) break;
    }

    if (valid_state()) {
        print_adj();
    } else {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions.
# ----------------------------------------------------------------------------

def _largest_pp(hi, cap=None):
    """Largest prime power q with 2 <= q <= min(hi, cap)."""
    top = hi if cap is None else min(hi, cap)
    for q in range(top, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_base(d):
    """PG(2, q) incidence graph, q the largest prime power with q + 1 <= d, with its 2-colouring."""
    q = _largest_pp(d - 1)
    if q is None:
        return None
    n, e = lib.projective_plane_incidence(q)
    half = n // 2
    return n, e, [0] * half + [1] * half


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are 0..P-1 and lines P..2P-1. Degree is q + 1 and diameter is 4.
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


def _gq_base(d):
    """W(q) with q the largest prime power <= d - 1 (capped at 9 for speed), with its 2-colouring."""
    q = _largest_pp(d - 1, cap=9)
    if q is None:
        return None
    n, e = _gq_w(q)
    half = n // 2
    return n, e, [0] * half + [1] * half


def _saturate(n, edges, d, color, rng):
    """Add edges between deficient opposite-colour vertices. Edges only shorten distances."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((u, v) if u < v else (v, u))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    rng.shuffle(left)
    rng.shuffle(right)
    for a in left:
        for b in right:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in existing:
                continue
            existing.add(key)
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        base = _pg_base(d) if D == 3 else _gq_base(d)
        if base is not None:
            n0, e0, color = base
            consider(n0, _saturate(n0, e0, d, color, rng))
            n1 = best[0]
            e1 = best[1]
            # Re-saturate from the best valid candidate so the C engine starts with spare slack filled.
            if n1 != n0:
                pass
            else:
                e1 = _saturate(n0, e0, d, color, rng)
            n1, e1 = n0, e1

            remaining = time_limit - (time.monotonic() - start)
            budget = remaining * 0.8 - 1.0
            if budget > 2.0:
                try:
                    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                    stdin_graph=(n1, e1), timeout=budget + 2.0)
                    n2, e2 = lib.parse_graph_text(out)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
