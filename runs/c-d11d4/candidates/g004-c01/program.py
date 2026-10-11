import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* Bitset-based vertex extension and edge saturation for bipartite graphs with
   max degree d and diameter <= D. A new vertex v on side 1-c is added with
   neighbourhood S (<= d deficient vertices on side c) iff the radius-(D-1) balls
   of S cover all existing vertices. Old distances can only shrink, so validity
   is preserved. Saturation adds edges between deficient opposite-side vertices,
   which also preserves validity. */

static int d, D, n, cap, W, maxN;
static int *adj, *dg, *col;
static uint64_t *bA, *bB, *fullm;
static uint64_t rs = 88172645463325252ULL;

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static int popc(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static void ensure_cap(int need) {
    if (need <= cap) return;
    int nc = cap * 2;
    if (nc < need) nc = need;
    if (nc < 64) nc = 64;
    adj = realloc(adj, sizeof(int) * (size_t)nc * (size_t)d);
    dg = realloc(dg, sizeof(int) * (size_t)nc);
    col = realloc(col, sizeof(int) * (size_t)nc);
    bA = realloc(bA, sizeof(uint64_t) * (size_t)nc * (size_t)W);
    bB = realloc(bB, sizeof(uint64_t) * (size_t)nc * (size_t)W);
    if (!adj || !dg || !col || !bA || !bB) { fprintf(stderr, "oom\n"); exit(1); }
    cap = nc;
}

static int adjacent(int a, int b) {
    for (int i = 0; i < dg[a]; i++) if (adj[a * d + i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a * d + dg[a]++] = b;
    adj[b * d + dg[b]++] = a;
}

static void make_full(void) {
    memset(fullm, 0, sizeof(uint64_t) * (size_t)W);
    for (int v = 0; v < n; v++) fullm[v >> 6] |= 1ULL << (v & 63);
}

static int is_full(const uint64_t *x) {
    for (int w = 0; w < W; w++) if (x[w] != fullm[w]) return 0;
    return 1;
}

/* Returns a pointer (bA or bB) holding, for each vertex, the bitset of vertices within distance R. */
static uint64_t *compute_balls(int R) {
    uint64_t *cur = bA, *nxt = bB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *self = cur + (size_t)v * W;
            memcpy(out, self, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *u = cur + (size_t)adj[v * d + i] * W;
                for (int w = 0; w < W; w++) out[w] |= u[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static int full_valid(void) {
    make_full();
    uint64_t *b = compute_balls(D);
    for (int v = 0; v < n; v++)
        if (!is_full(b + (size_t)v * W)) return 0;
    return 1;
}

static int color_graph(void) {
    int *st = malloc(sizeof(int) * (size_t)(n + 1));
    int ok = 1;
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0 && ok) {
            int u = st[--sp];
            for (int i = 0; i < dg[u]; i++) {
                int v = adj[u * d + i];
                if (col[v] < 0) { col[v] = 1 - col[u]; st[sp++] = v; }
                else if (col[v] == col[u]) { ok = 0; break; }
            }
        }
    }
    free(st);
    return ok;
}

static int load_edges(int m0, const int *eu, const int *ev) {
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (dg[a] >= d || dg[b] >= d) return 0;
        if (adjacent(a, b)) return 0;
        add_edge(a, b);
    }
    if (!color_graph()) return 0;
    return full_valid();
}

/* Randomized greedy set cover of all vertices by <= d deficient side-c vertices. */
static int try_extend(int c, int attempts, double deadline) {
    if (n + 1 > maxN || n + 1 > W * 64) return 0;
    ensure_cap(n + 1);
    int nc = 0;
    int *cands = malloc(sizeof(int) * (size_t)(n + 1));
    for (int v = 0; v < n; v++)
        if (col[v] == c && dg[v] < d) cands[nc++] = v;
    if (nc == 0) { free(cands); return 0; }
    uint64_t *ball = compute_balls(D - 1);
    make_full();
    int *pool = malloc(sizeof(int) * (size_t)nc);
    int *gains = malloc(sizeof(int) * (size_t)nc);
    int *chosen = malloc(sizeof(int) * (size_t)(d + 1));
    uint64_t *cov = malloc(sizeof(uint64_t) * (size_t)W);
    int found = 0, k = 0;
    for (int at = 0; at < attempts && !found; at++) {
        if ((at & 7) == 0 && now() > deadline) break;
        memcpy(pool, cands, sizeof(int) * (size_t)nc);
        int avail = nc, randomize = (at > 0);
        k = 0;
        memset(cov, 0, sizeof(uint64_t) * (size_t)W);
        for (;;) {
            if (is_full(cov)) { found = 1; break; }
            if (k >= d || avail == 0) break;
            int bestg = 0;
            for (int i = 0; i < avail; i++) {
                const uint64_t *bs = ball + (size_t)pool[i] * W;
                int g = 0;
                for (int w = 0; w < W; w++) g += popc(bs[w] & ~cov[w]);
                gains[i] = g;
                if (g > bestg) bestg = g;
            }
            if (bestg == 0) break;
            int thr = bestg;
            if (randomize && bestg > 1 && rndint(2) == 0) thr = bestg - 1;
            int opts = 0;
            for (int i = 0; i < avail; i++) if (gains[i] >= thr && gains[i] > 0) opts++;
            int pick = randomize ? rndint(opts) : 0;
            int idx = -1;
            for (int i = 0; i < avail; i++) {
                if (gains[i] >= thr && gains[i] > 0) {
                    if (pick == 0) { idx = i; break; }
                    pick--;
                }
            }
            int s = pool[idx];
            pool[idx] = pool[avail - 1];
            avail--;
            chosen[k++] = s;
            const uint64_t *bs = ball + (size_t)s * W;
            for (int w = 0; w < W; w++) cov[w] |= bs[w];
        }
    }
    int ok = found;
    if (ok) {
        int v = n++;
        col[v] = 1 - c;
        dg[v] = 0;
        for (int i = 0; i < k; i++) add_edge(chosen[i], v);
    }
    free(cands); free(pool); free(gains); free(chosen); free(cov);
    return ok;
}

static void shuffle_ints(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add edges between deficient opposite-side vertices. Returns number added. */
static int saturate(void) {
    int *L = malloc(sizeof(int) * (size_t)(n + 1));
    int *R = malloc(sizeof(int) * (size_t)(n + 1));
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (dg[v] < d) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_ints(L, nl);
    shuffle_ints(R, nr);
    int added = 0;
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && dg[a] < d; j++) {
            int b = R[j];
            if (dg[b] < d && !adjacent(a, b)) {
                add_edge(a, b);
                added++;
            }
        }
    }
    free(L); free(R);
    return added;
}

static void print_graph(void) {
    long m = 0;
    for (int v = 0; v < n; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < dg[v]; i++) {
            int u = adj[v * d + i];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = now() + budget;
    if (d < 1) { printf("1 0\n"); return 0; }

    double mooreD;
    if (D <= 0) mooreD = 1;
    else if (d == 1) mooreD = 2;
    else if (d == 2) mooreD = 2.0 * D;
    else {
        double s = 0, p = 1;
        for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
        mooreD = 2.0 * s;
    }
    if (mooreD > 1e6) mooreD = 1e6;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) { n0 = 0; m0 = 0; }
    maxN = (int)mooreD;
    if (maxN < n0) maxN = n0;
    maxN += 2;
    W = (maxN + 63) / 64;
    fullm = malloc(sizeof(uint64_t) * (size_t)W);

    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int ma = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        ma++;
    }

    int ok = 0;
    if (n0 > 0 && n0 <= maxN - 2) {
        n = n0;
        ensure_cap(n0 + 64);
        ok = load_edges(ma, eu, ev);
    }
    if (!ok) {
        n = 2 * d;
        ensure_cap(n + 64);
        for (int v = 0; v < n; v++) dg[v] = 0;
        for (int i = 0; i < d; i++) col[i] = 0;
        for (int j = 0; j < d; j++) col[d + j] = 1;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) add_edge(i, d + j);
    }

    int att = 200;
    while (now() < deadline) {
        int grown = 0;
        int first = rndint(2);
        for (int t = 0; t < 2 && !grown && now() < deadline; t++)
            grown = try_extend(t == 0 ? first : 1 - first, att, deadline);
        if (grown) { att = 200; continue; }
        if (saturate() > 0) { att = 200; continue; }
        if (att >= (1 << 20)) break;
        att *= 2;
    }

    print_graph();
    return 0;
}
"""


def _safe(fn, *args):
    """Call a construction, returning None instead of raising."""
    try:
        return fn(*args)
    except Exception:
        return None


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_base(d):
    """Araujo-Pardo and Lopez graph for d = q + 2 with q a prime power (not used by the parent)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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


def _gq_base(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16 to keep construction fast)."""
    for q in range(min(d - 1, 16), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    if D == 2:
        return best

    def consider(g):
        nonlocal best
        if g is None:
            return
        try:
            n, e = g
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    # Structured bases. Araujo-Lopez is used for D = 3 when d - 2 is a prime power.
    if D == 3:
        consider(_safe(_pg_base, d))
        consider(_safe(_araujo_base, d))
    else:
        consider(_safe(_gq_base, d) if D >= 4 else None)
        consider(_safe(_pg_base, d))

    # Calibration cases already at the Moore bound return immediately.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Remaining budget for the C engine (leave room for compile and final checks).
    left = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if left >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(left, 2)],
                            stdin_graph=best, timeout=left + 1.5)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
