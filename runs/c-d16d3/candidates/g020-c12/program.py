import time

import lib


# ----------------------------------------------------------------------------
# Bold change: replace the voltage-lift annealing with a generic "cover insertion"
# search in C, starting from the arc-extended projective plane graph.
#
# Insertion rule. A new vertex v on side s with neighbour set N (all on the other
# side, each with spare degree) keeps diameter <= D iff every existing vertex x has
# dist(N, x) <= D-1. Adding vertices never increases distances between old
# vertices, so this check is exact. The C engine finds N greedily as a set cover
# by radius-(D-1) balls, then runs a plateau walk: occasionally delete a random
# added vertex, try a few insertions, and keep the result only if the graph stays
# valid and does not shrink. The best valid graph is returned.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef struct { int *alive, *side, *deg, *adj; int count; } State;

static int d, D, R, n0, cap, W, count;
static int *alive, *side, *deg, *adj;
static uint64_t *ball, *scr, *B1, *abits, *unc;
static int *chosen, *Nb;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int pc64(uint64_t x) {
#ifdef __GNUC__
    return __builtin_popcountll(x);
#else
    int c = 0; while (x) { x &= x - 1; c++; } return c;
#endif
}
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static State st_new(void) {
    State s;
    s.alive = malloc(sizeof(int) * cap);
    s.side = malloc(sizeof(int) * cap);
    s.deg = malloc(sizeof(int) * cap);
    s.adj = malloc(sizeof(int) * (size_t)cap * d);
    s.count = 0;
    return s;
}

static void st_save(State *s) {
    memcpy(s->alive, alive, sizeof(int) * cap);
    memcpy(s->side, side, sizeof(int) * cap);
    memcpy(s->deg, deg, sizeof(int) * cap);
    memcpy(s->adj, adj, sizeof(int) * (size_t)cap * d);
    s->count = count;
}

static void st_load(const State *s) {
    memcpy(alive, s->alive, sizeof(int) * cap);
    memcpy(side, s->side, sizeof(int) * cap);
    memcpy(deg, s->deg, sizeof(int) * cap);
    memcpy(adj, s->adj, sizeof(int) * (size_t)cap * d);
    count = s->count;
}

/* out = radius-r balls of all alive vertices (bitsets over slots). */
static void balls(int r, uint64_t *out) {
    uint64_t *cur = out, *nx = scr;
    memset(cur, 0, sizeof(uint64_t) * (size_t)cap * W);
    for (int x = 0; x < cap; x++)
        if (alive[x]) cur[(size_t)x * W + (x >> 6)] |= 1ULL << (x & 63);
    for (int l = 0; l < r; l++) {
        for (int x = 0; x < cap; x++) {
            uint64_t *dst = nx + (size_t)x * W;
            if (!alive[x]) { memset(dst, 0, sizeof(uint64_t) * W); continue; }
            memcpy(dst, cur + (size_t)x * W, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[x]; k++) {
                const uint64_t *src = cur + (size_t)adj[x * d + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nx; nx = t;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)cap * W);
}

static void make_abits(void) {
    memset(abits, 0, sizeof(uint64_t) * W);
    for (int x = 0; x < cap; x++)
        if (alive[x]) abits[x >> 6] |= 1ULL << (x & 63);
}

/* Full check: every pair of alive vertices within distance D. */
static int valid_full(void) {
    balls(D, B1);
    make_abits();
    for (int x = 0; x < cap; x++) {
        if (!alive[x]) continue;
        const uint64_t *b = B1 + (size_t)x * W;
        for (int w = 0; w < W; w++)
            if ((b[w] & abits[w]) != abits[w]) return 0;
    }
    return 1;
}

static void remove_vertex(int v) {
    for (int k = 0; k < deg[v]; k++) {
        int u = adj[v * d + k];
        for (int j = 0; j < deg[u]; j++) {
            if (adj[u * d + j] == v) {
                adj[u * d + j] = adj[u * d + deg[u] - 1];
                deg[u]--;
                break;
            }
        }
    }
    deg[v] = 0;
    alive[v] = 0;
    count--;
}

/* Needs ball[] = radius-R balls of the current graph. */
static int try_insert(void) {
    int s = (int)(rnd() & 1u);
    int slot = -1;
    for (int x = n0; x < cap; x++) if (!alive[x]) { slot = x; break; }
    if (slot < 0) return 0;
    make_abits();
    memcpy(unc, abits, sizeof(uint64_t) * W);
    int nn = 0;
    while (nn < d) {
        int best = -1, bg = 0;
        for (int c = 0; c < cap; c++) {
            if (!alive[c] || side[c] == s || deg[c] >= d || chosen[c]) continue;
            const uint64_t *bc = ball + (size_t)c * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(bc[w] & unc[w]);
            if (g > bg || (g == bg && g > 0 && (rnd() & 3u) == 0)) { bg = g; best = c; }
        }
        if (best < 0) break;
        chosen[best] = 1;
        Nb[nn++] = best;
        const uint64_t *bb = ball + (size_t)best * W;
        int left = 0;
        for (int w = 0; w < W; w++) { unc[w] &= ~bb[w]; left |= (unc[w] != 0); }
        if (!left) break;
    }
    int ok = 1;
    for (int w = 0; w < W; w++) if (unc[w]) ok = 0;
    if (ok) {
        alive[slot] = 1;
        side[slot] = s;
        deg[slot] = 0;
        for (int i = 0; i < nn; i++) {
            int c = Nb[i];
            adj[slot * d + deg[slot]++] = c;
            adj[c * d + deg[c]++] = slot;
        }
        count++;
    }
    for (int i = 0; i < nn; i++) chosen[Nb[i]] = 0;
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || d < 1 || D < 2) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (m + 1));
    int *ev = malloc(sizeof(int) * (m + 1));
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m = i; break; }

    n0 = n;
    R = D - 1;
    cap = n0 + n0 / 2 + 64;
    W = (cap + 63) / 64;
    alive = calloc(cap, sizeof(int));
    side = malloc(sizeof(int) * cap);
    deg = calloc(cap, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)cap * d);
    for (int x = 0; x < cap; x++) side[x] = -1;
    for (int x = 0; x < n0; x++) alive[x] = 1;

    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) continue;
        if (deg[u] >= d || deg[v] >= d) { printf("0 0\n"); return 0; }
        adj[u * d + deg[u]++] = v;
        adj[v * d + deg[v]++] = u;
    }

    /* 2-colour the start graph (it is bipartite). */
    int *stk = malloc(sizeof(int) * (n0 + 1));
    for (int s0 = 0; s0 < n0; s0++) {
        if (side[s0] >= 0) continue;
        side[s0] = 0;
        int sp = 0;
        stk[sp++] = s0;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * d + k];
                if (side[v] < 0) { side[v] = 1 - side[u]; stk[sp++] = v; }
            }
        }
    }

    count = n0;
    ball = malloc(sizeof(uint64_t) * (size_t)cap * W);
    scr = malloc(sizeof(uint64_t) * (size_t)cap * W);
    B1 = malloc(sizeof(uint64_t) * (size_t)cap * W);
    abits = malloc(sizeof(uint64_t) * W);
    unc = malloc(sizeof(uint64_t) * W);
    chosen = calloc(cap, sizeof(int));
    Nb = malloc(sizeof(int) * (d + 1));

    State best = st_new(), snap = st_new();
    st_save(&best);
    int bestc = count;

    while (now() < tl) {
        st_save(&snap);
        int prev = count;
        if (count > n0 && urand() < 0.15) {
            for (int t = 0; t < 200; t++) {
                int x = n0 + (int)(rnd() % (uint64_t)(cap - n0));
                if (alive[x]) { remove_vertex(x); break; }
            }
        }
        for (int a = 0; a < 3; a++) {
            balls(R, ball);
            try_insert();
        }
        if (valid_full() && (count >= prev || urand() < 0.03)) {
            if (count > bestc) { bestc = count; st_save(&best); }
        } else {
            st_load(&snap);
        }
    }

    int *map = malloc(sizeof(int) * cap);
    int c = 0;
    for (int x = 0; x < cap; x++) map[x] = best.alive[x] ? c++ : -1;
    long long me = 0;
    for (int x = 0; x < cap; x++) if (best.alive[x]) me += best.deg[x];
    me /= 2;
    printf("%d %lld\n", c, me);
    for (int x = 0; x < cap; x++) {
        if (!best.alive[x]) continue;
        for (int k = 0; k < best.deg[x]; k++) {
            int y = best.adj[x * d + k];
            if (x < y) printf("%d %d\n", map[x], map[y]);
        }
    }
    return 0;
}
"""


def _pg_start(d):
    """PG(2,q) incidence graph with q the largest prime power <= d-1 (degree q+1 <= d)."""
    q = max(p for p in range(2, d) if lib.is_prime_power(p))
    n2, edges = lib.projective_plane_incidence(q)
    return n2, edges, q


def _arc_start(d):
    """PG(2,q) plus conic-type arcs on both sides (valid when spare degree s = d-q-1 >= 2)."""
    n, edges, q = _pg_start(d)
    s = d - q - 1
    if s < 2:
        return n, edges
    m = n // 2
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v)
        lp[v - m].append(u)
    out = list(edges)
    nn = n
    for p in S:  # new vertex on the point side, joined to the lines through p
        for L in pl[p]:
            out.append((nn, L))
        nn += 1
    for j in S:  # new vertex on the line side, joined to the points on line j
        for P in lp[j]:
            out.append((P, nn))
        nn += 1
    return nn, out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    start = best
    if D >= 3 and d >= 3:
        for make in (_arc_start, lambda dd: _pg_start(dd)[:2]):
            try:
                g = make(d)
            except Exception:
                continue
            if lib.is_valid(g[0], g[1], d, D):
                start = g
                consider(g)
                break

    elapsed = time.monotonic() - t0
    budget = 0.75 * time_limit - elapsed
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=start, timeout=0.9 * time_limit - elapsed)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
