"""Degree-diameter search for bipartite graphs.

New idea in this version: ejection-chain simulated annealing for vertex insertion.
Starting from the best known construction, the program adds one vertex at a time
with no edges. It then anneals on the number of vertex pairs at distance greater
than D. Two move types keep every degree at most d and the graph bipartite:
  * ejection: attach a deficient vertex x to a vertex y on the other side. If y is
    saturated, first remove one of y's edges (y, z), which leaves z deficient.
  * 2-switch: replace (a,b), (c,e) with (a,e), (c,b) on the same side pattern.
When a size is reached with zero bad pairs, the graph is saved and one more vertex
is added. A failed attempt restores the last valid graph and retries.
"""
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXDEG 64
#define MAXE 40000
#define ATTEMPT_ITERS 20000

static int N, DEG, DIAM, W;
static int side[MAXN], deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char mat[MAXN][MAXN];
static uint64_t Ra[MAXN * MAXW], Rb[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double budget;
static clock_t t0;

static int SN, SM;
static int SA[MAXE], SB[MAXE];
static int EA[MAXE], EB[MAXE];
static int qb[MAXN];

typedef struct { int t, a, b; } Op;
static Op lg[16];
static int nlg;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM (0 iff valid). */
static long long cost(void) {
    uint64_t *cur = Ra, *nxt = Rb;
    int v, k, w, t;
    long long bad = 0;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (t = 0; t < DIAM; t++) {
        for (v = 0; v < N; v++) {
            uint64_t *r = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            for (w = 0; w < W; w++) r[w] = s[w];
            for (k = 0; k < deg[v]; k++) {
                const uint64_t *q = cur + (size_t)adj[v][k] * W;
                for (w = 0; w < W; w++) r[w] |= q[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    for (v = 0; v < N; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        bad += N - c;
    }
    return bad / 2;
}

static void add_e(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    mat[a][b] = mat[b][a] = 1;
}
static void del_from(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; return; }
}
static void del_e(int a, int b) {
    del_from(a, b);
    del_from(b, a);
    mat[a][b] = mat[b][a] = 0;
}
static void OP_add(int a, int b) {
    add_e(a, b);
    lg[nlg].t = 1; lg[nlg].a = a; lg[nlg].b = b; nlg++;
}
static void OP_del(int a, int b) {
    del_e(a, b);
    lg[nlg].t = 0; lg[nlg].a = a; lg[nlg].b = b; nlg++;
}
static void undo(void) {
    while (nlg > 0) {
        Op o = lg[--nlg];
        if (o.t) del_e(o.a, o.b); else add_e(o.a, o.b);
    }
}

/* Ejection: attach a deficient x to an opposite-side y, removing one edge of y if needed. */
static int move_eject(void) {
    int x, y, z, t = 0;
    do { x = rndint(N); t++; } while (deg[x] >= DEG && t < 300);
    if (deg[x] >= DEG) return 0;
    t = 0;
    do { y = rndint(N); t++; } while ((side[y] == side[x] || mat[x][y]) && t < 300);
    if (side[y] == side[x] || mat[x][y]) return 0;
    if (deg[y] >= DEG) {
        z = adj[y][rndint(deg[y])];
        OP_del(y, z);
    }
    OP_add(x, y);
    return 1;
}

/* 2-switch: (a,b),(c,e) -> (a,e),(c,b); keeps all degrees and bipartiteness. */
static int move_switch(void) {
    int a, b, c, dd, t = 0;
    a = rndint(N);
    if (deg[a] == 0) return 0;
    b = adj[a][rndint(deg[a])];
    do { c = rndint(N); t++; } while ((side[c] != side[a] || c == a || deg[c] == 0) && t < 300);
    if (side[c] != side[a] || c == a || deg[c] == 0) return 0;
    dd = adj[c][rndint(deg[c])];
    if (mat[a][dd] || mat[c][b]) return 0;
    OP_del(a, b);
    OP_del(c, dd);
    OP_add(a, dd);
    OP_add(c, b);
    return 1;
}

static void snapshot(void) {
    int v, k;
    SM = 0;
    SN = N;
    for (v = 0; v < N; v++)
        for (k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) { SA[SM] = v; SB[SM] = adj[v][k]; SM++; }
}

static void restore(void) {
    int i;
    memset(mat, 0, sizeof mat);
    memset(deg, 0, sizeof deg);
    N = SN;
    W = (N + 63) >> 6;
    for (i = 0; i < SM; i++) add_e(SA[i], SB[i]);
    nlg = 0;
}

static int add_vertex(void) {
    if (N >= MAXN - 1) return 0;
    side[N] = rndint(2);
    deg[N] = 0;
    N++;
    W = (N + 63) >> 6;
    return 1;
}

/* Anneal at the current size. Returns 1 when a zero-cost graph is reached. */
static int attempt(void) {
    long long cur = cost(), nc, delta;
    int it, moved;
    double T;
    if (cur == 0) return 1;
    for (it = 0; it < ATTEMPT_ITERS; it++) {
        if ((it & 127) == 0 && elapsed() > budget) return 0;
        nlg = 0;
        moved = (rnd01() < 0.5) ? move_eject() : move_switch();
        if (!moved) continue;
        nc = cost();
        delta = nc - cur;
        T = 0.6 * (1.0 - (double)it / ATTEMPT_ITERS) + 0.03;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            nlg = 0;
            if (cur == 0) return 1;
        } else {
            undo();
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    int n, m, i, v, have_best = 0;
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = 88172645463325252ULL ^ ((uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL);
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    t0 = clock();

    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 0 || n > MAXN - 2 || m < 0 || m > MAXE || DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &EA[i], &EB[i]) != 2) { printf("0 0\n"); return 0; }
    }

    N = n;
    W = (N + 63) >> 6;
    memset(deg, 0, sizeof deg);
    memset(mat, 0, sizeof mat);
    for (i = 0; i < m; i++) {
        int a = EA[i], b = EB[i];
        if (a < 0 || a >= N || b < 0 || b >= N || a == b || mat[a][b] || deg[a] >= DEG || deg[b] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_e(a, b);
    }

    /* 2-colour the start graph; reject if it is not bipartite. */
    for (v = 0; v < N; v++) side[v] = -1;
    for (v = 0; v < N; v++) {
        int head = 0, tail = 0, k;
        if (side[v] >= 0) continue;
        side[v] = 0;
        qb[tail++] = v;
        while (head < tail) {
            int x = qb[head++];
            for (k = 0; k < deg[x]; k++) {
                int u = adj[x][k];
                if (side[u] < 0) { side[u] = 1 - side[x]; qb[tail++] = u; }
                else if (side[u] == side[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    nlg = 0;
    while (elapsed() < budget) {
        if (attempt()) {
            snapshot();
            have_best = 1;
            if (!add_vertex()) break;
        } else if (have_best) {
            if (elapsed() >= budget) break;
            restore();
            if (!add_vertex()) break;
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", SN, SM);
    for (i = 0; i < SM; i++) printf("%d %d\n", SA[i], SB[i]);
    return 0;
}
"""


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _best_valid(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2

    base = _pg_base(d) if d >= 3 else None
    if base is not None:
        if D == 3 and lib.is_prime_power(d - 1):
            return _best_valid([base], d, D)  # Moore-extremal
        cands.append(base)

    # Araujo-Pardo & Lopez record graph for d = q+2 with q a prime power (D = 3).
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    start = _best_valid(cands, d, D)

    # Insertion-and-anneal search in C, using the remaining time.
    timeout = max(1.0, min(time_limit * 0.92 - 1.0, 0.8 * time_limit + 4.0))
    budget = max(0.5, timeout - 3.0)
    elapsed_py = time.monotonic() - t_start
    if elapsed_py + timeout < time_limit:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=start, timeout=timeout)
            n, e = lib.parse_graph_text(out)
            cands.append((n, e))
        except Exception:
            pass

    return _best_valid(cands + [start], d, D)
