import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: unstructured search with vertex-insertion growth.
#
# The state is a simple d-regular bipartite graph (sides 0 and 1). Moves are
# double edge swaps, which keep regularity and bipartiteness. The cost is the
# number of ordered vertex pairs at distance > DIAM, computed with bitset
# BFS. Simulated annealing drives the cost to zero. When it reaches zero, the
# graph is saved and grown by two vertices: a new A-vertex x and a new B-vertex
# y take a matching of d edges (a_i, b_i), with x joined to every b_i and y to
# every a_i. Degrees are unchanged and the new vertices have degree d. After
# repeated failures at one size, the search restarts from the best valid graph.
#
# Input (stdin): optional d-regular bipartite graph in "n m" format. If it is
# absent or invalid, the search starts from K_{d,d}.
# Output: the largest valid graph found, in "n m" format.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXDEG 16
#define CHUNK 5000
#define MAXFAIL 6
#define TH 2.0
#define TL 0.15

static int DEG, DIAM, N;
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestN = 0;
static int badj[MAXN][MAXDEG];
static int bside[MAXN];
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

typedef struct { int a, i, a2, j, b, b2; } Move;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static inline int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_slot(int v, int u) {
    for (int i = 0; i < DEG; i++)
        if (adj[v][i] == u) return i;
    return -1;
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIAM. */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], sizeof(uint64_t) * (size_t)W);
            for (int e = 0; e < DEG; e++) {
                const uint64_t *s = cur[adj[v][e]];
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return bad;
}

static int pick_side(int s) {
    int v;
    do { v = rnd_int(N); } while (side[v] != s);
    return v;
}

/* Double edge swap: (a,b),(a2,b2) -> (a,b2),(a2,b). a, a2 on side 0. */
static int propose(Move *m) {
    int a = pick_side(0), a2 = pick_side(0);
    if (a == a2) return 0;
    m->a = a;
    m->a2 = a2;
    m->i = rnd_int(DEG);
    m->j = rnd_int(DEG);
    m->b = adj[a][m->i];
    m->b2 = adj[a2][m->j];
    if (m->b == m->b2) return 0;
    if (find_slot(a, m->b2) >= 0 || find_slot(a2, m->b) >= 0) return 0;
    return 1;
}

static void apply_move(const Move *m) {
    adj[m->a][m->i] = m->b2;
    adj[m->a2][m->j] = m->b;
    int k = find_slot(m->b, m->a);
    adj[m->b][k] = m->a2;
    int l = find_slot(m->b2, m->a2);
    adj[m->b2][l] = m->a;
}

static void undo_move(const Move *m) {
    adj[m->a][m->i] = m->b;
    adj[m->a2][m->j] = m->b2;
    int k = find_slot(m->b, m->a2);
    adj[m->b][k] = m->a;
    int l = find_slot(m->b2, m->a);
    adj[m->b2][l] = m->a2;
}

/* Add two vertices x (side 0) and y (side 1) by subdividing a matching of DEG edges. */
static int grow(void) {
    static int mark[MAXN];
    static int stamp = 0;
    if (N + 2 > MAXN) return 0;
    stamp++;
    int ea[MAXDEG], eb[MAXDEG], ne = 0;
    for (int tries = 0; tries < 20000 && ne < DEG; tries++) {
        int a = pick_side(0);
        int b = adj[a][rnd_int(DEG)];
        if (mark[a] == stamp || mark[b] == stamp) continue;
        mark[a] = stamp;
        mark[b] = stamp;
        ea[ne] = a;
        eb[ne] = b;
        ne++;
    }
    if (ne < DEG) return 0;
    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    for (int t = 0; t < DEG; t++) {
        int a = ea[t], b = eb[t];
        int sa = find_slot(a, b);
        adj[a][sa] = y;
        int sb = find_slot(b, a);
        adj[b][sb] = x;
        adj[x][t] = b;
        adj[y][t] = a;
    }
    N += 2;
    return 1;
}

static void save_best(void) {
    bestN = N;
    memcpy(badj, adj, sizeof(adj));
    memcpy(bside, side, sizeof(side));
}

static void restore_best(void) {
    N = bestN;
    memcpy(adj, badj, sizeof(adj));
    memcpy(side, bside, sizeof(side));
}

/* Read an optional start graph from stdin; it must be d-regular and bipartite. */
static int load_start(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > MAXN || m0 < 0) return 0;
    static int dg[MAXN];
    static int q[MAXN];
    memset(dg, 0, sizeof(int) * (size_t)n0);
    int ok = 1;
    for (int e = 0; e < m0; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; continue; }
        if (dg[u] >= DEG || dg[v] >= DEG) { ok = 0; continue; }
        int dup = 0;
        for (int i = 0; i < dg[u]; i++)
            if (adj[u][i] == v) { dup = 1; break; }
        if (dup) { ok = 0; continue; }
        adj[u][dg[u]++] = v;
        adj[v][dg[v]++] = u;
    }
    if (!ok) return 0;
    for (int v = 0; v < n0; v++)
        if (dg[v] != DEG) return 0;
    for (int v = 0; v < n0; v++) side[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int i = 0; i < DEG; i++) {
                int y = adj[x][i];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    q[tail++] = y;
                } else if (side[y] == side[x]) {
                    return 0;
                }
            }
        }
    }
    N = n0;
    return 1;
}

static void output_best(void) {
    if (bestN <= 0) {
        printf("0 0\n");
        return;
    }
    long long m = 0;
    for (int v = 0; v < bestN; v++)
        if (bside[v] == 0) m += DEG;
    printf("%d %lld\n", bestN, m);
    for (int v = 0; v < bestN; v++) {
        if (bside[v] != 0) continue;
        for (int e = 0; e < DEG; e++)
            printf("%d %d\n", v, badj[v][e]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 977ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!load_start()) {
        N = 2 * DEG;
        for (int a = 0; a < DEG; a++) {
            side[a] = 0;
            side[DEG + a] = 1;
            for (int j = 0; j < DEG; j++) {
                adj[a][j] = DEG + j;
                adj[DEG + a][j] = j;
            }
        }
    }

    long long cur = eval_cost();
    if (cur == 0) save_best();
    int fails = 0;
    Move mv;
    while (elapsed() < DEADLINE) {
        if (cur == 0) {
            save_best();
            if (!grow()) break;
            cur = eval_cost();
            fails = 0;
            continue;
        }
        for (int it = 0; it < CHUNK && cur > 0; it++) {
            if ((it & 127) == 0 && elapsed() > DEADLINE) break;
            double p = (double)it / CHUNK;
            double T = TH * (1.0 - p) + TL * p;
            if (!propose(&mv)) continue;
            apply_move(&mv);
            long long nc = eval_cost();
            long long dl = nc - cur;
            if (dl <= 0 || rnd_unit() < exp(-(double)dl / T)) {
                cur = nc;
            } else {
                undo_move(&mv);
            }
        }
        if (cur > 0) {
            fails++;
            if (fails >= MAXFAIL && bestN > 0) {
                restore_best();
                cur = 0;
                fails = 0;
            }
        }
    }
    if (cur == 0) save_best();
    output_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions used as fallbacks and as starting graphs for the C search.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: Python baselines, then the C search that grows a regular bipartite graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # The C search starts from the best baseline (used only if d-regular and bipartite)
    # and grows it. Keep a margin for process start, parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if 2 <= d <= 16 and D >= 2 and remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
