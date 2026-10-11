import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with a bad-pair cost.
# Moves are endpoint rewires, degree-preserving swaps, edge additions, and
# edge removals. Once the cost reaches 0 the engine adds a vertex, saturates
# the spare degree, and anneals again. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define WMAX 22
#define DMAX 40
#define LOGMAX 64

static int N, DEG, DIAM;
static int side[NMAX];
static int degc[NMAX];
static int nb[NMAX][DMAX];
static unsigned char A[NMAX][NMAX];
static long ecount = 0;
static uint64_t B1[NMAX][WMAX], B2[NMAX][WMAX];
static uint64_t rs = 1;

static int logging = 0;
static int lg_t[LOGMAX], lg_u[LOGMAX], lg_v[LOGMAX], lg_n = 0;

static int best_n = 0, best_m = 0, have_best = 0;
static int bestU[NMAX * DMAX], bestV[NMAX * DMAX];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int u, int v) {
    nb[u][degc[u]++] = v;
    nb[v][degc[v]++] = u;
    A[u][v] = 1;
    A[v][u] = 1;
    ecount++;
}

static void del_nb(int u, int v) {
    for (int i = 0; i < degc[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][degc[u] - 1];
            degc[u]--;
            return;
        }
    }
}

static void del_e(int u, int v) {
    del_nb(u, v);
    del_nb(v, u);
    A[u][v] = 0;
    A[v][u] = 0;
    ecount--;
}

static void do_add(int u, int v) {
    add_e(u, v);
    if (logging && lg_n < LOGMAX) {
        lg_t[lg_n] = 1; lg_u[lg_n] = u; lg_v[lg_n] = v; lg_n++;
    }
}

static void do_del(int u, int v) {
    del_e(u, v);
    if (logging && lg_n < LOGMAX) {
        lg_t[lg_n] = 0; lg_u[lg_n] = u; lg_v[lg_n] = v; lg_n++;
    }
}

static void undo(void) {
    for (int i = lg_n - 1; i >= 0; i--) {
        if (lg_t[i]) del_e(lg_u[i], lg_v[i]);
        else add_e(lg_u[i], lg_v[i]);
    }
    lg_n = 0;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts as bad). */
static long eval_bad(void) {
    int wn = (N + 63) >> 6;
    uint64_t (*cur)[WMAX] = B1;
    uint64_t (*nxt)[WMAX] = B2;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < wn; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < wn; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < degc[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < wn; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < wn; w++) c += pc64(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int rand_edge(int *ou, int *ov) {
    for (int t = 0; t < 200; t++) {
        int x = rndint(N);
        if (degc[x] == 0) continue;
        *ou = x;
        *ov = nb[x][rndint(degc[x])];
        return 1;
    }
    return 0;
}

/* Replace one endpoint of a random edge by another vertex of the same side with spare degree. */
static int move_rewire(void) {
    int x, y;
    if (!rand_edge(&x, &y)) return 0;
    if (rndint(2)) { int t = x; x = y; y = t; }
    for (int t = 0; t < 40; t++) {
        int z = rndint(N);
        if (z == y || side[z] != side[y] || degc[z] >= DEG || A[x][z]) continue;
        do_del(x, y);
        do_add(x, z);
        return 1;
    }
    return 0;
}

/* Degree-preserving 2-swap across the bipartition. */
static int move_swap(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b)) return 0;
    if (!rand_edge(&c, &e)) return 0;
    if (side[a] != 0) { int t = a; a = b; b = t; }
    if (side[c] != 0) { int t = c; c = e; e = t; }
    if (a == c || b == e) return 0;
    if (A[a][e] || A[c][b]) return 0;
    do_del(a, b);
    do_del(c, e);
    do_add(a, e);
    do_add(c, b);
    return 1;
}

static int move_add(void) {
    for (int t = 0; t < 60; t++) {
        int x = rndint(N), y = rndint(N);
        if (side[x] == side[y] || degc[x] >= DEG || degc[y] >= DEG || A[x][y]) continue;
        do_add(x, y);
        return 1;
    }
    return 0;
}

static int move_remove(void) {
    int x, y;
    if (!rand_edge(&x, &y)) return 0;
    do_del(x, y);
    return 1;
}

/* Append a vertex on the smaller side and join it to DEG opposite vertices. */
static int grow_vertex(void) {
    if (N + 1 >= NMAX) return 0;
    int cnt1 = 0;
    for (int v = 0; v < N; v++) cnt1 += side[v];
    int s = (cnt1 < N - cnt1) ? 1 : 0;
    int v = N;
    N++;
    side[v] = s;
    degc[v] = 0;
    for (int k = 0; k < DEG; k++) {
        int x = -1;
        for (int t = 0; t < 300 && x < 0; t++) {
            int c = rndint(N);
            if (side[c] == s || c == v || A[v][c] || degc[c] >= DEG) continue;
            x = c;
        }
        if (x < 0) {
            for (int t = 0; t < 300 && x < 0; t++) {
                int c = rndint(N);
                if (side[c] == s || c == v || A[v][c] || degc[c] == 0) continue;
                int y = nb[c][rndint(degc[c])];
                del_e(c, y);
                x = c;
            }
        }
        if (x < 0) break;
        add_e(v, x);
    }
    return 1;
}

static void saturate(void) {
    int fails = 0;
    while (fails < 2000) {
        if (move_add()) fails = 0;
        else fails++;
    }
}

static void snapshot(void) {
    best_m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < degc[v]; i++) {
            int u = nb[v][i];
            if (u > v) {
                bestU[best_m] = v;
                bestV[best_m] = u;
                best_m++;
            }
        }
    }
    best_n = N;
    have_best = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    DEG = d;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (DEG < 1 || DEG > DMAX || DIAM < 1 || n0 < 1 || n0 > NMAX - 200 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || A[u][v] || degc[u] >= DEG || degc[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_e(u, v);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < N; v++) side[v] = -1;
    int *queue = (int *)malloc(sizeof(int) * (N + 1));
    int bip = 1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < degc[u]; i++) {
                int w = nb[u][i];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    bip = 0;
                }
            }
        }
    }
    free(queue);
    if (!bip) { printf("0 0\n"); return 0; }

    logging = 0;
    long cur = eval_bad();
    if (cur == 0) snapshot();

    clock_t t0 = clock();
    long it = 0;
    const long EPOCH = 20000;
    const double TMAX = 1.5, TMIN = 0.08;
    while (1) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        it++;
        if (cur == 0) {
            if (N > best_n) snapshot();
            if (!grow_vertex()) break;
            saturate();
            cur = eval_bad();
            continue;
        }
        double frac = (double)(it % EPOCH) / (double)EPOCH;
        double T = TMAX * pow(TMIN / TMAX, frac);
        lg_n = 0;
        logging = 1;
        int r = rndint(100);
        int ok3;
        if (r < 45) ok3 = move_rewire();
        else if (r < 85) ok3 = move_swap();
        else if (r < 93) ok3 = move_add();
        else ok3 = move_remove();
        if (!ok3) {
            logging = 0;
            lg_n = 0;
            continue;
        }
        long nc = eval_bad();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo();
        }
        logging = 0;
        lg_n = 0;
    }

    if (cur == 0 && N > best_n) snapshot();
    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions used as the start graph for the C engine.
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedy set cover of `full` by at most d candidate vertices, or None."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of each other."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover-vertex extension and edge saturation while time remains."""
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Start graphs from structured constructions, grown by cover extension.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, t0 + 0.1 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            end = t0 + 0.2 * time_limit
            for _ in range(10):
                if time.monotonic() >= end:
                    break
                sub = random.Random(rng.randrange(1 << 30))
                n2, e2 = _grow(gq[0], gq[1], d, D, end, sub)
                consider(n2, e2)

    # Annealing in C from the best start graph, using most of the remaining budget.
    if d >= 2 and D >= 2:
        remaining = 0.8 * time_limit - (time.monotonic() - t0)
        if remaining > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                stdin_graph=best, timeout=remaining + 6)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
