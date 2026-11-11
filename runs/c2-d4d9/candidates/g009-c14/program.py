"""Program: grow-and-repair search on d-regular bipartite graphs (non-lift construction).

Construction:
  1. Python builds a cheap valid start: the largest random Haar graph over Z_m it can find
     quickly (A_i ~ B_{i+s} for s in S, |S| = d). Haar graphs are d-regular and bipartite,
     and their diameter follows from two BFS runs by translation symmetry. For D = 3 with
     a known record, that graph is used as the baseline and returned directly if it reaches
     the Moore bound.
  2. C engine (grow_c): keeps a d-regular bipartite graph and inserts vertex pairs. Inserting
     a pair (a, b) removes d matched edges (x_k, y_k) and adds x_k-b and a-y_k, so every
     degree stays d. The diameter is then repaired by simulated annealing over double-edge
     switches (x1,y1),(x2,y2) -> (x1,y2),(x2,y1). The cost is the number of vertex pairs at
     distance > D, computed by bitset BFS. The batch size doubles after each success and
     halves after each failure. The last valid graph is kept as a snapshot.
  3. Python validates the output with lib.is_valid and keeps the largest valid graph.
     The fallbacks are the Haar start, the known start, or K_{d,d}.
"""
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 6144
#define MAXD 8
#define MAXW (MAXV / 64)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* current graph */
static int n;
static int side[MAXV];
static int nb[MAXV][MAXD];
/* snapshot of last valid graph */
static int snb[MAXV][MAXD];
static int sside[MAXV];
static int sn;

static uint64_t bufA[MAXV][MAXW], bufB[MAXV][MAXW];
static int usedA[MAXV], usedB[MAXV];
static int stk = 0;

/* number of unordered pairs at distance > D (0 = valid) */
static long eval_bad(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cu)[MAXW] = bufA;
    uint64_t (*nx)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        memset(cu[v], 0, sizeof(uint64_t) * (size_t)W);
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx[v];
            const uint64_t *s0 = cu[v];
            for (int w = 0; w < W; w++) o[w] = s0[w];
            for (int k = 0; k < d; k++) {
                const uint64_t *s = cu[nb[v][k]];
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t (*t)[MAXW] = cu;
        cu = nx;
        nx = t;
    }
    long un = 0;
    for (int v = 0; v < n; v++) {
        long pc = 0;
        for (int w = 0; w < W; w++) pc += pop64(cu[v][w]);
        un += (long)n - pc;
    }
    return un / 2;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < d; k++)
        if (nb[u][k] == v) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int k = 0; k < d; k++)
        if (nb[v][k] == old) { nb[v][k] = nw; return; }
}

static int pick_side(int s) {
    for (;;) {
        int v = rndint(n);
        if (side[v] == s) return v;
    }
}

static void init_k(void) {
    n = 2 * d;
    for (int i = 0; i < d; i++) { side[i] = 0; side[d + i] = 1; }
    for (int i = 0; i < d; i++)
        for (int k = 0; k < d; k++) {
            nb[i][k] = d + k;
            nb[d + k][i] = i;
        }
}

/* Reads "n m" and m edges; accepts only d-regular simple bipartite graphs. */
static int load_stdin(void) {
    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2) return 0;
    if (nn < 4 || nn > MAXV - 2 || (nn & 1) || mm < 0 || mm > MAXV * MAXD / 2) return 0;
    static int eu[MAXV * MAXD / 2], ev[MAXV * MAXD / 2];
    static int deg[MAXV], fill[MAXV], col[MAXV], qu[MAXV];
    memset(deg, 0, sizeof(int) * (size_t)nn);
    for (int i = 0; i < mm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= nn || v >= nn || u == v) return 0;
        eu[i] = u;
        ev[i] = v;
        deg[u]++;
        deg[v]++;
    }
    for (int v = 0; v < nn; v++)
        if (deg[v] != d) return 0;
    memset(fill, 0, sizeof(int) * (size_t)nn);
    for (int i = 0; i < mm; i++) {
        int u = eu[i], v = ev[i];
        nb[u][fill[u]++] = v;
        nb[v][fill[v]++] = u;
    }
    for (int v = 0; v < nn; v++)
        for (int k1 = 0; k1 < d; k1++)
            for (int k2 = k1 + 1; k2 < d; k2++)
                if (nb[v][k1] == nb[v][k2]) return 0;
    for (int v = 0; v < nn; v++) col[v] = -1;
    int head = 0, tail = 0;
    for (int s = 0; s < nn; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        qu[tail++] = s;
        while (head < tail) {
            int x = qu[head++];
            for (int k = 0; k < d; k++) {
                int y = nb[x][k];
                if (col[y] == -1) {
                    col[y] = 1 - col[x];
                    qu[tail++] = y;
                } else if (col[y] == col[x]) {
                    return 0;
                }
            }
        }
    }
    n = nn;
    for (int v = 0; v < n; v++) side[v] = col[v];
    return 1;
}

/* Insert a new A-vertex a and B-vertex b, keeping the graph d-regular. */
static int insert_pair(void) {
    if (n + 2 > MAXV) return 0;
    stk++;
    int xs[MAXD], ys[MAXD], cnt = 0;
    long att = 0;
    while (cnt < d && att < 20000) {
        att++;
        int x = pick_side(0);
        int y = nb[x][rndint(d)];
        if (usedA[x] == stk || usedB[y] == stk) continue;
        usedA[x] = stk;
        usedB[y] = stk;
        xs[cnt] = x;
        ys[cnt] = y;
        cnt++;
    }
    if (cnt < d) return 0;
    int a = n, b = n + 1;
    side[a] = 0;
    side[b] = 1;
    for (int k = 0; k < d; k++) {
        int x = xs[k], y = ys[k];
        repl(x, y, b);
        repl(y, x, a);
        nb[a][k] = y;
        nb[b][k] = x;
    }
    n += 2;
    return 1;
}

static void save_snap(void) {
    sn = n;
    memcpy(snb, nb, sizeof(int) * MAXD * (size_t)n);
    memcpy(sside, side, sizeof(int) * (size_t)n);
}

static void restore_snap(void) {
    n = sn;
    memcpy(nb, snb, sizeof(int) * MAXD * (size_t)sn);
    memcpy(side, sside, sizeof(int) * (size_t)sn);
}

/* Simulated annealing with double-edge switches; returns 1 if bad reaches 0 before end. */
static int anneal(double end, long *bad_io) {
    long cur = *bad_io;
    double start = now();
    double span = end - start;
    if (span <= 0.0) return 0;
    double temp = 1.0;
    long it = 0;
    for (;;) {
        if ((it++ & 3) == 0) {
            double tm = now();
            if (tm >= end) return 0;
            double fr = (tm - start) / span;
            temp = 1.2 * (1.0 - fr) + 0.05;
        }
        int x1 = pick_side(0), x2 = pick_side(0);
        if (x1 == x2) continue;
        int k1 = rndint(d), k2 = rndint(d);
        int y1 = nb[x1][k1], y2 = nb[x2][k2];
        if (y1 == y2) continue;
        if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
        nb[x1][k1] = y2;
        nb[x2][k2] = y1;
        repl(y1, x1, x2);
        repl(y2, x2, x1);
        long c2 = eval_bad();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur == 0) {
                *bad_io = 0;
                return 1;
            }
        } else {
            nb[x1][k1] = y1;
            nb[x2][k2] = y2;
            repl(y1, x2, x1);
            repl(y2, x1, x2);
        }
    }
}

static void print_snap(void) {
    int cntA = 0;
    for (int v = 0; v < sn; v++)
        if (sside[v] == 0) cntA++;
    printf("%d %d\n", sn, cntA * d);
    for (int v = 0; v < sn; v++) {
        if (sside[v] != 0) continue;
        for (int k = 0; k < d; k++) printf("%d %d\n", v, snb[v][k]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < 0.5 * limit) usable = 0.5 * limit;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    if (!(load_stdin() && eval_bad() == 0)) init_k();
    save_snap();

    int k = 1, stuck = 0;
    double last = 0.3;
    while (now() < t_end) {
        double st = now();
        int ok = 1;
        for (int i = 0; i < k; i++)
            if (!insert_pair()) { ok = 0; break; }
        if (!ok) {
            restore_snap();
            if (k > 1) k /= 2;
            else if (++stuck > 50) break;
            continue;
        }
        long bad = eval_bad();
        double budget = 2.0 * last;
        if (budget < 0.3) budget = 0.3;
        double end = now() + budget;
        if (end > t_end) end = t_end;
        int good = (bad == 0) || anneal(end, &bad);
        double dur = now() - st;
        if (good) {
            save_snap();
            stuck = 0;
            last = dur;
            k *= 2;
            int cap = n / 8 + 1;
            if (k > cap) k = cap;
        } else {
            restore_snap();
            last = dur;
            if (k > 1) k /= 2;
            else ++stuck;
        }
    }
    restore_snap();
    print_snap();
    return 0;
}
'''


def known_start(d, D):
    """Record constructions for D = 3 that Python can build directly, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _haar_ok(m, S, D):
    """Diameter test for the Haar graph H(m, S): translation symmetry means BFS from A_0 and B_0 suffices."""
    nbr = [[m + (i + s) % m for s in S] for i in range(m)]
    nbr += [[(j - s) % m for s in S] for j in range(m)]
    for src in (0, m):
        dist = [-1] * (2 * m)
        dist[src] = 0
        frontier = [src]
        reached = 1
        level = 0
        while frontier and level < D:
            level += 1
            nxt = []
            for v in frontier:
                for u in nbr[v]:
                    if dist[u] < 0:
                        dist[u] = level
                        nxt.append(u)
            reached += len(nxt)
            frontier = nxt
        if reached < 2 * m:
            return False
    return True


def _haar_search(d, D, deadline, rng):
    """Largest Haar graph over Z_m (|S| = d) found quickly, as (n, edges), or None."""
    best = None
    m = d
    fails = 0
    while time.monotonic() < deadline and fails < 30 and m < 3000:
        found = None
        for _ in range(8):
            S = rng.sample(range(m), d)
            if _haar_ok(m, S, D):
                found = S
                break
        if found is not None:
            best = (m, found)
            fails = 0
            m += max(1, m // 20)
        else:
            fails += 1
            m += 1
    if best is None:
        return None
    m, S = best
    return lib.haar_graph(m, S)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = lib.haar_graph(d, range(d))          # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])

    try:
        ks = known_start(d, D)
    except Exception:
        ks = None
    if ks is not None and ks[0] > best[0] and lib.is_valid(ks[0], ks[1], d, D):
        best = ks
    if best[0] >= lib.moore_bound(d, D):
        return best
    if not (2 <= d <= 8 and D >= 2):
        return best

    end = t0 + 0.88 * time_limit - 1.5
    start = None
    try:
        haar = _haar_search(d, D, t0 + 0.15 * time_limit, random.Random(seed))
    except Exception:
        haar = None
    if haar is not None and lib.is_valid(haar[0], haar[1], d, D):
        start = haar
        if haar[0] > best[0]:
            best = haar

    budget = end - time.monotonic()
    if budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 10)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
