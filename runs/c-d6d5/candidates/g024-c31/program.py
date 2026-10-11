import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: direct simulated annealing on bipartite graphs with
# max degree DEG, no group structure. Vertex 2i is an A-vertex and 2i+1 is a
# B-vertex. Edges only join A and B, so the graph is bipartite by construction.
#
# Cost = number of ordered vertex pairs at distance > DIAM (bitset BFS).
# Moves: ADD an edge between two deficit vertices, SWITCH two edges (degree
# preserving), and MOVE one endpoint of an edge to a deficit vertex on the
# same side. Every move keeps degrees <= DEG and the graph simple.
#
# Growth: when cost reaches 0 the graph is valid; it is recorded and extra
# vertex pairs are added, then the annealer repairs the new vertices.
# The best recorded graph is returned. Python keeps the baseline fallbacks
# (PG(2,q), W(q), cycle, K_{d,d}) and validates everything with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define RUNLEN 30000
#define TEMP0 20.0
#define TEMP1 0.3
#define CAPMAX 4000

static uint64_t rs[2];
static struct timespec TS0;

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
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static int DEG, DIAM, H, nv, nvmax, CAP, MAXW, W;
static long long MOORE;
static double DEADLINE;
static int *adj, *deg, *snapadj, *snapdeg;
static uint64_t *B1, *B2;
static int best_n, best_m;
static int *best_e = NULL;
static int logt[8], loga[8], logb[8], nlog;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Returns the number of ordered pairs (v,w) with dist(v,w) > DIAM. */
static long long eval_bad(void) {
    int n = nv;
    W = (n + 63) >> 6;
    uint64_t *cur = B1, *nxt = B2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            const int *av = adj + (size_t)v * DEG;
            for (int e = 0; e < deg[v]; e++) {
                const uint64_t *t = cur + (size_t)av[e] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
            if (!changed)
                for (int w = 0; w < W; w++)
                    if (o[w] != s[w]) { changed = 1; break; }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int pop = 0;
        for (int w = 0; w < W; w++) pop += pc64(s[w]);
        bad += n - pop;
    }
    return bad;
}

static int has_edge(int x, int y) {
    const int *ax = adj + (size_t)x * DEG;
    for (int i = 0; i < deg[x]; i++)
        if (ax[i] == y) return 1;
    return 0;
}

static void remove_from(int x, int y) {
    int *ax = adj + (size_t)x * DEG;
    for (int i = 0; i < deg[x]; i++) {
        if (ax[i] == y) {
            ax[i] = ax[deg[x] - 1];
            deg[x]--;
            return;
        }
    }
}

static void raw_add(int a, int b) {
    adj[(size_t)a * DEG + deg[a]++] = b;
    adj[(size_t)b * DEG + deg[b]++] = a;
}

static void raw_del(int a, int b) {
    remove_from(a, b);
    remove_from(b, a);
}

static void add_e(int a, int b) {
    raw_add(a, b);
    logt[nlog] = 1; loga[nlog] = a; logb[nlog] = b; nlog++;
}

static void del_e(int a, int b) {
    raw_del(a, b);
    logt[nlog] = 0; loga[nlog] = a; logb[nlog] = b; nlog++;
}

static void undo(void) {
    for (int i = nlog - 1; i >= 0; i--) {
        if (logt[i]) raw_del(loga[i], logb[i]);
        else raw_add(loga[i], logb[i]);
    }
    nlog = 0;
}

static int rand_v(int parity) { return 2 * rnd_int(H) + parity; }

/* Random vertex of the given parity (0 = A, 1 = B) with spare degree, or -1. */
static int pick_def(int parity) {
    for (int t = 0; t < 40; t++) {
        int v = rand_v(parity);
        if (deg[v] < DEG) return v;
    }
    return -1;
}

static int mv_add(void) {
    int a = rand_v(0), b = rand_v(1);
    if (deg[a] >= DEG || deg[b] >= DEG || has_edge(a, b)) return 0;
    add_e(a, b);
    return 1;
}

static int mv_switch(void) {
    int a1 = rand_v(0);
    if (!deg[a1]) return 0;
    int b1 = adj[(size_t)a1 * DEG + rnd_int(deg[a1])];
    int a2 = rand_v(0);
    if (!deg[a2]) return 0;
    int b2 = adj[(size_t)a2 * DEG + rnd_int(deg[a2])];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    del_e(a1, b1); del_e(a2, b2);
    add_e(a1, b2); add_e(a2, b1);
    return 1;
}

/* Move the B endpoint of edge (a1,b1) to a deficit B-vertex. */
static int mv_moveB(void) {
    int a1 = rand_v(0);
    if (!deg[a1]) return 0;
    int b1 = adj[(size_t)a1 * DEG + rnd_int(deg[a1])];
    int b2 = pick_def(1);
    if (b2 < 0 || b2 == b1 || has_edge(a1, b2)) return 0;
    del_e(a1, b1);
    add_e(a1, b2);
    return 1;
}

/* Move the A endpoint of edge (a1,b1) to a deficit A-vertex. */
static int mv_moveA(void) {
    int b1 = rand_v(1);
    if (!deg[b1]) return 0;
    int a1 = adj[(size_t)b1 * DEG + rnd_int(deg[b1])];
    int a2 = pick_def(0);
    if (a2 < 0 || a2 == a1 || has_edge(a2, b1)) return 0;
    del_e(a1, b1);
    add_e(a2, b1);
    return 1;
}

/* Record the current valid graph if it beats the best so far. */
static void record(void) {
    if (nv <= best_n) return;
    int m = 0;
    for (int v = 0; v < nv; v++)
        for (int e = 0; e < deg[v]; e++)
            if (adj[(size_t)v * DEG + e] > v) m++;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int v = 0; v < nv; v++)
        for (int e = 0; e < deg[v]; e++) {
            int u = adj[(size_t)v * DEG + e];
            if (u > v) {
                best_e[idx++] = v;
                best_e[idx++] = u;
            }
        }
    best_m = m;
    best_n = nv;
}

static void snapshot(void) {
    memcpy(snapadj, adj, sizeof(int) * (size_t)nv * DEG);
    memcpy(snapdeg, deg, sizeof(int) * (size_t)nv);
}

static void restore(void) {
    memcpy(adj, snapadj, sizeof(int) * (size_t)nv * DEG);
    memcpy(deg, snapdeg, sizeof(int) * (size_t)nv);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    long long mo = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        mo += p;
        p *= (DEG - 1);
        if (mo > 1000000) break;
    }
    MOORE = 2 * mo;
    int limit = MOORE < CAPMAX ? (int)MOORE : CAPMAX;
    nvmax = 2 * (limit / 2);
    if (nvmax < 4) {
        printf("0 0\n");
        return 0;
    }
    CAP = nvmax + 2;
    MAXW = (CAP + 63) >> 6;
    adj = calloc((size_t)CAP * DEG, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    snapadj = calloc((size_t)CAP * DEG, sizeof(int));
    snapdeg = calloc((size_t)CAP, sizeof(int));
    B1 = calloc((size_t)CAP * MAXW, sizeof(uint64_t));
    B2 = calloc((size_t)CAP * MAXW, sizeof(uint64_t));

    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    H = (start_n / 2) * 3 / 4;
    if (H < DEG + 1) H = DEG + 1;
    if (2 * H > nvmax) H = nvmax / 2;
    nv = 2 * H;
    nlog = 0;
    long long cost = eval_bad();
    int step = 1 + H / 60;
    int done = 0;

    while (!done && elapsed() < DEADLINE) {
        long long runbest = cost;
        snapshot();
        for (int it = 0; it < RUNLEN; it++) {
            if ((it & 31) == 0 && elapsed() > DEADLINE) {
                done = 1;
                break;
            }
            double T = TEMP0 * pow(TEMP1 / TEMP0, (double)it / RUNLEN);
            nlog = 0;
            double r = rnd_unit();
            int ok;
            if (r < 0.3) ok = mv_add();
            else if (r < 0.6) ok = mv_switch();
            else if (r < 0.8) ok = mv_moveA();
            else ok = mv_moveB();
            if (!ok) {
                nlog = 0;
                continue;
            }
            long long c2 = eval_bad();
            long long delta = c2 - cost;
            if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
                cost = c2;
                nlog = 0;
                if (cost < runbest) {
                    runbest = cost;
                    snapshot();
                }
            } else {
                undo();
            }
            if (cost == 0) {
                record();
                if (nv + 2 * step > nvmax) step = (nvmax - nv) / 2;
                if (step < 1) {
                    done = 1;
                    break;
                }
                nv += 2 * step;
                H += step;
                cost = eval_bad();
                runbest = cost;
                snapshot();
            }
        }
        if (!done && cost > runbest) {
            restore();
            cost = runbest;
        }
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baseline families (validated fallbacks).
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


def _cycle(D):
    """Cycle C_{2D}: 2-regular, bipartite, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


# ----------------------------------------------------------------------------
# Driver: baselines, then the bitset annealer, with every result validated.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        consider(*_cycle(D))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if d >= 3 and D >= 3 and remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
