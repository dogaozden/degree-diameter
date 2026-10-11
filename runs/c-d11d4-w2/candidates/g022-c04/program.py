import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: cover-based growth plus greedy-cover repair.
#
#   * grow_cover: add a vertex whose neighbourhood is chosen greedily so that
#     its radius-(DIAM-1) balls cover the whole graph (set cover, both sides
#     tried). Falls back to a partial attachment if no full cover exists.
#   * relocate: take the worst vertex (sampled by bad-pair count), detach it,
#     and reattach it to a greedy cover of the rest of the graph. Spare slots
#     are filled with random deficient vertices (extra edges never hurt).
#   * swap: classic degree-preserving double-edge swap.
#
# Cost = number of unordered vertex pairs at distance > DIAM. A state with
# cost 0 is saved as the best valid graph and grown by one vertex. A stall
# restores the best valid graph, grows it, and applies a few random swaps.
# Rejected moves are undone from a snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int badv[MAXN];
static int stk[MAXN];
static int candbuf[MAXN];

static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv = 0;
static int have_valid = 0;

static int snAdj[MAXN][DEGMAX];
static int snDeg[MAXN];
static int snBad[MAXN];
static int snNv = 0;

static uint64_t BUFA[MAXN * WMAX];
static uint64_t BUFB[MAXN * WMAX];

static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void raw_add(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void raw_remove(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

/* Bitset balls of radius r for all vertices; returns a pointer to the result buffer. */
static uint64_t *compute_balls(int r) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = BUFA, *nxt = BUFB, *tmp;
    memset(cur, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    return cur;
}

static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *R = compute_balls(DIAM);
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        const uint64_t *s = R + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        badv[v] = nv - cnt;
        bad += badv[v];
    }
    return bad / 2;
}

/* Greedy set cover of all vertices except ex by balls B of vertices of colour cc
   with deg < DEG. Picks at most k vertices into chosen[]; *covcnt = covered count. */
static int greedy_cover(const uint64_t *B, int cc, int ex, int k, int *chosen,
                        int randomize, int *covcnt) {
    int W = (nv + 63) >> 6;
    uint64_t covered[WMAX];
    memset(covered, 0, sizeof(uint64_t) * (size_t)W);
    if (ex >= 0) covered[ex >> 6] |= 1ULL << (ex & 63);
    int nc = 0;
    while (nc < k) {
        int best = -1, bestg = 0, ties = 0;
        int rpick = -1, rcount = 0;
        for (int x = 0; x < nv; x++) {
            if (col[x] != cc || x == ex || deg[x] >= DEG) continue;
            const uint64_t *bx = B + (size_t)x * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(bx[w] & ~covered[w]);
            if (g == 0) continue;
            rcount++;
            if (rnd(rcount) == 0) rpick = x;
            if (g > bestg) {
                bestg = g;
                best = x;
                ties = 1;
            } else if (g == bestg) {
                ties++;
                if (rnd(ties) == 0) best = x;
            }
        }
        int pick = best;
        if (randomize && rpick >= 0 && rnd(3) == 0) pick = rpick;
        if (pick < 0) break;
        chosen[nc++] = pick;
        const uint64_t *bp = B + (size_t)pick * W;
        for (int w = 0; w < W; w++) covered[w] |= bp[w];
    }
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(covered[w]);
    *covcnt = c;
    return nc;
}

static void grow_cover(void) {
    int order[2];
    order[0] = rnd(2);
    order[1] = 1 - order[0];
    int randomize = (rnd(3) == 0);
    int bestc = -1, bestk = 0, bestcov = -1, bestfull = 0;
    int bestCh[DEGMAX];
    for (int t = 0; t < 2; t++) {
        int cc = order[t];
        int ch[DEGMAX];
        int cov = 0;
        uint64_t *B = compute_balls(DIAM - 1);
        int k = greedy_cover(B, 1 - cc, -1, DEG, ch, randomize, &cov);
        int full = (cov == nv);
        int better = 0;
        if (bestc < 0) better = 1;
        else if (full && !bestfull) better = 1;
        else if (full && bestfull && k < bestk) better = 1;
        else if (!full && !bestfull && cov > bestcov) better = 1;
        if (better) {
            bestc = cc;
            bestk = k;
            bestcov = cov;
            bestfull = full;
            for (int i = 0; i < k; i++) bestCh[i] = ch[i];
        }
    }
    int v = nv++;
    col[v] = bestc;
    deg[v] = 0;
    for (int i = 0; i < bestk; i++) raw_add(v, bestCh[i]);
}

static int swap_move(void) {
    int a = rnd(nv);
    if (deg[a] == 0) return 0;
    int c = -1;
    for (int t = 0; t < 50; t++) {
        int x = rnd(nv);
        if (x != a && col[x] == col[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int b = adjv[a][rnd(deg[a])];
    int e = adjv[c][rnd(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    raw_remove(a, b);
    raw_remove(c, e);
    raw_add(a, e);
    raw_add(c, b);
    return 1;
}

static void relocate_move(void) {
    int v = rnd(nv);
    for (int t = 0; t < 2; t++) {
        int u = rnd(nv);
        if (badv[u] > badv[v]) v = u;
    }
    int c = col[v];
    while (deg[v] > 0) raw_remove(v, adjv[v][deg[v] - 1]);
    int ch[DEGMAX];
    int cov = 0;
    uint64_t *B = compute_balls(DIAM - 1);
    int k = greedy_cover(B, 1 - c, v, DEG, ch, rnd(4) == 0, &cov);
    if (k < DEG) {
        int nc = 0;
        for (int x = 0; x < nv; x++) {
            if (x == v || col[x] == c || deg[x] >= DEG) continue;
            int used = 0;
            for (int i = 0; i < k; i++)
                if (ch[i] == x) {
                    used = 1;
                    break;
                }
            if (!used) candbuf[nc++] = x;
        }
        shuffle_int(candbuf, nc);
        for (int i = 0; i < nc && k < DEG; i++) ch[k++] = candbuf[i];
    }
    for (int i = 0; i < k; i++) raw_add(v, ch[i]);
}

static void snap_save(void) {
    snNv = nv;
    memcpy(snAdj, adjv, sizeof(int) * (size_t)nv * DEGMAX);
    memcpy(snDeg, deg, sizeof(int) * (size_t)nv);
    memcpy(snBad, badv, sizeof(int) * (size_t)nv);
}

static void snap_restore(void) {
    nv = snNv;
    memcpy(adjv, snAdj, sizeof(int) * (size_t)nv * DEGMAX);
    memcpy(deg, snDeg, sizeof(int) * (size_t)nv);
    memcpy(badv, snBad, sizeof(int) * (size_t)nv);
}

static void save_best(void) {
    bestNv = nv;
    memcpy(bestAdj, adjv, sizeof(int) * (size_t)nv * DEGMAX);
    memcpy(bestDeg, deg, sizeof(int) * (size_t)nv);
    memcpy(bestCol, col, sizeof(int) * (size_t)nv);
    have_valid = 1;
}

static void load_best(void) {
    nv = bestNv;
    memcpy(adjv, bestAdj, sizeof(int) * (size_t)nv * DEGMAX);
    memcpy(deg, bestDeg, sizeof(int) * (size_t)nv);
    memcpy(col, bestCol, sizeof(int) * (size_t)nv);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [stall]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long stallLim = 400;
    if (argc >= 6) stallLim = atol(argv[5]);
    if (stallLim < 20) stallLim = 20;
    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n > MAXN - 4) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) {
        deg[i] = 0;
        col[i] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (nv == 0) {
        printf("0 0\n");
        return 0;
    }

    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    long long cur = eval_cost();
    if (cur == 0) save_best();
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    long long curMin = cur;

    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
        if (frac >= 1.0) break;

        if (cur == 0) {
            if (!have_valid || nv > bestNv) save_best();
            if (nv + 2 >= MAXN) break;
            grow_cover();
            cur = eval_cost();
            curMin = cur;
            stall = 0;
            continue;
        }

        double T = 0.15 + 0.6 * (1.0 - frac);
        snap_save();
        if (rnd01() < 0.25) {
            if (!swap_move()) continue;
        } else {
            relocate_move();
        }
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            snap_restore();
        }

        if (cur < curMin) {
            curMin = cur;
            stall = 0;
        } else if (++stall > stallLim) {
            if (have_valid) load_best();
            if (nv + 2 < MAXN) grow_cover();
            for (int k = 0; k < 3; k++) swap_move();
            cur = eval_cost();
            curMin = cur;
            stall = 0;
        }
    }

    if (cur == 0 && (!have_valid || nv > bestNv)) save_best();
    if (!have_valid) {
        printf("0 0\n");
        return 0;
    }

    long long em = 0;
    for (int v = 0; v < bestNv; v++) em += bestDeg[v];
    printf("%d %lld\n", bestNv, em / 2);
    for (int v = 0; v < bestNv; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q), degree q + 1, diameter 4.

    Returns (n, edges, P) where the first P vertices are points.
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
    edges = []
    nlines = 0
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
            for p in L:
                edges.append((p, P + nlines))
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nlines += 1
    return P + nlines, edges, P


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 keeps Python time low)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate(n, edges, d, P, rng):
    """Add edges between deficient point and line vertices (sides 0..P-1 and P..n-1)."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(P) if deg[v] < d]
    right = [v for v in range(P, n) if deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _run_c(d, D, seed, graph, budget, stall):
    """Run the C repair engine from `graph` for about `budget` seconds."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Starting graphs: projective planes for D = 3, saturated W(q) for D >= 4.
    starts = []
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            starts.append((pn, pe))
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            gn, ge, P = gq
            consider(gn, ge)
            sat_e = _saturate(gn, ge, d, P, rng)
            consider(gn, sat_e)
            starts.append((gn, sat_e))
    if not starts:
        starts.append(best)

    # Main search: the C repair engine, first from the first start, then from the best.
    end = start + 0.9 * tl - 1.5
    stall = 400
    src = starts[0]
    for idx in range(2):
        remaining = end - time.monotonic()
        if remaining < 3.0:
            break
        budget = remaining * (0.6 if idx == 0 else 1.0)
        try:
            n2, e2 = _run_c(d, D, seed + idx, src, budget, stall)
            consider(n2, e2)
        except Exception:
            pass
        src = best

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
