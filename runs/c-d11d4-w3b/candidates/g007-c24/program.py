import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over bipartite graphs with three moves
# (swap, targeted rewire, relocate), stall kicks, and an exact undo log.
# Cost = number of unordered vertex pairs at distance > DIAM. Whenever cost is 0
# the state is saved as the best valid graph and grown by one vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define LOGMAX 1024

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;
static int defi[MAXN], fulli[MAXN], stk[MAXN];
static int logOp[LOGMAX], logA[LOGMAX], logB[LOGMAX], logN;
static int stampArr[MAXN], distArr[MAXN], qbuf[MAXN];
static int stampCur = 0;

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

static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += nv - cnt;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void raw_del_half(int a, int b) {
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
    raw_del_half(a, b);
    raw_del_half(b, a);
}

static void log_push(int op, int a, int b) {
    if (logN < LOGMAX) {
        logOp[logN] = op;
        logA[logN] = a;
        logB[logN] = b;
        logN++;
    }
}

static void edit_remove(int a, int b) {
    raw_remove(a, b);
    log_push(0, a, b);
}

static void edit_add(int a, int b) {
    raw_add(a, b);
    log_push(1, a, b);
}

static void undo_log(void) {
    for (int i = logN - 1; i >= 0; i--) {
        if (logOp[i] == 0) raw_add(logA[i], logB[i]);
        else raw_remove(logA[i], logB[i]);
    }
    logN = 0;
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int swap_move(void) {
    int a = rnd(nv);
    if (deg[a] == 0) return 0;
    int c = -1;
    for (int t = 0; t < 200; t++) {
        int x = rnd(nv);
        if (x != a && col[x] == col[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int b = adjv[a][rnd(deg[a])];
    int e = adjv[c][rnd(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    logN = 0;
    edit_remove(a, b);
    edit_remove(c, e);
    edit_add(a, e);
    edit_add(c, b);
    return 1;
}

static int targeted_move(void) {
    int v = rnd(nv);
    if (deg[v] == 0) return 0;
    stampCur++;
    int qh = 0, qt = 0;
    qbuf[qt++] = v;
    stampArr[v] = stampCur;
    distArr[v] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        if (distArr[u] >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int x = adjv[u][i];
            if (stampArr[x] != stampCur) {
                stampArr[x] = stampCur;
                distArr[x] = distArr[u] + 1;
                qbuf[qt++] = x;
            }
        }
    }
    int cnt = 0, w = -1;
    for (int x = 0; x < nv; x++) {
        if (col[x] != col[v] || stampArr[x] == stampCur) continue;
        cnt++;
        if (rnd(cnt) == 0) w = x;
    }
    if (w < 0 || deg[w] == 0) return 0;
    int a = adjv[v][rnd(deg[v])];
    int e = adjv[w][rnd(deg[w])];
    if (a == e) return 0;
    if (has_edge(v, e) || has_edge(w, a)) return 0;
    logN = 0;
    edit_remove(v, a);
    edit_remove(w, e);
    edit_add(v, e);
    edit_add(w, a);
    return 1;
}

static int relocate_move(void) {
    int v = rnd(nv);
    int c = col[v];
    logN = 0;
    while (deg[v] > 0) edit_remove(v, adjv[v][deg[v] - 1]);
    int nd = 0, nf = 0;
    for (int w = 0; w < nv; w++) {
        if (w == v || col[w] == c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        edit_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        edit_remove(w, x);
        edit_add(v, w);
        k++;
    }
    return 1;
}

static void grow(void) {
    int c = rnd(2);
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    int nd = 0, nf = 0;
    for (int w = 0; w < v; w++) {
        if (col[w] != 1 - c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        raw_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        raw_remove(w, x);
        raw_add(v, w);
        k++;
    }
}

static void vertex_replace_kick(void) {
    if (nv < 3) return;
    int v = rnd(nv);
    while (deg[v] > 0) raw_remove(v, adjv[v][deg[v] - 1]);
    int L = nv - 1;
    if (v != L) {
        for (int i = 0; i < deg[L]; i++) {
            int w = adjv[L][i];
            for (int j = 0; j < deg[w]; j++)
                if (adjv[w][j] == L) adjv[w][j] = v;
        }
        memcpy(adjv[v], adjv[L], sizeof(int) * DEGMAX);
        deg[v] = deg[L];
        col[v] = col[L];
        deg[L] = 0;
    }
    nv--;
    grow();
}

static void save_best(void) {
    memcpy(bestAdj, adjv, sizeof adjv);
    memcpy(bestDeg, deg, sizeof deg);
    memcpy(bestCol, col, sizeof col);
    bestNv = nv;
}

static void restore_best(void) {
    memcpy(adjv, bestAdj, sizeof adjv);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    nv = bestNv;
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
    long stallLim = 1500;
    if (argc >= 6) stallLim = atol(argv[5]);
    if (stallLim < 50) stallLim = 50;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) { deg[i] = 0; col[i] = -1; }
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

    long long cur_cost = eval_cost();
    save_best();
    int have_valid = (cur_cost == 0);
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    logN = 0;

    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
        if (frac >= 1.0) break;

        if (cur_cost == 0) {
            if (nv > bestNv || !have_valid) {
                save_best();
                have_valid = 1;
            }
            if (nv + 1 >= MAXN) break;
            grow();
            cur_cost = eval_cost();
            stall = 0;
            continue;
        }

        double T = 0.12 + 0.5 * (1.0 - frac);
        double pm = rnd01();
        int ok;
        if (pm < 0.35) ok = swap_move();
        else if (pm < 0.70) ok = targeted_move();
        else ok = relocate_move();
        if (!ok) {
            logN = 0;
            continue;
        }
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur_cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur_cost = c2;
            logN = 0;
        } else {
            undo_log();
        }

        if (++stall > stallLim) {
            restore_best();
            logN = 0;
            if (rnd01() < 0.5) {
                vertex_replace_kick();
            } else {
                for (int k = 0; k < 2; k++) relocate_move();
            }
            logN = 0;
            cur_cost = eval_cost();
            stall = 0;
        }
    }

    if (cur_cost == 0 && (nv > bestNv || !have_valid)) save_best();

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
# Constructions.
#
# Changed strategy for D >= 4 targets: instead of spending most of the budget
# in the cover-extension pipeline, the new run order is
#   1. generalized quadrangle W(q) (diameter 4) plus saturation of spare degree;
#   2. greedy cover-vertex extension, which keeps diameter <= D by construction
#      (a new vertex joined to a set S stays within D of everything if the
#      (D-1)-balls of S cover the graph; old distances never grow);
#   3. non-cyclic bi-Cayley group lifts with small bases, searched by voltage
#      hill-climbing, with group orders aimed just above best_n / (2k);
#   4. C annealing from the best valid graph, then from the saturated quadrangle.
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q + 1, diameter 4, order 2(q+1)(q^2+1)."""
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
    """W(q) for the largest prime power q <= d - 1 (so q + 1 <= d), q <= 16."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


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


def _greedy_cover(cands, ball, full, d, rng, tries):
    """Greedy set cover of `full` by at most d candidates; randomized restarts after the first try."""
    for t in range(tries):
        pool = list(cands)
        if t:
            rng.shuffle(pool)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d and pool:
            gains = [(ball[s] & ~covered).bit_count() for s in pool]
            mx = max(gains)
            if mx <= 0:
                break
            opts = [i for i, g in enumerate(gains) if g == mx]
            i = rng.choice(opts) if t else opts[0]
            s = pool.pop(i)
            chosen.append(s)
            covered |= ball[s]
        if covered == full:
            return chosen
    return None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods (<= d same-side vertices) cover all of V within radius D-1.

    Old distances never grow, the new vertex is within D of everything, and bipartiteness holds.
    """
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
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, ball, full, d, rng, 6)
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


def _sample_group(G, rng):
    """(order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular k+k base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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

    use_c = D >= 3 and d >= 4

    # Base structures.
    base = None
    if D >= 4:
        base = _best_gq(d)
    elif D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            base = lib.projective_plane_incidence(qs[0])

    sat = None
    if base is not None:
        consider(base[0], base[1])
        sat = (base[0], _saturate_edges(base[0], base[1], d, rng))
        consider(sat[0], sat[1])

    # Phase A: cover-vertex extension from the quadrangle / plane (diameter-safe by construction).
    if sat is not None:
        phase_a_end = start + (0.30 if use_c else 0.6) * tl
        cur_n, cur_e = _extend_cover(sat[0], sat[1], d, D, phase_a_end, rng)
        consider(cur_n, cur_e)
        if cur_n > sat[0]:
            cur_e = _saturate_edges(cur_n, cur_e, d, rng)
            consider(cur_n, cur_e)

    # Phase B: non-cyclic bi-Cayley group lifts with small bases.
    if D >= 3 and d >= 3:
        group_end = start + (0.50 if use_c else 0.8) * tl
        group_sizes = [1, 2, 3]
        state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
        while time.monotonic() < group_end:
            k = rng.choice(group_sizes)
            st = state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 150, group_end)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor

    # Phase C: C annealing from the best valid graph, then from the saturated base.
    if use_c:
        end = start + 0.92 * tl - 1.5
        starts_c = [best]
        if sat is not None:
            starts_c.append(sat)
        for idx, g in enumerate(starts_c):
            remaining = end - time.monotonic()
            if remaining < 2.0:
                break
            share = 0.65 if (idx == 0 and len(starts_c) > 1) else 1.0
            try:
                n2, e2 = _run_c(d, D, seed + idx, g, remaining * share)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
