import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over bipartite graphs with two moves.
#
#   * swap: take edges a-b and c-e with a, c on the same side, replace them by
#     a-e and c-b. Degrees and bipartiteness are preserved.
#   * relocate: detach a random vertex v from all its neighbours and reattach it
#     to up to DEG opposite-side vertices (deficient ones first, then full ones
#     with one stolen edge each). Changes the structure more than a swap.
#
# Every move is recorded in an edit log so a rejected move is undone exactly.
# Cost = number of unordered vertex pairs at distance > DIAM, computed with
# bitset ball propagation. Whenever cost is 0 the state is saved as the best
# valid graph and grown by one vertex (grow). Stalls restore the best graph and
# apply a small random kick. Optional argv[5] sets the stall limit.
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

/* Undo the logged edits in reverse order, restoring the previous state. */
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

    /* two-colour the start graph by DFS */
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
        int ok = (rnd01() < 0.6) ? swap_move() : relocate_move();
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
            for (int k = 0; k < 2; k++) relocate_move();
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
# Generalized quadrangle W(q) built with numpy.
# Points of PG(3,q); lines are totally isotropic for B(x,y) = x0y1 - x1y0 + x2y3 - x3y2.
# ----------------------------------------------------------------------------

def _gq_fast(q):
    """Return (P, Lc, M, iso): P points, Lc lines, M the P x Lc incidence, iso the collinearity matrix."""
    F = lib.GF(q)
    pts = np.array([v for v in itertools.product(range(q), repeat=4)
                    if any(v) and next(c for c in v if c) == 1], dtype=np.int64)
    P = len(pts)
    mul, add = F.mul_table, F.add_table
    neg = np.array([F.neg(a) for a in range(q)], dtype=np.int64)
    inv = np.array([0] + [F.inv(a) for a in range(1, q)], dtype=np.int64)
    t01 = mul[pts[:, None, 0], pts[None, :, 1]]
    t10 = mul[pts[:, None, 1], pts[None, :, 0]]
    t23 = mul[pts[:, None, 2], pts[None, :, 3]]
    t32 = mul[pts[:, None, 3], pts[None, :, 2]]
    iso = add[add[t01, neg[t10]], add[t23, neg[t32]]] == 0

    qpow = q ** np.arange(4, dtype=np.int64)
    lookup = np.full(q ** 4, -1, dtype=np.int64)
    lookup[pts @ qpow] = np.arange(P, dtype=np.int64)
    AB = np.array([(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)],
                  dtype=np.int64)
    ca, cb = AB[:, :1], AB[:, 1:]
    covered = np.zeros((P, P), dtype=bool)
    lines = []
    for i in range(P):
        js = np.nonzero(iso[i, i + 1:] & ~covered[i, i + 1:])[0] + i + 1
        for j in js:
            if covered[i, j]:
                continue
            v = add[mul[ca, pts[i][None, :]], mul[cb, pts[j][None, :]]]
            idx = np.argmax(v != 0, axis=1)
            c = v[np.arange(v.shape[0]), idx]
            v = mul[inv[c][:, None], v]
            L = np.unique(lookup[v @ qpow])
            lines.append(L)
            covered[np.ix_(L, L)] = True
    Lc = len(lines)
    M = np.zeros((P, Lc), dtype=bool)
    for j, L in enumerate(lines):
        M[L, j] = True
    return P, Lc, M, iso


def _gq_graph(q):
    """Incidence graph of W(q): degree q+1, diameter 4, order 2(q+1)(q^2+1)."""
    P, Lc, M, _ = _gq_fast(q)
    r, c = np.nonzero(M)
    return P + Lc, [(a, P + b) for a, b in zip(r.tolist(), c.tolist())]


def _partial_ovoid(P, iso, rng):
    """Random maximal set of pairwise non-collinear points."""
    order = list(range(P))
    rng.shuffle(order)
    blocked = np.zeros(P, dtype=bool)
    S = []
    for p in order:
        if not blocked[p]:
            S.append(p)
            blocked |= iso[p]
    return S


def _cut_graph(P, Lc, M, iso, rng):
    """Degree-cut of W(q) to degree q, from a partial ovoid S of points.

    Kept lines are exactly the lines meeting S (each meets S once, so has q points).
    Lines missing S are deleted; uncovered points get an extra deleted line each.
    Returns (n, edges) with all degrees <= q, or None.
    """
    S = _partial_ovoid(P, iso, rng)
    inS = np.zeros(P, dtype=bool)
    inS[S] = True
    meet = M[S].any(axis=0)
    T = ~meet
    cov = M[:, T].any(axis=1)
    U = (~inS) & (~cov)
    avail = meet.copy()
    while U.any():
        score = (M[U] & avail[None, :]).sum(axis=0)
        j = int(np.argmax(score))
        if score[j] == 0:
            return None
        T[j] = True
        avail[j] = False
        U &= ~M[:, j]
    kp = np.nonzero(~inS)[0]
    kl = np.nonzero(~T)[0]
    r, c = np.nonzero(M[np.ix_(kp, kl)])
    n = len(kp) + len(kl)
    edges = [(a, len(kp) + b) for a, b in zip(r.tolist(), c.tolist())]
    return n, edges


# ----------------------------------------------------------------------------
# Greedy repair: delete the vertices involved in the most bad pairs until the
# graph has diameter <= D. Deletion keeps degree and bipartiteness.
# ----------------------------------------------------------------------------

def _ball_masks(n, adj, D):
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _greedy_repair(n, edges, D, deadline):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    alive = [True] * n
    n_alive = n
    while True:
        if time.monotonic() > deadline:
            return None
        ball = _ball_masks(n, adj, D)
        counts = []
        total = 0
        for v in range(n):
            if alive[v]:
                c = n_alive - ball[v].bit_count()
                if c:
                    counts.append((c, v))
                    total += c
        if not counts:
            break
        bad = total // 2
        counts.sort(reverse=True)
        batch = max(1, min(n_alive // 80, bad // 10))
        for _, v in counts[:batch]:
            alive[v] = False
            n_alive -= 1
            for u in adj[v]:
                adj[u].discard(v)
            adj[v] = set()
    keep = [v for v in range(n) if alive[v]]
    idx = {v: i for i, v in enumerate(keep)}
    out = [(idx[u], idx[v]) for u in keep for v in adj[u] if u < v]
    return len(keep), out


def _gq_start(d, D, rng, deadline):
    """Valid diameter-D graph of max degree d built from a generalized quadrangle, or None."""
    if 2 <= d - 1 <= 13 and lib.is_prime_power(d - 1):
        return _gq_graph(d - 1)  # degree d exactly
    if 3 <= d <= 13 and lib.is_prime_power(d):
        P, Lc, M, iso = _gq_fast(d)  # degree d + 1, cut down to d
        cut = _cut_graph(P, Lc, M, iso, rng)
        if cut is None:
            return None
        return _greedy_repair(cut[0], cut[1], D, deadline)
    return None


# ----------------------------------------------------------------------------
# Twin extension: a twin v of x (same side, N(v) = N(x)) keeps old distances,
# has dist(v, x) = 2, and preserves bipartiteness.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(len(adj[y]) >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            for y in nb:
                adj[y].append(v)
                edges.append((y, v))
            changed = True
    return n, edges


def _largest_pp(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
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

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    # Baselines: projective plane (D = 3) or W(q) with q + 1 <= d (D = 4).
    try:
        q = _largest_pp(d - 1)
        if q is not None:
            if D == 3 and d >= 3:
                consider(lib.projective_plane_incidence(q))
            elif D == 4 and d >= 5 and q <= 13:
                consider(_gq_graph(q))
    except Exception:
        pass

    # Bold route for D = 4: generalized quadrangle cut down to degree d, then greedy repair.
    alt = None
    if D == 4 and d >= 5:
        try:
            alt = _gq_start(d, D, rng, start + 0.35 * tl)
            if alt is not None:
                alt = _twin_grow(alt[0], alt[1], d, D, start + 0.4 * tl, rng)
        except Exception:
            alt = None
        consider(alt)
        try:
            consider(_twin_grow(best[0], best[1], d, D, start + 0.4 * tl, rng))
        except Exception:
            pass

    # C annealing in chained rounds. Round 0 and 2 start from the best valid graph;
    # round 1 starts from the cut-and-repaired GQ graph when one exists.
    end = start + 0.92 * tl - 1.5
    rounds = 3
    for idx in range(rounds):
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        budget = remaining / (rounds - idx)
        src = alt if (idx == 1 and alt is not None) else best
        try:
            consider(_run_c(d, D, seed + idx, src, budget))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
