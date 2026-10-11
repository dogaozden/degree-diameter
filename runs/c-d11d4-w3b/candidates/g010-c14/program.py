import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over bipartite graphs with three moves.
#
#   * swap: take edges a-b and c-e with a, c on the same side, replace them by
#     a-e and c-b. Degrees and bipartiteness are preserved.
#   * targeted: pick a vertex v, BFS to depth DIAM, pick a same-side vertex w
#     that v cannot reach in time, and rewire v-a, w-e into v-e, w-a.
#   * relocate: detach a random vertex v from all its neighbours and reattach it
#     to up to DEG opposite-side vertices.
#
# Stall kicks: with probability 1/2 a vertex-replace kick (delete a random vertex,
# move the last vertex into its slot, grow a fresh vertex), otherwise two relocates.
#
# Every move is recorded in an edit log so a rejected move is undone exactly.
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

/* Vertex-replace kick (structural): delete a random vertex v, move the last
   vertex into its index so indices stay contiguous, then grow a fresh vertex.
   Uses raw (unlogged) edits; the caller resets the log and re-evaluates. */
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
# Generalized quadrangle W(q) incidence graph (order 2(q+1)(q^2+1), degree q+1,
# diameter 4), built with numpy for the symplectic form.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    arr = np.array(pts, dtype=np.int64)
    mul, add = F.mul_table, F.add_table
    negt = np.array([F.neg(a) for a in range(q)], dtype=np.int64)
    X0, X1, X2, X3 = arr[:, 0], arr[:, 1], arr[:, 2], arr[:, 3]
    # Symplectic form B(x, y) = x0 y1 - x1 y0 + x2 y3 - x3 y2 for all point pairs.
    t1 = mul[X0[:, None], X1[None, :]]
    t2 = mul[X1[:, None], X0[None, :]]
    t3 = mul[X2[:, None], X3[None, :]]
    t4 = mul[X3[:, None], X2[None, :]]
    s = add[add[t1, negt[t2]], add[t3, negt[t4]]]
    Z = np.triu(s == 0, 1)
    covered = np.zeros((P, P), dtype=bool)
    lines = []
    for i, j in zip(*np.nonzero(Z)):
        i = int(i)
        j = int(j)
        if covered[i, j]:
            continue
        x, y = pts[i], pts[j]
        L = set()
        for a in range(q):
            for b in range(q):
                if a == 0 and b == 0:
                    continue
                v = [F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4)]
                c = next(t for t in v if t)
                inv = F.inv(c)
                L.add(index[tuple(F.mul(inv, t) for t in v)])
        L = sorted(L)
        lines.append(L)
        idx = np.array(L, dtype=np.int64)
        covered[np.ix_(idx, idx)] = True
    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return P + len(lines), edges


def _best_gq(d):
    """W(q) for the largest prime power q (q <= 11) with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 11 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: delete vertices from W(q) with q + 1 > d until max degree
# is at most d and diameter is at most D. Removal of vertices never adds edges,
# so the result is bipartite and keeps the degree bound. Degrees are fixed by
# deleting neighbours of over-full vertices; diameter is repaired by deleting
# the vertices involved in the most bad pairs.
# ----------------------------------------------------------------------------

def _bad_counts(n, adj, alive, D):
    """Per alive vertex, the number of alive vertices at distance > D (bitset BFS)."""
    reach = [(1 << v) if alive[v] else 0 for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            if not alive[v]:
                continue
            r = reach[v]
            for u in adj[v]:
                if alive[u]:
                    r |= reach[u]
            new[v] = r
        reach = new
    alive_cnt = sum(1 for v in range(n) if alive[v])
    return [alive_cnt - reach[v].bit_count() if alive[v] else 0 for v in range(n)]


def _gq_delete(n, edges, d, D, deadline, rng):
    """Return a boolean alive-mask giving a subgraph with max degree <= d and diameter <= D, or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    alive = [True] * n
    frac = 0.01
    while time.monotonic() < deadline:
        if not any(alive):
            return None
        deg = [0] * n
        for v in range(n):
            if alive[v]:
                deg[v] = sum(1 for u in adj[v] if alive[u])
        order = list(range(n))
        rng.shuffle(order)
        for v in order:
            if not alive[v] or deg[v] <= d:
                continue
            need = deg[v] - d
            nbrs = [u for u in adj[v] if alive[u]]
            rng.shuffle(nbrs)
            nbrs.sort(key=lambda u: -deg[u])
            for u in nbrs:
                if need == 0:
                    break
                alive[u] = False
                for w in adj[u]:
                    if alive[w]:
                        deg[w] -= 1
                need -= 1
        counts = _bad_counts(n, adj, alive, D)
        if not any(counts):
            return alive
        live = [v for v in range(n) if alive[v]]
        bad = sorted((v for v in live if counts[v] > 0), key=lambda v: -counts[v])
        k = max(1, int(frac * len(live)))
        for v in bad[:k]:
            alive[v] = False
    return None


def _induced(n, edges, alive):
    """Relabel the subgraph induced by the alive vertices to 0..m-1."""
    new = {}
    for v in range(n):
        if alive[v]:
            new[v] = len(new)
    return len(new), [(new[u], new[v]) for u, v in edges if alive[u] and alive[v]]


def _gq_route(d, D, deadline, rng):
    """Build W(q) with q + 1 >= d (smallest such), delete down to degree d; return (n, edges) or None."""
    q = None
    for cand in range(d - 1, d + 4):
        if 2 <= cand <= 11 and lib.is_prime_power(cand) and cand + 1 >= d:
            q = cand
            break
    if q is None:
        return None
    n0, e0 = _gq_w(q)
    if q + 1 == d:
        return n0, e0
    alive = _gq_delete(n0, e0, d, D, deadline, rng)
    if alive is None:
        return None
    return _induced(n0, e0, alive)


# ----------------------------------------------------------------------------
# Growth helpers: twin vertices, cover-based vertex insertion, saturation,
# BFS-verified insertion.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same neighbourhood as an existing vertex) while degrees allow."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


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


def _cand_matrix(cand_balls, n):
    """Boolean matrix M[i, w] = 1 iff vertex w lies in the ball of candidate i."""
    nb = (n + 7) // 8
    buf = b"".join(x.to_bytes(nb, "little") for x in cand_balls)
    arr = np.frombuffer(buf, dtype=np.uint8).reshape(len(cand_balls), nb)
    return np.unpackbits(arr, axis=1, bitorder="little")[:, :n].astype(bool)


def _weighted_cover(B, cand_ids, n, d, nrng, randomize):
    """Hardest-first weighted set cover: rare uncovered vertices weigh more."""
    k = B.shape[0]
    uncov = np.ones(n, dtype=bool)
    avail = np.ones(k, dtype=bool)
    chosen = []
    for _ in range(d):
        if not uncov.any():
            break
        sub = B[:, uncov]
        cnt = sub.sum(axis=0)
        if (cnt == 0).any():
            return None
        w = 1.0 / cnt
        score = sub.astype(np.float64) @ w
        if randomize:
            score = score * (1.0 + 0.08 * nrng.random(k))
        score[~avail] = -1.0
        i = int(np.argmax(score))
        if score[i] <= 0:
            break
        avail[i] = False
        chosen.append(cand_ids[i])
        uncov &= ~B[i]
    return chosen if not uncov.any() else None


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices."""
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


def _find_cover(cands, ball, n, full, d, rng):
    """Try weighted covers first, then greedy covers."""
    B = _cand_matrix([ball[s] for s in cands], n)
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    for attempt in range(10):
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt > 0)
        if chosen:
            return chosen
    for attempt in range(3):
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if chosen:
            return chosen
    return None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within distance D-1."""
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
            chosen = _find_cover(cands, ball, n, full, d, rng)
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
    """Greedily join deficient opposite-side vertices that are not yet adjacent."""
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
    """Alternate cover-vertex growth and edge saturation."""
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def _multi_ball(adj, S, r, n):
    """Number of vertices within distance r of the source set S."""
    seen = bytearray(n)
    frontier = []
    for s in S:
        if not seen[s]:
            seen[s] = 1
            frontier.append(s)
    cnt = len(frontier)
    for _ in range(r):
        if not frontier:
            break
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = 1
                    nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _insert_search(n, adj, deg, color, d, D, rng, iters, deadline):
    """Find (colour, neighbour set) for a new vertex whose D-ball covers all n vertices, or None."""
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
        if not cands:
            continue
        k = min(d, len(cands))
        S = rng.sample(cands, k)
        best = _multi_ball(adj, S, D - 1, n)
        for _ in range(iters):
            if best >= n:
                return c, S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(k)
            s = rng.choice(cands)
            if s in S:
                continue
            T = S[:]
            T[i] = s
            val = _multi_ball(adj, T, D - 1, n)
            if val >= best:
                S, best = T, val
        if best >= n:
            return c, S
    return None


def _insert_grow(n, edges, d, D, deadline, rng):
    """Repeatedly insert BFS-verified vertices (old distances are never lengthened)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    fails = 0
    while time.monotonic() < deadline and fails < 25:
        res = _insert_search(n, adj, deg, color, d, D, rng, 80, deadline)
        if res is None:
            fails += 1
            continue
        c, S = res
        v = n
        n += 1
        color.append(c)
        adj.append(list(S))
        deg.append(len(S))
        for s in S:
            adj[s].append(v)
            deg[s] += 1
            edges.append((s, v))
        fails = 0
    return n, edges


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

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

    if D == 3:
        for q in [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            n2, e2 = _pipeline(pn, pe, d, D, start + 0.5 * tl, rng)
            consider(n2, e2)
        return best

    if D >= 4:
        use_c = d >= 5

        # Baseline: W(q) with degree q+1 <= d, saturated, then grown.
        gq = _best_gq(d)
        sat = None
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])
        base_end = start + (0.25 if use_c else 0.6) * tl
        pool = [x for x in (gq, sat) if x is not None]
        first = True
        while gq is not None and time.monotonic() < base_end:
            src = gq if first else rng.choice(pool + [best])
            first = False
            pn, pe = _pipeline(src[0], src[1], d, D, base_end, rng)
            consider(pn, pe)

        # New construction: W(q) with q + 1 > d, reduced by vertex deletion.
        route_best = None
        if use_c:
            new_end = start + 0.55 * tl
            res = _gq_route(d, D, start + 0.42 * tl, rng)
            if res is not None:
                hn, he = res
                hs = (hn, _saturate_edges(hn, he, d, rng))
                consider(hs[0], hs[1])
                pn, pe = _pipeline(hs[0], hs[1], d, D, new_end, rng)
                consider(pn, pe)
                route_best = (pn, pe) if pn >= hs[0] else hs

            # BFS-verified insertion on the best graph.
            try:
                gn, ge = _insert_grow(best_n, best[1], d, D, start + 0.66 * tl, rng)
                consider(gn, ge)
            except Exception:
                pass

            # C annealing from the best valid graph, then from the new-route graph.
            end = start + 0.92 * tl - 1.5
            starts_c = [best]
            if route_best is not None and route_best[0] != best[0]:
                starts_c.append(route_best)
            for idx, g in enumerate(starts_c):
                remaining = end - time.monotonic()
                if remaining < 2.0:
                    break
                share = 0.6 if (idx == 0 and len(starts_c) > 1) else 1.0
                try:
                    n2, e2 = _run_c(d, D, seed + idx, g, remaining * share)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
