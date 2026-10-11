import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with a fixed vertex set.
# Cost = number of unordered pairs at distance > D (unreachable counts as bad).
# Moves keep max degree <= d and bipartiteness (sides are fixed per vertex).
# Whenever the cost reaches 0 the engine saves the graph and appends one more
# isolated vertex, so it grows the order while staying valid. It always prints
# a graph; Python re-checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW 25
#define DCAP 64
#define MAXE (MAXN * DCAP)

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;
static int vis[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (nb[u][i] > u && m < MAXE) {
                bestU[m] = u; bestV[m] = nb[u][i]; m++;
            }
        }
    }
    best_n = n; best_m = m;
}

static int color_graph(void) {
    static int queue[MAXN];
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* a -- b  becomes  a -- w, where w is on the same side as b. */
static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int ok = (n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1);
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    int cur_bad = bad_pairs();
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }

    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            have_best = 1;
            if (n >= MAXN - 2) break;
            side[n] = n & 1;
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            continue;
        }

        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind = 0, ua = 0, ub = 0, uw = 0, applied = 0;
        int r = rint_(100);
        if (r < 55) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
        else if (r < 90) { kind = 1; applied = move_add(&ua, &ub); }
        else { kind = 2; applied = move_remove(&ua, &ub); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }

    if (!have_best) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective plane data and arcs.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, point_lines, line_points, index, pts) for PG(2, q).

    Points are 0..m-1 and line j is vertex m+j in lib.projective_plane_incidence.
    Line j has the same coordinate vector pts[j] as point j, so an index set can
    be read either as points or as lines.
    """
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, point_lines, line_points, index, pts


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as an index set: no three collinear, and dually no three concurrent."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy_point_arc(m, s, point_lines, rng):
    """Random maximal set of points with at most s of them on every line (pencil centres for X)."""
    order = list(range(m))
    rng.shuffle(order)
    cl = [0] * m
    S = []
    for P in order:
        if all(cl[L] < s for L in point_lines[P]):
            S.append(P)
            for L in point_lines[P]:
                cl[L] += 1
    return S


def _greedy_line_arc(m, s, line_points, rng):
    """Random maximal set of lines with at most s of them through every point (dual pencils for Y)."""
    order = list(range(m))
    rng.shuffle(order)
    cp = [0] * m
    S = []
    for L in order:
        if all(cp[P] < s for P in line_points[L]):
            S.append(L)
            for P in line_points[L]:
                cp[P] += 1
    return S


# ----------------------------------------------------------------------------
# New helper: cover extension.
#
# Base graph: PG(2,q) incidence. Spare degree s = d - q - 1 on every vertex.
# Extra point-class vertex X: adjacent to a set T of lines (|T| <= d). Extra
# line-class vertex Y: adjacent to a set T of points. Let the base graph have
# diameter 3. The new graph keeps diameter 3 exactly when
#   (a) every X's line set covers all points, and every Y's point set covers
#       all lines (then every X reaches every point in 2 steps, every line in 3),
#   (b) any two X's share a line, and any two Y's share a point (same-side pairs
#       need distance 2),
#   (c) each line is used by at most s X's, each point by at most s Y's.
# Cross pairs X-Y are then automatically at distance <= 3. The result is still
# checked with lib.is_valid.
# The base pencils (X at a point of an arc, Y at a line of a dual arc) satisfy
# (a)-(c) and reproduce the parent's 394 for d = 16.
# ----------------------------------------------------------------------------

def _cover_search(nu, cover_of_block, elem_blocks, load, cap, existing, dmax, rng):
    """Randomized greedy: a set of blocks covering all nu elements, hitting every existing set,
    using only blocks with load < cap and of size <= dmax. Returns a list of blocks or None."""
    nb = len(cover_of_block)
    gain = [len(c) for c in cover_of_block]
    covered = [False] * nu
    unc = nu
    ex_of = [[] for _ in range(nb)]
    for idx, E in enumerate(existing):
        for b in E:
            ex_of[b].append(idx)
    hit = [False] * len(existing)
    unhit = len(existing)
    noise = [rng.random() * 0.5 for _ in range(nb)]
    used = [False] * nb
    chosen = []
    while unc > 0 or unhit > 0:
        if len(chosen) >= dmax:
            return None
        best, bs, bh = -1, -1e18, 0
        for b in range(nb):
            if used[b] or load[b] >= cap:
                continue
            hg = 0
            for idx in ex_of[b]:
                if not hit[idx]:
                    hg += 1
            sc = gain[b] + 2.0 * hg + noise[b]
            if sc > bs:
                bs, best, bh = sc, b, hg
        if best < 0 or (gain[best] == 0 and bh == 0):
            return None
        used[best] = True
        chosen.append(best)
        for e in cover_of_block[best]:
            if not covered[e]:
                covered[e] = True
                unc -= 1
                for b2 in elem_blocks[e]:
                    gain[b2] -= 1
        for idx in ex_of[best]:
            if not hit[idx]:
                hit[idx] = True
                unhit -= 1
    return chosen


def _extend(m, point_lines, line_points, s, d, xsets, ysets, rng, deadline):
    """Greedily add point-class covers (xsets) and line-class covers (ysets) until repeated failure."""
    lload = [0] * m
    pload = [0] * m
    for T in xsets:
        for L in T:
            lload[L] += 1
    for T in ysets:
        for P in T:
            pload[P] += 1
    if max(lload) > s or max(pload) > s:
        return None
    fails = 0
    while fails < 40 and time.monotonic() < deadline:
        if rng.random() < 0.5:
            T = _cover_search(m, line_points, point_lines, lload, s, xsets, d, rng)
            if T is not None:
                xsets.append(T)
                for L in T:
                    lload[L] += 1
                fails = 0
                continue
        else:
            T = _cover_search(m, point_lines, line_points, pload, s, ysets, d, rng)
            if T is not None:
                ysets.append(T)
                for P in T:
                    pload[P] += 1
                fails = 0
                continue
        fails += 1
    return xsets, ysets


def _assemble(m, point_lines, line_points, xsets, ysets):
    """Points 0..m-1, lines m..2m-1, then X vertices (point class), then Y vertices (line class)."""
    n = 2 * m + len(xsets) + len(ysets)
    E = []
    for P in range(m):
        for L in point_lines[P]:
            E.append((P, m + L))
    t = 2 * m
    for T in xsets:
        for L in T:
            E.append((t, m + L))
        t += 1
    for T in ysets:
        for P in T:
            E.append((P, t))
        t += 1
    return n, E


def _extension_search(q, d, rng, deadline):
    """Try random base arcs plus cover extension for PG(2,q). Returns the largest valid-by-construction (n, edges)."""
    s = d - q - 1
    m, point_lines, line_points, index, pts = _pg_data(q)
    best = (2 * m, [(P, m + L) for P in range(m) for L in point_lines[P]])
    if s < 1:
        return best
    conic = []
    if s >= 2:
        conic = _conic_set(q, index, lib.GF(q))
    trial = 0
    best_total = 0
    while time.monotonic() < deadline:
        trial += 1
        if s >= 2 and trial % 2 == 1:
            SA, SB = conic, conic
        else:
            SA = _greedy_point_arc(m, s, point_lines, rng)
            SB = _greedy_line_arc(m, s, line_points, rng)
        xsets = [list(point_lines[P]) for P in SA]
        ysets = [list(line_points[L]) for L in SB]
        out = _extend(m, point_lines, line_points, s, d, xsets, ysets, rng, deadline)
        if out is None:
            continue
        xs, ys = out
        total = len(xs) + len(ys)
        if total > best_total:
            n_, E_ = _assemble(m, point_lines, line_points, xs, ys)
            if n_ > best[0]:
                best = (n_, E_)
                best_total = total
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.9 * time_limit - 1.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2. It is also the safe fallback.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best[0], list(best[1])

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    if D == 3:
        # Prime powers q with q + 1 <= d and q close to d-1 (large spare capacity is not needed).
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q) and q >= d - 6][:3]
        if qs:
            consider(lib.projective_plane_incidence(qs[0]))
            helper_end = t0 + 0.3 * (end - t0)
            for idx, q in enumerate(qs):
                now = time.monotonic()
                share = (helper_end - now) / (len(qs) - idx)
                if share <= 0.2:
                    break
                consider(_extension_search(q, d, random.Random(seed * 1009 + q), now + share))
    else:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # C annealing: starting from the best valid graph, it appends vertices and repairs.
    remaining = end - time.monotonic() - 2.0
    if remaining > 2.0 and best[0] < lib.moore_bound(d, D):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=remaining + 3)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
