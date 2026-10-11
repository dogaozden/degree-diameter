import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar graphs from difference covers.
#
# Haar graph H(Z_m, S): vertices a_i = i and b_j = m + j, with a_i ~ b_{i+s} for
# s in S. It is bipartite and d-regular when |S| = d. Its diameter is at most 3
# exactly when S - S covers Z_m, because same-side pairs are at distance <= 2
# and cross pairs are then at distance <= 3. So the largest valid order for
# degree d is 2m with m <= d(d-1)+1. The C code searches upward in m for a set
# S with 0 in S that covers all nonzero residues as differences, using simulated
# annealing on the number of uncovered residues.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int D_, M_;
static int S[MAXD];
static int cnt[MAXM];
static int uncovered;

static int md(int x) { x %= M_; if (x < 0) x += M_; return x; }

static void dec(int x) { if (x) { if (--cnt[x] == 0) uncovered++; } }
static void inc(int x) { if (x) { if (cnt[x]++ == 0) uncovered--; } }

static void remove_at(int idx) {
    int a = S[idx];
    for (int j = 0; j < D_; j++) {
        if (j != idx) {
            dec(md(a - S[j]));
            dec(md(S[j] - a));
        }
    }
}

static void place_at(int idx, int v) {
    S[idx] = v;
    for (int j = 0; j < D_; j++) {
        if (j != idx) {
            inc(md(v - S[j]));
            inc(md(S[j] - v));
        }
    }
}

static void init_random(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M_);
    uncovered = M_ - 1;
    S[0] = 0;
    for (int k = 1; k < D_; k++) {
        int v = 0, ok = 0;
        while (!ok) {
            v = 1 + (int)(rnd() % (uint64_t)(M_ - 1));
            ok = 1;
            for (int j = 0; j < k; j++) {
                if (S[j] == v) { ok = 0; break; }
            }
        }
        S[k] = v;
        for (int j = 0; j < k; j++) {
            inc(md(v - S[j]));
            inc(md(S[j] - v));
        }
    }
}

static int search(double budget_end) {
    while (cpu() < budget_end) {
        init_random();
        double T;
        double r = rnd01();
        if (r < 0.33) T = 0.3;
        else if (r < 0.66) T = 0.6;
        else T = 1.0;
        for (long it = 0; it < 3000000L; it++) {
            if (uncovered == 0) return 1;
            if ((it & 16383L) == 0 && cpu() >= budget_end) return 0;
            int idx = 1 + (int)(rnd() % (uint64_t)(D_ - 1));
            int v = 1 + (int)(rnd() % (uint64_t)(M_ - 1));
            int in = 0;
            for (int j = 0; j < D_; j++) {
                if (S[j] == v) { in = 1; break; }
            }
            if (in) continue;
            int old = S[idx];
            int U0 = uncovered;
            remove_at(idx);
            place_at(idx, v);
            int delta = uncovered - U0;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) continue;
            remove_at(idx);
            place_at(idx, old);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    int d = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    int mhi = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double tl = atof(argv[5]);
    if (d < 2 || d > MAXD || mhi >= MAXM) { printf("0 0\n"); return 0; }
    if (mlo < d + 1) mlo = d + 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    D_ = d;
    double t0 = cpu();
    int best_m = -1;
    int bestS[MAXD];
    int fails = 0;
    for (int m = mlo; m <= mhi; m++) {
        double rem = tl - (cpu() - t0);
        if (rem < 0.05) break;
        M_ = m;
        int ok = search(cpu() + 0.3 * rem);
        if (ok) {
            best_m = m;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            fails = 0;
        } else {
            fails++;
            if (fails >= 3) break;
        }
    }
    if (best_m < 0) { printf("0 0\n"); return 0; }
    int m = best_m;
    printf("%d %d\n", 2 * m, m * d);
    for (int i = 0; i < m; i++) {
        for (int k = 0; k < d; k++) {
            int s = bestS[k];
            printf("%d %d\n", i, m + (i + s) % m);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as the
# Python-side fallback candidate.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def _side_colors(n, adj):
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


def _ball_masks(n, adj, R):
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------
# Haar graph search through the C engine.
# ----------------------------------------------------------------------------

def _haar_search(d, seed, start, total):
    """Run the C difference-cover search; return (n, edges) or None."""
    mlo = max(d + 1, (d * d - d + 1) // 2)
    mhi = d * d - d + 1
    budget = max(1.0, 0.85 * total - (time.monotonic() - start) - 1.0)
    text = lib.run_c(C_SOURCE, [d, mlo, mhi, seed, round(budget, 2)],
                     stdin_graph=None, timeout=budget + 5.0)
    n, edges = lib.parse_graph_text(text)
    if n <= 0:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

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
        # Stage 1: arc-extended projective plane graphs, then greedy insertion.
        try:
            arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
            if arcs:
                n_a, e_a = arcs[0]
                n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.20 * time_limit)
                consider(n2, e2)
        except Exception:
            pass

        # Stage 2: cyclic Haar graphs from difference covers (new construction).
        if d >= 3:
            try:
                res = _haar_search(d, seed, start, 0.85 * time_limit)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
