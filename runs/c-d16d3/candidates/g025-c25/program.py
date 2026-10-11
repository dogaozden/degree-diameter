import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset ball-cover insertion plus annealed edge-swap repair.
#
# State: bipartite graph with max degree d, colour classes fixed per vertex.
# cost = number of unordered pairs at distance > D (bitset balls of radius D).
# Moves:
#   * insertion: if cost == 0, add a vertex whose <= d neighbours on the other
#     side cover (within radius D-1) every vertex. This keeps cost 0 exactly.
#   * edge swap (a-b, c-e) -> (a-e, c-b) and edge addition, both keep bipartiteness
#     and degree bounds; accepted by Metropolis on cost.
# The best valid graph (largest n with cost 0) is snapshotted and printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 4096
#define WMAX (NMAX / 64)

static int d_, D_, n_;
static int *nb, *deg, *col;
static int *cand, *chosen, *used;
static uint64_t *ballR, *ballD, *tmpb;
static int *snapE, *snapCol;
static int snapN, snapM;
static uint64_t rs;

static uint64_t rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (nb[u * d_ + k] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    nb[u * d_ + deg[u]++] = v;
    nb[v * d_ + deg[v]++] = u;
}
static void del_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nb[u * d_ + k] == v) {
            nb[u * d_ + k] = nb[u * d_ + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void rem_edge(int u, int v) { del_half(u, v); del_half(v, u); }

static int nw(void) { return (n_ + 63) >> 6; }

static void step(const uint64_t *src, uint64_t *dst) {
    int w = nw();
    for (int v = 0; v < n_; v++) {
        uint64_t *o = dst + (size_t)v * WMAX;
        const uint64_t *s = src + (size_t)v * WMAX;
        for (int i = 0; i < w; i++) o[i] = s[i];
        for (int k = 0; k < deg[v]; k++) {
            const uint64_t *t = src + (size_t)nb[v * d_ + k] * WMAX;
            for (int i = 0; i < w; i++) o[i] |= t[i];
        }
    }
}

static void compute_balls(void) {
    memset(ballR, 0, sizeof(uint64_t) * (size_t)n_ * WMAX);
    for (int v = 0; v < n_; v++) ballR[(size_t)v * WMAX + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 1; it < D_ - 1; it++) {
        step(ballR, tmpb);
        memcpy(ballR, tmpb, sizeof(uint64_t) * (size_t)n_ * WMAX);
    }
    step(ballR, ballD);
}

static long long cost(void) {
    compute_balls();
    int w = nw();
    long long bad = 0;
    for (int v = 0; v < n_; v++) {
        int c = 0;
        for (int i = 0; i < w; i++) c += __builtin_popcountll(ballD[(size_t)v * WMAX + i]);
        bad += n_ - c;
    }
    return bad / 2;
}

/* Requires ballR of the current state (call cost() first). */
static int try_insert(void) {
    if (n_ >= NMAX) return 0;
    int w = nw();
    uint64_t full[WMAX], covered[WMAX];
    for (int i = 0; i < w; i++) {
        int rem = n_ - 64 * i;
        full[i] = rem >= 64 ? ~0ULL : ((1ULL << rem) - 1);
    }
    int s0 = rndint(2);
    for (int si = 0; si < 2; si++) {
        int s = (si == 0) ? s0 : 1 - s0;
        int nc = 0;
        for (int u = 0; u < n_; u++)
            if (col[u] == 1 - s && deg[u] < d_) cand[nc++] = u;
        if (nc == 0) continue;
        for (int att = 0; att < 4; att++) {
            for (int i = nc - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
            }
            memset(used, 0, sizeof(int) * (size_t)nc);
            for (int i = 0; i < w; i++) covered[i] = 0;
            int nch = 0;
            while (nch < d_) {
                int done = 1;
                for (int i = 0; i < w; i++) if (covered[i] != full[i]) { done = 0; break; }
                if (done) break;
                int bestg = 0, bj = -1;
                for (int j = 0; j < nc; j++) {
                    if (used[j]) continue;
                    const uint64_t *b = ballR + (size_t)cand[j] * WMAX;
                    int g = 0;
                    for (int i = 0; i < w; i++) g += __builtin_popcountll(b[i] & ~covered[i]);
                    if (g > bestg) { bestg = g; bj = j; }
                }
                if (bj < 0) break;
                used[bj] = 1;
                chosen[nch++] = cand[bj];
                const uint64_t *b = ballR + (size_t)cand[bj] * WMAX;
                for (int i = 0; i < w; i++) covered[i] |= b[i];
            }
            int ok = 1;
            for (int i = 0; i < w; i++) if (covered[i] != full[i]) { ok = 0; break; }
            if (ok) {
                int x = n_++;
                col[x] = s;
                deg[x] = 0;
                for (int k = 0; k < nch; k++) add_edge(x, chosen[k]);
                return 1;
            }
        }
    }
    return 0;
}

static int pick(int side, int mode) {
    for (int t = 0; t < 400; t++) {
        int v = rndint(n_);
        if (col[v] != side) continue;
        if (mode == 0 && deg[v] == 0) continue;
        if (mode == 1 && deg[v] >= d_) continue;
        return v;
    }
    return -1;
}

static void save_snapshot(void) {
    snapN = n_;
    for (int v = 0; v < n_; v++) snapCol[v] = col[v];
    int m = 0;
    for (int u = 0; u < n_; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = nb[u * d_ + k];
            if (v > u) {
                snapE[2 * m] = u;
                snapE[2 * m + 1] = v;
                m++;
            }
        }
    }
    snapM = m;
}

static void restore_snapshot(void) {
    n_ = snapN;
    for (int v = 0; v < n_; v++) {
        deg[v] = 0;
        col[v] = snapCol[v];
    }
    for (int i = 0; i < snapM; i++) add_edge(snapE[2 * i], snapE[2 * i + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)strtoull(argv[3], NULL, 10) * 0xBF58476D1CE4E5B9ULL);
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (d_ < 1 || D_ < 2) { printf("0 0\n"); return 0; }

    nb = malloc(sizeof(int) * (size_t)NMAX * d_);
    deg = calloc(NMAX, sizeof(int));
    col = calloc(NMAX, sizeof(int));
    cand = malloc(sizeof(int) * NMAX);
    chosen = malloc(sizeof(int) * NMAX);
    used = malloc(sizeof(int) * NMAX);
    ballR = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    ballD = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    tmpb = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    snapE = malloc(sizeof(int) * ((size_t)NMAX * d_ + 2));
    snapCol = malloc(sizeof(int) * NMAX);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 >= 2 && n0 <= NMAX) {
        n_ = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n_ || v >= n_ || u == v) continue;
            if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) continue;
            add_edge(u, v);
        }
        for (int v = 0; v < n_; v++) col[v] = -1;
        for (int s = 0; s < n_; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int h = 0, t = 0;
            cand[t++] = s;
            while (h < t) {
                int u = cand[h++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = nb[u * d_ + k];
                    if (col[v] == -1) {
                        col[v] = 1 - col[u];
                        cand[t++] = v;
                    }
                }
            }
        }
    } else {
        n_ = 2 * d_;
        for (int v = 0; v < n_; v++) col[v] = (v < d_) ? 0 : 1;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++)
                add_edge(i, d_ + j);
    }

    long long cur = cost();
    save_snapshot();

    clock_t t0 = clock();
    long long stall = 0;
    const double T = 0.4;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        if (cur == 0) {
            if (n_ > snapN) save_snapshot();
            cur = cost();
            if (cur == 0 && try_insert()) {
                cur = cost();
                if (cur != 0) { restore_snapshot(); cur = cost(); }
                stall = 0;
                continue;
            }
        }
        int mv, a = -1, b = -1, c = -1, e = -1;
        if (rnd01() < 0.6) {
            mv = 0;
            a = pick(0, 0);
            if (a < 0) continue;
            b = nb[a * d_ + rndint(deg[a])];
            c = pick(0, 0);
            if (c < 0 || c == a) continue;
            e = nb[c * d_ + rndint(deg[c])];
            if (e == b || has_edge(a, e) || has_edge(c, b)) continue;
            rem_edge(a, b);
            rem_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
        } else {
            mv = 1;
            a = pick(0, 1);
            b = pick(1, 1);
            if (a < 0 || b < 0 || has_edge(a, b)) continue;
            add_edge(a, b);
        }
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            if (mv == 0) {
                rem_edge(a, e);
                rem_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            } else {
                rem_edge(a, b);
            }
        }
        if (cur > 0) {
            if (++stall > 20000) {
                restore_snapshot();
                cur = cost();
                stall = 0;
            }
        } else {
            stall = 0;
        }
    }

    if (cur == 0 && n_ > snapN) save_snapshot();
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapE[2 * i], snapE[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python: projective-plane starts (with arc extensions) and glue.
# ----------------------------------------------------------------------------

def _pg_parts(q):
    """Incidence graph of PG(2, q) plus point->lines and line->points lists."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomised greedy arc-like set S with all loads <= s."""
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
    """Conic (plus nucleus for even q) as point indices."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus an A-vertex per P in S (on its lines) and a B-vertex per j in S (on its points)."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _arc_start(d, deadline, rng):
    """Largest arc-extended PG(2, q) with q + 1 <= d, or None."""
    best = None
    for q in range(2, d):
        if q > 16 or not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_parts(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
        if s >= 2:
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        n, E = _arc_graph(m, edges, point_lines, line_points, S)
        if best is None or n > best[0]:
            best = (n, E)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    # K_{d,d}: bipartite, degree d, diameter 2 (also valid for d = 1).
    best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2 or d == 1:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        arc = _arc_start(d, t0 + 0.08 * time_limit, random.Random(seed * 7919 + d))
        if arc is not None:
            consider(arc[0], arc[1])

    start = best
    c_budget = max(1.0, time_limit * 0.85 - 2.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, f"{c_budget:.2f}"],
                        stdin_graph=start, timeout=time_limit * 0.95)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    return best
