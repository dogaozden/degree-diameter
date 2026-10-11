import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: validity-preserving growth with annealing repair.
#
# State: a graph with fixed sides, max degree <= d, and cost = number of
# unordered pairs at distance > D. A snapshot of the last valid graph is kept.
#   1. When valid: try a cover insertion (new vertex joined to neighbours on the
#      opposite side whose (D-1)-balls cover everything). This keeps validity.
#   2. If that fails: add a vertex greedily joined to up to d neighbours (partial
#      cover), then anneal with rewire / add / remove / degree-preserving 2-switch
#      moves until the cost is 0 again.
#   3. If annealing stalls, restore the snapshot and retry with new randomness.
# The output is always the last valid snapshot (or the input if none exists).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define DCAP 64
#define MAXE 40960
#define LIM 8000
#define TEMP 0.6

typedef uint64_t row_t[MAXW];

typedef struct {
    int nr, na;
    int ru[2], rv[2], au[2], av[2];
} move_t;

static int n, d, D, cap;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static row_t RA[MAXN], RB[MAXN];
static int snapU[MAXE], snapV[MAXE];
static int snapM = 0, snapN = 0, have_snap = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1;
    adjm[v][u] = 1;
}

static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    rm_one(u, v);
    rm_one(v, u);
    adjm[u][v] = 0;
    adjm[v][u] = 0;
}

/* Rows of the radius-R ball bitsets; returns whichever buffer holds the result. */
static row_t *ball_calc(int R) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(row_t));
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    row_t *cur = RA, *nxt = RB;
    for (int t = 0; t < R; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        row_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    return cur;
}

static long bad_pairs(void) {
    int W = (n + 63) / 64;
    row_t *c = ball_calc(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int k = 0;
        for (int w = 0; w < W; w++) k += popc(c[v][w]);
        bad += n - k;
    }
    return bad / 2;
}

static int uncovered(const uint64_t *cov, int W) {
    int c = 0;
    for (int w = 0; w < W; w++) {
        uint64_t mask = ~0ULL;
        if (w == W - 1) {
            int r = n - 64 * (W - 1);
            if (r < 64) mask = (1ULL << r) - 1;
        }
        c += popc(~cov[w] & mask);
    }
    return c;
}

static int colour(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[qt++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void save_snapshot(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (v > u && m < MAXE) {
                snapU[m] = u;
                snapV[m] = v;
                m++;
            }
        }
    }
    snapM = m;
    snapN = n;
    have_snap = 1;
}

static void restore_snapshot(void) {
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        memset(adjm[v], 0, (size_t)n);
    }
    n = snapN;
    for (int i = 0; i < snapM; i++) add_edge(snapU[i], snapV[i]);
}

static void emit(void) {
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
}

/* Insert a vertex on side s. Full mode: neighbours must cover every vertex
   within distance D (validity kept). Partial mode: always adds a vertex with
   greedy neighbours, leaving some pairs uncovered for annealing to repair. */
static int try_insert(int s, int partial) {
    int W = (n + 63) / 64;
    row_t *B = ball_calc(D - 1);
    static int cand[MAXN];
    static char used[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (side[u] != s && deg[u] < d) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    for (int i = 0; i < nc; i++) used[cand[i]] = 0;
    row_t cov;
    memset(cov, 0, sizeof(cov));
    int chosen[DCAP];
    int nch = 0;
    while (nch < d) {
        if (uncovered(cov, W) == 0) break;
        int best = -1;
        long bg = partial ? -1 : 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            long g = 0;
            for (int w = 0; w < W; w++) g += popc(B[u][w] & ~cov[w]);
            if (g > bg) {
                bg = g;
                best = u;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= B[best][w];
    }
    if (!partial && uncovered(cov, W) != 0) return 0;
    int w = n;
    n++;
    side[w] = s;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static int pick_deg(void) {
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] > 0) return c;
    }
    return -1;
}

static int propose(move_t *m) {
    m->nr = 0;
    m->na = 0;
    int r = rint_(100);
    if (r < 40) {  /* rewire: a-b becomes a-c, c on the side of b */
        int a = pick_deg();
        if (a < 0) return 0;
        int b = nb[a][rint_(deg[a])];
        int c = -1;
        for (int t = 0; t < 64 && c < 0; t++) {
            int x = rint_(n);
            if (x != b && side[x] == side[b] && deg[x] < d && !adjm[a][x]) c = x;
        }
        if (c < 0) return 0;
        m->nr = 1; m->ru[0] = a; m->rv[0] = b;
        m->na = 1; m->au[0] = a; m->av[0] = c;
        return 1;
    }
    if (r < 65) {  /* add an edge between opposite sides */
        int x = -1, y = -1;
        for (int t = 0; t < 64 && x < 0; t++) {
            int c = rint_(n);
            if (deg[c] < d) x = c;
        }
        if (x < 0) return 0;
        for (int t = 0; t < 64 && y < 0; t++) {
            int c = rint_(n);
            if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) y = c;
        }
        if (y < 0) return 0;
        m->na = 1; m->au[0] = x; m->av[0] = y;
        return 1;
    }
    if (r < 90) {  /* degree-preserving 2-switch */
        int a = pick_deg();
        if (a < 0) return 0;
        int b = nb[a][rint_(deg[a])];
        int c = -1;
        for (int t = 0; t < 64 && c < 0; t++) {
            int x = rint_(n);
            if (x != a && side[x] == side[a] && deg[x] > 0) c = x;
        }
        if (c < 0) return 0;
        int e = nb[c][rint_(deg[c])];
        if (e == b || adjm[a][e] || adjm[c][b]) return 0;
        m->nr = 2; m->ru[0] = a; m->rv[0] = b; m->ru[1] = c; m->rv[1] = e;
        m->na = 2; m->au[0] = a; m->av[0] = e; m->au[1] = c; m->av[1] = b;
        return 1;
    }
    /* remove an edge */
    {
        int a = pick_deg();
        if (a < 0) return 0;
        int b = nb[a][rint_(deg[a])];
        m->nr = 1; m->ru[0] = a; m->rv[0] = b;
        return 1;
    }
}

static void apply_move(const move_t *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->ru[i], m->rv[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->au[i], m->av[i]);
}

static void undo_move(const move_t *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ru[i], m->rv[i]);
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    clock_t t0 = clock();

    if (d < 1 || d > DCAP || D < 1) { printf("0 0\n"); return 0; }
    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 1 || n > MAXN - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (adjm[u][v] || deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    if (D < 2 || !colour()) {
        save_snapshot();
        emit();
        return 0;
    }

    cap = MAXN - 2;
    if (d >= 3) {
        double mb = 0, p = 1;
        for (int i = 0; i < D; i++) { mb += p; p *= (double)(d - 1); }
        mb *= 2;
        if (mb < cap) cap = (int)mb;
    }

    long cur_bad = bad_pairs();
    if (cur_bad == 0) save_snapshot();
    long steps = 0;

    while (elapsed(t0) <= tl) {
        if (cur_bad == 0) {
            save_snapshot();
            if (n >= cap) break;
            int s0 = rint_(2), ok = 0;
            for (int k = 0; k < 2 && !ok; k++)
                ok = try_insert(k == 0 ? s0 : 1 - s0, 0);
            if (ok) {
                cur_bad = bad_pairs();
                if (cur_bad != 0 && have_snap) {
                    restore_snapshot();
                    cur_bad = 0;
                }
                continue;
            }
            try_insert(rint_(2), 1);
            cur_bad = bad_pairs();
            steps = 0;
            continue;
        }
        move_t mv;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long nbad = bad_pairs();
        long delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / TEMP)) {
            cur_bad = nbad;
        } else {
            undo_move(&mv);
        }
        if (++steps > LIM) {
            steps = 0;
            if (have_snap && cur_bad > 0) {
                restore_snapshot();
                cur_bad = 0;
            }
        }
    }
    if (cur_bad == 0) save_snapshot();
    if (!have_snap) save_snapshot();
    emit();
    return 0;
}
"""


def _c_grow(graph, d, D, seed, budget):
    """Run the C engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each vertex has degree q+1, spare s = d-q-1.
# SA: points, each line may contain <= s points of SA; an A-vertex joins the
#     q+1 lines through each P in SA.
# SB: lines, each point may lie on <= s lines of SB; a B-vertex joins the q+1
#     points on each line in SB.
# The two sides are independent, so SA and SB are maximized separately.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline) if s >= 1 else []
        SB = _greedy_side(m, s, line_points, rng, 30, deadline) if s >= 1 else []
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
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


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Build. Time plan (fractions of time_limit, minus a safety margin):
#   D >= 3: arc-extended PG graphs (up to 15%), then C growth for the rest.
#   D >= 4: GQ baseline, C growth for half the remaining time, then lift annealing.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)

    if D >= 4 and time.monotonic() < end:
        consider(_best_gq(d))

    if D >= 3 and end - time.monotonic() > 1.0:
        remaining = end - time.monotonic()
        budget = remaining if D == 3 else 0.5 * remaining
        consider(_c_grow(best, d, D, seed, budget))

    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
