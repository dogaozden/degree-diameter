"""Arc-extended projective-plane search with a C annealing improver.

Pipeline:
1. Python builds the best construction it knows: K_{d,d} (diameter 2), arc-extended
   projective-plane incidence graphs (diameter 3, twin vertices on both sides), and
   the generalized quadrangle for D >= 4.
2. If that is below the Moore bound, a C engine starts from it. It keeps a valid graph
   (degree <= d, bipartite, diameter <= D) and runs simulated annealing over edge moves
   (single-endpoint swaps, 2-switches, and edge additions). The cost is the number of
   ordered vertex pairs at distance > D. When the cost reaches 0 it adds a vertex and
   keeps searching. On stall it restores the best valid graph and perturbs it.
3. Python validates the C output with lib.is_valid and falls back to the Python base.
"""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
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
# Generalized quadrangle baseline (D = 4).
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
# C engine: validity-preserving annealing that tries to add vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXW 16
#define MAXD 72
#define STALL 60000

typedef uint64_t u64;

static int DEG_CAP, DIAM, N;
static int deg[MAXN];
static int adjm[MAXN][MAXD];
static unsigned char amat[MAXN][MAXN];
static int side[MAXN];
static u64 BA[MAXN][MAXW], BB[MAXN][MAXW];
static u64 rs;

static int bestN = 0;
static int bestDeg[MAXN];
static int bestAdj[MAXN][MAXD];

static u64 rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(rnd64() % (u64)k); }
static double unif(void) { return (double)(rnd64() >> 11) / 9007199254740992.0; }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static void rm_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjm[a][i] == b) {
            adjm[a][i] = adjm[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void add_e(int a, int b) {
    adjm[a][deg[a]++] = b;
    adjm[b][deg[b]++] = a;
    amat[a][b] = 1;
    amat[b][a] = 1;
}
static void del_e(int a, int b) {
    rm_half(a, b);
    rm_half(b, a);
    amat[a][b] = 0;
    amat[b][a] = 0;
}

/* Total number of ordered pairs (u,v) with dist(u,v) > DIAM. Zero means valid diameter. */
static long long cost(void) {
    int nw = (N + 63) / 64;
    u64 (*cur)[MAXW] = BA;
    u64 (*nxt)[MAXW] = BB;
    for (int u = 0; u < N; u++) {
        for (int w = 0; w < nw; w++) cur[u][w] = 0;
        cur[u][u >> 6] |= 1ULL << (u & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int u = 0; u < N; u++) {
            for (int w = 0; w < nw; w++) nxt[u][w] = cur[u][w];
            for (int i = 0; i < deg[u]; i++) {
                int v = adjm[u][i];
                for (int w = 0; w < nw; w++) nxt[u][w] |= cur[v][w];
            }
        }
        u64 (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long total = 0;
    for (int u = 0; u < N; u++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(cur[u][w]);
        total += N - c;
    }
    return total;
}

/* Sets side[] by BFS 2-colouring. Returns 1 if bipartite. */
static int color_graph(void) {
    static int st[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp) {
            int u = st[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adjm[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    st[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void build_complete(int d) {
    memset(amat, 0, sizeof amat);
    memset(deg, 0, sizeof deg);
    N = 2 * d;
    for (int a = 0; a < d; a++)
        for (int b = d; b < 2 * d; b++)
            add_e(a, b);
    color_graph();
}

static void save_best(void) {
    bestN = N;
    for (int u = 0; u < N; u++) {
        bestDeg[u] = deg[u];
        for (int i = 0; i < deg[u]; i++) bestAdj[u][i] = adjm[u][i];
    }
}

static void restore_best(void) {
    for (int u = 0; u < N; u++) {
        for (int v = 0; v < N; v++) amat[u][v] = 0;
        deg[u] = 0;
    }
    N = bestN;
    for (int u = 0; u < N; u++) {
        deg[u] = bestDeg[u];
        for (int i = 0; i < deg[u]; i++) {
            adjm[u][i] = bestAdj[u][i];
            amat[u][adjm[u][i]] = 1;
        }
    }
}

/* Propose a move as a list of ops: type 0 = add edge (a,b), type 1 = delete edge (a,b). */
static int propose(int *nops, int *ot, int *oa, int *ob) {
    int r = rnd(100);
    if (r < 30) {  /* add an edge between spare vertices */
        for (int t = 0; t < 40; t++) {
            int v = rnd(N), u = rnd(N);
            if (v == u || side[u] == side[v]) continue;
            if (deg[v] >= DEG_CAP || deg[u] >= DEG_CAP || amat[u][v]) continue;
            *nops = 1;
            ot[0] = 0; oa[0] = v; ob[0] = u;
            return 1;
        }
        return 0;
    }
    if (r < 60) {  /* move endpoint on side 1 */
        for (int t = 0; t < 40; t++) {
            int a = rnd(N);
            if (side[a] != 0 || deg[a] == 0) continue;
            int b = adjm[a][rnd(deg[a])];
            int c = rnd(N);
            if (side[c] != 1 || c == b || deg[c] >= DEG_CAP || amat[a][c]) continue;
            *nops = 2;
            ot[0] = 1; oa[0] = a; ob[0] = b;
            ot[1] = 0; oa[1] = a; ob[1] = c;
            return 1;
        }
        return 0;
    }
    if (r < 80) {  /* move endpoint on side 0 */
        for (int t = 0; t < 40; t++) {
            int b = rnd(N);
            if (side[b] != 1 || deg[b] == 0) continue;
            int a = adjm[b][rnd(deg[b])];
            int x = rnd(N);
            if (side[x] != 0 || x == a || deg[x] >= DEG_CAP || amat[x][b]) continue;
            *nops = 2;
            ot[0] = 1; oa[0] = a; ob[0] = b;
            ot[1] = 0; oa[1] = x; ob[1] = b;
            return 1;
        }
        return 0;
    }
    /* 2-switch: keeps all degrees */
    for (int t = 0; t < 40; t++) {
        int a = rnd(N);
        if (side[a] != 0 || deg[a] == 0) continue;
        int b = adjm[a][rnd(deg[a])];
        int c = rnd(N);
        if (side[c] != 0 || c == a || deg[c] == 0) continue;
        int e = adjm[c][rnd(deg[c])];
        if (e == b || amat[a][e] || amat[c][b]) continue;
        *nops = 4;
        ot[0] = 1; oa[0] = a; ob[0] = b;
        ot[1] = 1; oa[1] = c; ob[1] = e;
        ot[2] = 0; oa[2] = a; ob[2] = e;
        ot[3] = 0; oa[3] = c; ob[3] = b;
        return 1;
    }
    return 0;
}

static void apply_ops(int nops, const int *ot, const int *oa, const int *ob) {
    for (int i = 0; i < nops; i++) {
        if (ot[i] == 0) add_e(oa[i], ob[i]);
        else del_e(oa[i], ob[i]);
    }
}

static void undo_ops(int nops, const int *ot, const int *oa, const int *ob) {
    for (int i = nops - 1; i >= 0; i--) {
        if (ot[i] == 0) del_e(oa[i], ob[i]);
        else add_e(oa[i], ob[i]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > 64 || 2 * d > MAXN || D < 2) {
        printf("0 0\n");
        return 0;
    }
    DEG_CAP = d;
    DIAM = D;
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)seed * 0xBF58476D1CE4E5B9ULL + 0x1234567ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double tend = now() + budget;

    memset(amat, 0, sizeof amat);
    memset(deg, 0, sizeof deg);

    int n = 0, m = 0;
    int ok = 1;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN || m < 0) { ok = 0; n = 0; }
    N = n;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || amat[u][v]
            || deg[u] >= DEG_CAP || deg[v] >= DEG_CAP) {
            ok = 0;
            break;
        }
        add_e(u, v);
    }
    if (n == 0) ok = 0;
    if (ok) {
        if (!(color_graph() && cost() == 0)) ok = 0;
    }
    if (!ok) build_complete(d);
    else color_graph();

    save_best();
    long long cur = cost();
    int stall = 0;
    double T = 1.0;

    while (now() < tend) {
        if (cur == 0) {
            if (N > bestN) save_best();
            if (N >= MAXN) break;
            int v = N;
            N++;
            deg[v] = 0;
            side[v] = rnd(2);
            cur = cost();
            stall = 0;
            continue;
        }

        int nops = 0;
        int ot[4], oa[4], ob[4];
        if (!propose(&nops, ot, oa, ob)) {
            stall++;
        } else {
            apply_ops(nops, ot, oa, ob);
            long long c2 = cost();
            long long delta = c2 - cur;
            if (delta <= 0 || unif() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                undo_ops(nops, ot, oa, ob);
            }
            stall++;
        }

        if (cur == 0) continue;

        if (stall > STALL) {
            restore_best();
            T = 0.5 + 2.5 * unif();
            for (int k = 0; k < 20; k++) {
                int no = 0;
                if (propose(&no, ot, oa, ob)) apply_ops(no, ot, oa, ob);
            }
            cur = cost();
            stall = 0;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    int m2 = 0;
    for (int u = 0; u < bestN; u++)
        for (int i = 0; i < bestDeg[u]; i++)
            if (bestAdj[u][i] > u) m2++;
    printf("%d %d\n", bestN, m2);
    for (int u = 0; u < bestN; u++)
        for (int i = 0; i < bestDeg[u]; i++)
            if (bestAdj[u][i] > u) printf("%d %d\n", u, bestAdj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        deadline = t0 + 0.25 * time_limit
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealing improver in C, started from the best valid graph so far.
    if (D >= 2 and d <= 64 and 2 * d <= 1024
            and best_n < lib.moore_bound(d, D)):
        elapsed = time.monotonic() - t0
        budget = max(0.5, 0.7 * time_limit - elapsed)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=0.85 * time_limit)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
