import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (diameter D).
#
# Let R = D-1. A new vertex w joined to a set N of opposite-colour vertices is
# within distance D of every old vertex x that lies in the R-ball of some u in N.
# Adding vertices and cross edges never increases old distances, so validity is
# preserved. Each round:
#   1. compute R-balls as bitsets,
#   2. for each colour class, greedily cover all vertices with spare-degree
#      neighbours (randomized tie-breaks) and insert a vertex on success,
#   3. on failure add a random spare cross edge to change the spare pattern.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 400;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (NEW): capacitated set packing by tabu search.
#
# Problem: elements x = 0..m-1, each hitting a list of targets. Choose a
# maximum set S of elements so that every target is hit by at most CAP chosen
# elements. For PG(2,q) this is exactly the arc-extension problem: choose
# points so that each line carries at most s of them (or lines so that each
# point does).
#
# Move: pick the outside element x whose insertion needs the fewest removals
# (each saturated target of x must lose one chosen element that hits it).
# Removed elements become tabu for re-adding; freshly added elements are
# protected from immediate removal. Aspiration allows tabu moves that beat the
# best size. After STALL idle moves, restore the best set and kick it with
# random forced insertions.
#
# Input: lib.graph format with n = m + T vertices; edges (x, m + t) join
# element x to target t. Arguments: seed budget cap m.
# Output: size line, then the chosen element indices on one line.
# ----------------------------------------------------------------------------

C_PACK = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXE 1024
#define MAXK 64
#define MAXT 1024
#define MAXCAP 64
#define MAXRM 4
#define STALL 3000

static int m, T, cap;
static int kk[MAXE];
static int nb[MAXE][MAXK];
static int inS[MAXE];
static int bestS[MAXE];
static int load[MAXT];
static int hcnt[MAXT];
static int hl[MAXT][MAXCAP];
static long long tabu[MAXE];
static long long addtabu[MAXE];
static long long mark[MAXT];
static long long stampc = 0;
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static void rebuild(void) {
    for (int t = 0; t < T; t++) load[t] = 0;
    for (int x = 0; x < m; x++)
        if (inS[x])
            for (int j = 0; j < kk[x]; j++) load[nb[x][j]]++;
}

static void build_hits(void) {
    for (int t = 0; t < T; t++) hcnt[t] = 0;
    for (int y = 0; y < m; y++)
        if (inS[y])
            for (int j = 0; j < kk[y]; j++) {
                int t = nb[y][j];
                if (hcnt[t] < MAXCAP) hl[t][hcnt[t]++] = y;
            }
}

/* Removals needed so that x can be added; -1 if more than MAXRM. */
static int compute_rem(int x, long long now, int *remv) {
    int nrem = 0;
    stampc++;
    for (int j = 0; j < kk[x]; j++) {
        int t = nb[x][j];
        if (load[t] < cap || mark[t] == stampc) continue;
        if (nrem >= MAXRM) return -1;
        int y = hl[t][rnd() % (uint32_t)cap];
        for (int tr = 0; tr < 3 && addtabu[y] > now; tr++)
            y = hl[t][rnd() % (uint32_t)cap];
        remv[nrem++] = y;
        for (int q2 = 0; q2 < kk[y]; q2++) mark[nb[y][q2]] = stampc;
    }
    return nrem;
}

static void apply_move(int x, int nrem, const int *remv, long long now) {
    for (int i = 0; i < nrem; i++) {
        int y = remv[i];
        inS[y] = 0;
        for (int j = 0; j < kk[y]; j++) load[nb[y][j]]--;
        tabu[y] = now + 5 + (long long)(rnd() % 8u);
    }
    inS[x] = 1;
    for (int j = 0; j < kk[x]; j++) load[nb[x][j]]++;
    addtabu[x] = now + 2 + (long long)(rnd() % 4u);
}

static void greedy_init(void) {
    static int order[MAXE];
    for (int i = 0; i < m; i++) order[i] = i;
    for (int i = m - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int tmp = order[i]; order[i] = order[j]; order[j] = tmp;
    }
    for (int x = 0; x < m; x++) inS[x] = 0;
    for (int t = 0; t < T; t++) load[t] = 0;
    for (int i = 0; i < m; i++) {
        int x = order[i], ok = 1;
        for (int j = 0; j < kk[x]; j++)
            if (load[nb[x][j]] >= cap) { ok = 0; break; }
        if (ok) {
            inS[x] = 1;
            for (int j = 0; j < kk[x]; j++) load[nb[x][j]]++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0\n\n"); return 0; }
    unsigned long seed = strtoul(argv[1], NULL, 10);
    double budget = atof(argv[2]);
    cap = atoi(argv[3]);
    int melem = atoi(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int N, M;
    if (scanf("%d %d", &N, &M) != 2) { printf("0\n\n"); return 0; }
    if (cap < 1 || cap > MAXCAP || melem < 1 || melem > N ||
        melem > MAXE || N - melem > MAXT || N - melem < 1) {
        printf("0\n\n");
        return 0;
    }
    m = melem;
    T = N - melem;
    for (int i = 0; i < M; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a >= m) { int tmp = a; a = b; b = tmp; }
        if (a < 0 || a >= m || b < m || b >= N) continue;
        if (kk[a] >= MAXK) continue;
        nb[a][kk[a]++] = b - m;
    }

    greedy_init();
    int size = 0;
    for (int x = 0; x < m; x++) size += inS[x];
    int bestsize = size;
    memcpy(bestS, inS, sizeof(int) * m);

    clock_t t0 = clock();
    long long it = 0, lastimp = 0;
    int remv[MAXRM], brem[MAXRM];

    while (1) {
        if ((it & 127) == 0 &&
            (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        build_hits();

        int bx = -1, bn = 1 << 30, nties = 0, bnrem = 0;
        for (int x = 0; x < m; x++) {
            if (inS[x]) continue;
            int nr = compute_rem(x, it, remv);
            if (nr < 0) continue;
            if (tabu[x] > it && size + 1 - nr <= bestsize) continue;
            if (nr < bn) {
                bn = nr; bnrem = nr; bx = x; nties = 1;
                for (int i = 0; i < nr; i++) brem[i] = remv[i];
            } else if (nr == bn) {
                nties++;
                if (rnd() % (uint32_t)nties == 0) {
                    bx = x; bnrem = nr;
                    for (int i = 0; i < nr; i++) brem[i] = remv[i];
                }
            }
        }

        if (bx >= 0) {
            apply_move(bx, bnrem, brem, it);
            size += 1 - bnrem;
            if (size > bestsize) {
                bestsize = size;
                memcpy(bestS, inS, sizeof(int) * m);
                lastimp = it;
            }
        }

        if (it - lastimp > STALL) {
            memcpy(inS, bestS, sizeof(int) * m);
            rebuild();
            size = bestsize;
            for (int r = 0; r < 3; r++) {
                build_hits();
                int x = (int)(rnd() % (uint32_t)m);
                if (inS[x]) continue;
                int nr = compute_rem(x, it, remv);
                if (nr < 0) continue;
                apply_move(x, nr, remv, it);
                size += 1 - nr;
            }
            lastimp = it;
        }
    }

    int cnt = 0;
    for (int x = 0; x < m; x++) cnt += bestS[x];
    printf("%d\n", cnt);
    int first = 1;
    for (int x = 0; x < m; x++)
        if (bestS[x]) {
            printf("%s%d", first ? "" : " ", x);
            first = 0;
        }
    printf("\n");
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


def _pack_side(lists, T, cap, seed, budget):
    """Max set of elements such that each of T targets is hit by <= cap chosen elements.

    lists[x] gives the targets of element x. Returns the chosen element list, or None.
    """
    mm = len(lists)
    if mm == 0 or T == 0:
        return []
    if cap < 1:
        return []
    edges = [(x, mm + t) for x, ts in enumerate(lists) for t in ts]
    try:
        out = lib.run_c(C_PACK, [seed, round(budget, 2), cap, mm],
                        stdin_graph=(mm + T, edges), timeout=budget + 8.0)
        nums = out.split()
        k = int(nums[0])
        S = sorted({int(v) for v in nums[1:1 + k]})
    except Exception:
        return None
    load = [0] * T
    for x in S:
        if not 0 <= x < mm:
            return None
        for t in lists[x]:
            load[t] += 1
    if max(load, default=0) > cap:
        return None
    return S


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to the
#         q+1 lines through P. Each line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to the q+1
#         points on j. Each point lies on <= s lines of SB.
#
# Diameter stays 3 for any SA, SB. The two sides are independent packing
# problems, each solved by the C tabu engine above.
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


def _arc_qs(d):
    """Prime powers q with q + 1 <= d, keeping the two with the largest order bound."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    return qs[:2]


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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
# Driver.
#   D = 3: greedy arc seeds for PG(2,q), then tabu capacitated packing for each
#          side (A and B) of the top two planes, alternating, until 0.45 of
#          time_limit; then C insertion on the best graph until 0.85.
#   D >= 4: GQ baseline, then annealed group voltage lifts until 0.70, then
#          C insertion until 0.88.
#   If the Moore bound is already reached, return immediately.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def at_bound():
        return best_n >= lib.moore_bound(d, D)

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3 and not at_bound():
        qs = _arc_qs(d)
        pg = {}
        sets = {}
        for q in qs:
            m_, edges, pl, lp, index, pts = _pg_data(q)
            pg[q] = (m_, edges, pl, lp)
            s = d - q - 1
            if s < 1:
                sets[q] = [[], []]
                continue
            SA = _greedy_side(m_, s, pl, rng, 40, start + 0.10 * time_limit)
            SB = _greedy_side(m_, s, lp, rng, 40, start + 0.10 * time_limit)
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if len(cs) > len(SA) and _loads_ok(cs, s, m_, pl):
                    SA = cs
                if len(cs) > len(SB) and _loads_ok(cs, s, m_, lp):
                    SB = cs
            sets[q] = [SA, SB]

        # Packing rounds: each job is one (plane, side) call; the remaining
        # time is split evenly over the remaining jobs.
        jobs = [(q, side) for _ in range(2) for q in qs
                for side in (0, 1) if d - q - 1 >= 1]
        pack_end = start + 0.45 * time_limit
        for j, (q, side) in enumerate(jobs):
            left = len(jobs) - j
            budget = (pack_end - time.monotonic()) / left
            if budget < 0.5:
                break
            m_, edges, pl, lp = pg[q]
            s = d - q - 1
            lists = pl if side == 0 else lp
            S = _pack_side(lists, m_, s, seed * 31 + j + 1, budget)
            if S is not None and len(S) > len(sets[q][side]):
                sets[q][side] = S

        for q in qs:
            m_, edges, pl, lp = pg[q]
            SA, SB = sets[q]
            s = d - q - 1
            if not (_loads_ok(SA, s, m_, pl) and _loads_ok(SB, s, m_, lp)):
                continue
            consider(_arc_graph(m_, edges, pl, lp, SA, SB))

        if not at_bound():
            budget = 0.85 * time_limit - el()
            if budget >= 0.5:
                consider(_c_augment(best, d, D, seed, budget))

    if D >= 4 and el() < 0.50 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D >= 4:
        anneal_end = start + 0.70 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

        if not at_bound():
            rem = 0.88 * time_limit - el()
            if rem >= 0.5:
                consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
