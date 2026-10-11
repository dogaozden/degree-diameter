import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: maximum packing by iterated local search (NEW this round).
#
# Input (through lib.run_c's edge-list channel, flattened into pairs):
#   nc nt cap, then for each candidate: k t_1 ... t_k.
# Goal: choose the most candidates such that every target is hit at most `cap`
# times. For the arc-extension this is: pick points (or lines) whose incidence
# with the opposite class never exceeds the spare degree.
# Moves: greedy fill; pick an unselected candidate x, evict one selected
# candidate per saturated target of x, insert x. Accept plateau/improving moves
# always and worsening moves rarely. Keeps the best packing seen.
# ----------------------------------------------------------------------------

PACK_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXC 4096
#define MAXT 4096
#define MAXK 64

static uint64_t rs = 88172645463325252ULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }

static int nc, nt, cap;
static int kc[MAXC];
static int tg[MAXC][MAXK];
static int kt[MAXT];
static int *tc[MAXT];
static int sel[MAXC], load[MAXT], cnt;
static int bsel[MAXC], bcnt;
static int ord[MAXC];
static int ssel[MAXC], sload[MAXT];

static int fits(int x) {
    for (int i = 0; i < kc[x]; i++) if (load[tg[x][i]] >= cap) return 0;
    return 1;
}
static void addc(int x) {
    sel[x] = 1; cnt++;
    for (int i = 0; i < kc[x]; i++) load[tg[x][i]]++;
}
static void remc(int x) {
    sel[x] = 0; cnt--;
    for (int i = 0; i < kc[x]; i++) load[tg[x][i]]--;
}
static void fill(void) {
    for (int i = 0; i < nc; i++) ord[i] = i;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
    }
    for (int i = 0; i < nc; i++) {
        int x = ord[i];
        if (!sel[x] && fits(x)) addc(x);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) return 1;
    unsigned long seed = strtoul(argv[1], NULL, 10);
    double budget = atof(argv[2]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int N, M;
    if (scanf("%d %d", &N, &M) != 2 || M < 0) { printf("0\n\n"); return 0; }
    long tokn = 2L * M;
    int *st = (int *)malloc(sizeof(int) * (size_t)(tokn + 3));
    long ns = 0;
    for (long i = 0; i < tokn; i++) {
        int v;
        if (scanf("%d", &v) != 1) break;
        st[ns++] = v;
    }
    if (ns < 3) { printf("0\n\n"); free(st); return 0; }
    nc = st[0]; nt = st[1]; cap = st[2];
    if (nc < 0 || nc > MAXC || nt < 0 || nt > MAXT || cap < 0) { printf("0\n\n"); free(st); return 0; }

    long p = 3;
    int ok = 1;
    for (int i = 0; i < nc && ok; i++) {
        if (p >= ns) { ok = 0; break; }
        int k = st[p++];
        if (k < 0 || k > MAXK || p + k > ns) { ok = 0; break; }
        kc[i] = 0;
        for (int j = 0; j < k; j++) {
            int t = st[p++];
            if (t < 0 || t >= nt) { ok = 0; break; }
            int dup = 0;
            for (int q = 0; q < kc[i]; q++) if (tg[i][q] == t) dup = 1;
            if (!dup) tg[i][kc[i]++] = t;
        }
    }
    free(st);
    if (!ok || nc == 0) { printf("0\n\n"); return 0; }

    for (int t = 0; t < nt; t++) kt[t] = 0;
    for (int i = 0; i < nc; i++) for (int j = 0; j < kc[i]; j++) kt[tg[i][j]]++;
    for (int t = 0; t < nt; t++) {
        tc[t] = (int *)malloc(sizeof(int) * (size_t)(kt[t] + 1));
        kt[t] = 0;
    }
    for (int i = 0; i < nc; i++)
        for (int j = 0; j < kc[i]; j++) {
            int t = tg[i][j];
            tc[t][kt[t]++] = i;
        }

    for (int i = 0; i < nc; i++) sel[i] = 0;
    for (int t = 0; t < nt; t++) load[t] = 0;
    cnt = 0;
    fill();
    bcnt = cnt;
    memcpy(bsel, sel, sizeof(int) * nc);

    clock_t t0 = clock();
    long it = 0;
    while (1) {
        if ((it & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        if (cnt > bcnt) { bcnt = cnt; memcpy(bsel, sel, sizeof(int) * nc); }
        if (cnt == nc) break;

        int x = -1;
        for (int tr = 0; tr < 40 && x < 0; tr++) {
            int y = (int)(rnd() % (uint32_t)nc);
            if (!sel[y]) x = y;
        }
        if (x < 0) for (int y = 0; y < nc; y++) if (!sel[y]) { x = y; break; }
        if (x < 0) break;

        if (fits(x)) { addc(x); continue; }

        memcpy(ssel, sel, sizeof(int) * nc);
        memcpy(sload, load, sizeof(int) * nt);
        int cs = cnt, removed = 0;
        for (int i = 0; i < kc[x]; i++) {
            int t = tg[x][i];
            if (load[t] < cap) continue;
            int m = kt[t];
            int s0 = (int)(rnd() % (uint32_t)m);
            int y = -1;
            for (int j = 0; j < m; j++) {
                int c = tc[t][(s0 + j) % m];
                if (sel[c]) { y = c; break; }
            }
            if (y < 0) continue;
            remc(y);
            removed++;
        }
        int accept = 0;
        if (fits(x)) {
            addc(x);
            accept = (removed <= 1) || (rnd() % 100u < 2u);
        }
        if (accept) {
            fill();
        } else {
            memcpy(sel, ssel, sizeof(int) * nc);
            memcpy(load, sload, sizeof(int) * nt);
            cnt = cs;
        }
    }

    printf("%d\n", bcnt);
    for (int i = 0; i < nc; i++) if (bsel[i]) printf("%d ", i);
    printf("\n");
    for (int t = 0; t < nt; t++) free(tc[t]);
    return 0;
}
"""


def _pack(sets, nt, cap, seed, budget):
    """Choose indices of `sets` (lists of targets in range(nt)) so each target is hit <= cap times.

    Returns a list of chosen indices, or None if the C run fails.
    """
    if not sets or budget < 0.2:
        return None
    stream = [len(sets), nt, cap]
    for s in sets:
        stream.append(len(s))
        stream.extend(s)
    if len(stream) % 2:
        stream.append(0)
    pairs = [(stream[i], stream[i + 1]) for i in range(0, len(stream), 2)]
    try:
        out = lib.run_c(PACK_SOURCE, [seed, round(budget, 2)],
                        stdin_graph=(0, pairs), timeout=budget + 5.0)
        toks = out.split()
        c = int(toks[0])
        idx = [int(t) for t in toks[1:1 + c]]
    except Exception:
        return None
    if len(set(idx)) != len(idx) or any(not (0 <= i < len(sets)) for i in idx):
        return None
    return idx


# ----------------------------------------------------------------------------
# C engine 2: greedy vertex insertion with ball-cover certificates (parent).
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
    int cand[MAXN];
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
    const int maxfails = 200;
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


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1.
#
# A-side: a set SA of points; each P in SA gets a new vertex joined to the q+1
# lines through P. Every line may hold at most s points of SA.
# B-side: a set SB of lines; each j in SB gets a new vertex joined to the q+1
# points on j. Every point may lie on at most s lines of SB.
# Any such choice keeps diameter 3, so the only constraint is the packing one,
# which is solved by the C packer above (with greedy and conic fallbacks).
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


def _solve_side(sets, m, s, rng, seed, budget, deadline):
    """Best packing for one side: the C packer, improved over greedy when possible."""
    best = _greedy_side(m, s, sets, rng, 20, deadline)
    budget_t = min(budget, max(0.2, deadline - time.monotonic()))
    idx = _pack(sets, m, s, seed, budget_t)
    if idx is not None and len(idx) > len(best) and _loads_ok(idx, s, m, sets):
        best = idx
    return best


def _arc_candidates(d, deadline, seed, per_call, floor_n):
    """Return arc-extended graphs (n, edges) for prime powers q with q + 1 <= d, largest q first."""
    out = []
    best_n = floor_n
    rng = random.Random(seed * 7919 + d)
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for q in qs:
        s = d - q - 1
        if s < 1:
            continue
        if time.monotonic() > deadline:
            break
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        ub = min(m, m * s // (q + 1))
        if 2 * m + 2 * ub <= best_n:
            continue  # cannot beat what we already have
        SA = _solve_side(point_lines, m, s, rng, seed + 1, per_call, deadline)
        SB = _solve_side(line_points, m, s, rng, seed + 2, per_call, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        g = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append(g)
        best_n = max(best_n, g[0])
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
            nx = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nx.append(v)
            count += len(nx)
            frontier = nx
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
# Driver. Time plan (fractions of time_limit):
#   D = 3: 0.00-0.45 packed arc extensions (largest q first),
#          0.45-0.86 C greedy insertion on the best graph so far.
#   D >= 4: 0.00-0.25 packed arc extensions (diameter 3 is also valid for D >= 4),
#           0.25-0.40 generalized quadrangle baseline,
#           0.40-0.70 annealed group voltage lifts,
#           0.70-0.86 C greedy insertion on the best graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        deadline = start + (0.45 if D == 3 else 0.25) * T
        for g in _arc_candidates(d, deadline, seed, 0.12 * T, best_n):
            consider(g)

    if D == 3:
        rem = 0.86 * T - elapsed()
        if rem > 0.5:
            consider(_c_augment(best, d, D, seed, rem))
    else:
        if elapsed() < 0.40 * T:
            consider(_best_gq(d))

        anneal_end = start + 0.70 * T
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

        rem = 0.86 * T - elapsed()
        if rem > 0.5:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
