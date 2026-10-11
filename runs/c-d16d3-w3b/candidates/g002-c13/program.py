import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow a valid bipartite graph by inserting one vertex at a time,
# then repair it with simulated annealing over degree-preserving moves.
# Cost = number of unordered pairs at distance > D (computed with bitsets).
# Moves: endpoint shift (keeps degrees <= d) and 2-switch (keeps degrees).
# Every accepted state with cost 0 is saved; failed growth restarts from the
# best saved graph. Output is always a graph that was checked to have cost 0.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 40
#define MAXE (MAXN * MAXDEG / 2 + 16)

static int N, DEG, DIAM;
static int side[MAXN], deg[MAXN], adjl[MAXN][MAXDEG];
static unsigned char mat[MAXN][MAXN];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static uint64_t rs;
static int best_n = 0, best_m = 0, best_side[MAXN];
static int best_e[MAXE][2];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost(void) {
    int w = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < w; k++) nxt[v][k] = cur[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = adjl[v][i];
                for (int k = 0; k < w; k++) nxt[v][k] |= cur[u][k];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc64(cur[v][k]);
        tot += N - c;
    }
    return tot / 2;
}

static void rm_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjl[a][i] == b) {
            adjl[a][i] = adjl[a][--deg[a]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    mat[a][b] = 1;
    mat[b][a] = 1;
    adjl[a][deg[a]++] = b;
    adjl[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    mat[a][b] = 0;
    mat[b][a] = 0;
    rm_half(a, b);
    rm_half(b, a);
}

static void add_vertex(int s) {
    int v = N++;
    side[v] = s;
    deg[v] = 0;
}

static int pick_nonisolated(void) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(N);
        if (deg[v] > 0) return v;
    }
    return -1;
}

static void fill_spare(void) {
    static int sl[2][MAXN];
    int cnt[2] = {0, 0};
    for (int v = 0; v < N; v++)
        if (deg[v] < DEG) sl[side[v]][cnt[side[v]]++] = v;
    for (int s = 0; s < 2; s++)
        for (int i = cnt[s] - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sl[s][i];
            sl[s][i] = sl[s][j];
            sl[s][j] = t;
        }
    for (int i = 0; i < cnt[0]; i++) {
        int a = sl[0][i];
        for (int j = 0; j < cnt[1] && deg[a] < DEG; j++) {
            int b = sl[1][j];
            if (deg[b] < DEG && !mat[a][b]) add_edge(a, b);
        }
    }
}

static void save_best(void) {
    best_n = N;
    best_m = 0;
    for (int v = 0; v < N; v++) {
        best_side[v] = side[v];
        for (int i = 0; i < deg[v]; i++) {
            int u = adjl[v][i];
            if (u > v) {
                best_e[best_m][0] = v;
                best_e[best_m][1] = u;
                best_m++;
            }
        }
    }
}

static void restore_best(void) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) mat[v][adjl[v][i]] = 0;
        deg[v] = 0;
    }
    N = best_n;
    for (int v = 0; v < N; v++) side[v] = best_side[v];
    for (int e = 0; e < best_m; e++) add_edge(best_e[e][0], best_e[e][1]);
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n < 2 || n > MAXN / 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || mat[u][v]) { ok = 0; break; }
        if (deg[u] >= DEG || deg[v] >= DEG) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    /* bipartition by BFS */
    for (int v = 0; v < N; v++) side[v] = -1;
    static int queue[MAXN];
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int v = queue[qh++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adjl[v][i];
                if (side[u] == -1) {
                    side[u] = 1 - side[v];
                    queue[qt++] = u;
                } else if (side[u] == side[v]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    double t0 = now_sec();
    while (now_sec() - t0 < budget && N < MAXN - 2) {
        add_vertex(rndint(2));
        fill_spare();
        long long c = cost();
        int cap = 6000 + 40 * N;
        for (int it = 0; it < cap && c != 0; it++) {
            if ((it & 127) == 0 && now_sec() - t0 >= budget) break;
            double T = 1.5 * pow(0.03 / 1.5, (double)it / (double)cap);
            if (rndint(2) == 0) {
                int v = pick_nonisolated();
                if (v < 0) continue;
                int u = adjl[v][rndint(deg[v])];
                int x = -1;
                for (int t = 0; t < 40; t++) {
                    int y = rndint(N);
                    if (side[y] == side[u] && y != u && deg[y] < DEG && !mat[v][y]) {
                        x = y;
                        break;
                    }
                }
                if (x < 0) continue;
                del_edge(v, u);
                add_edge(v, x);
                long long c2 = cost();
                if (accept(c2 - c, T)) c = c2;
                else {
                    del_edge(v, x);
                    add_edge(v, u);
                }
            } else {
                int a1 = pick_nonisolated();
                if (a1 < 0) continue;
                int b1 = adjl[a1][rndint(deg[a1])];
                int a2 = -1;
                for (int t = 0; t < 40; t++) {
                    int y = rndint(N);
                    if (y != a1 && side[y] == side[a1] && deg[y] > 0) {
                        a2 = y;
                        break;
                    }
                }
                if (a2 < 0) continue;
                int b2 = adjl[a2][rndint(deg[a2])];
                if (b1 == b2 || mat[a1][b2] || mat[a2][b1]) continue;
                del_edge(a1, b1);
                del_edge(a2, b2);
                add_edge(a1, b2);
                add_edge(a2, b1);
                long long c2 = cost();
                if (accept(c2 - c, T)) c = c2;
                else {
                    del_edge(a1, b2);
                    del_edge(a2, b1);
                    add_edge(a1, b1);
                    add_edge(a2, b2);
                }
            }
        }
        if (c == 0) save_best();
        else restore_best();
    }

    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", best_e[e][0], best_e[e][1]);
    return 0;
}
"""

_LS_ITERS = 12000


# ----------------------------------------------------------------------------
# Arc-extended projective plane candidates (Python start-graph generator).
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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy capacitated set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set found by greedy, supplied seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus A-vertices and B-vertices."""
    Rset = set(R)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs_ = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs_[trial] if trial < len(rs_) else rng.choice(rs_)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


# ----------------------------------------------------------------------------
# Build: arc candidates as a start, then C growth/annealing from the best one.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3 and d >= 3:
        try:
            rng = random.Random(seed * 7919 + d)
            cands = _arc_extensions(d, t0 + 0.3 * time_limit, rng)
            for n_c, e_c in cands:  # sorted largest first
                if n_c > best[0]:
                    consider(n_c, e_c)
        except Exception:
            pass

    if best[0] >= lib.moore_bound(d, D) or d > 40 or d < 2:
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    elapsed = time.monotonic() - t0
    remaining = 0.85 * time_limit - elapsed
    if remaining > 1.0:
        try:
            timeout = max(1.0, 0.93 * time_limit - elapsed)
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=timeout)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
