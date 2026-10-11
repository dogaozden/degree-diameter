import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
# An A-vertex for point P is a twin of P (joined to the lines through P); each
# line can take at most s such twins. B-vertices are the dual construction.
# The two sides are independent, so SA and SB are optimized separately.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
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
            if len(cur) >= s:
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# C growth engine: bitset-based annealed repair.
#
# Starting from a valid bipartite graph, the engine adds one vertex (or a pair,
# one per side) and anneals over 2-switches, endpoint shifts and greedy fills to
# drive the number of vertex pairs at distance > D to zero. Distances are
# computed with 64-bit bitsets, so one full evaluation costs about D*m*n/64 word
# operations. On failure it returns the last valid graph it saved.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1536
#define MAXW 24
#define MAXD 64
#define MAXE (MAXN * MAXD / 2 + 64)

static int d_, D_;
static int n_, m_;
static int col[MAXN];
static int deg[MAXN];
static int ex[MAXE], ey[MAXE];          /* ex: colour-0 endpoint, ey: colour-1 endpoint */
static unsigned char adjm[MAXN][MAXN];
static int adjl[MAXN][MAXD];
static int adjd[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static uint64_t rs;
static int bn_, bm_;
static int bex[MAXE], bey[MAXE];

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > D_ (unreachable counts as bad). */
static int eval_cost(void) {
    int n = n_, W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) adjd[v] = 0;
    for (int e = 0; e < m_; e++) {
        int x = ex[e], y = ey[e];
        adjl[x][adjd[x]++] = y;
        adjl[y][adjd[y]++] = x;
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < adjd[v]; k++) {
                int u = adjl[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

/* Rebuild deg and adjacency matrix from the edge list. */
static void rebuild(void) {
    memset(adjm, 0, sizeof(adjm));
    for (int v = 0; v < n_; v++) deg[v] = 0;
    for (int e = 0; e < m_; e++) {
        deg[ex[e]]++;
        deg[ey[e]]++;
        adjm[ex[e]][ey[e]] = 1;
        adjm[ey[e]][ex[e]] = 1;
    }
}

/* Add an edge between a random non-adjacent pair of deficient vertices of opposite colour. */
static int try_fill(void) {
    if (m_ >= MAXE) return 0;
    int dx[MAXN], dy[MAXN], nx = 0, ny = 0;
    for (int v = 0; v < n_; v++) {
        if (deg[v] < d_) {
            if (col[v] == 0) dx[nx++] = v;
            else dy[ny++] = v;
        }
    }
    if (nx == 0 || ny == 0) return 0;
    for (int t = 0; t < 40; t++) {
        int x = dx[rndi(nx)], y = dy[rndi(ny)];
        if (!adjm[x][y]) {
            ex[m_] = x;
            ey[m_] = y;
            m_++;
            deg[x]++;
            deg[y]++;
            adjm[x][y] = 1;
            adjm[y][x] = 1;
            return 1;
        }
    }
    return 0;
}

/* Simulated annealing until cost 0 (returns 1) or deadline (returns 0). */
static int anneal(double deadline) {
    int cost = eval_cost();
    if (cost == 0) return 1;
    for (long it = 0;; it++) {
        if ((it & 31) == 0 && now_s() > deadline) return 0;
        if (try_fill()) {
            cost = eval_cost();
            if (cost == 0) return 1;
            continue;
        }
        if (m_ < 2) continue;
        long ph = it % 40000;
        double T = 3.0 * pow(0.03 / 3.0, (double)ph / 40000.0);
        int r = rndi(100);
        if (r < 50) {
            /* degree-preserving 2-switch */
            int i = rndi(m_), j = rndi(m_);
            if (i == j) continue;
            int x1 = ex[i], y1 = ey[i], x2 = ex[j], y2 = ey[j];
            if (x1 == x2 || y1 == y2) continue;
            if (adjm[x1][y2] || adjm[x2][y1]) continue;
            ey[i] = y2;
            ey[j] = y1;
            adjm[x1][y1] = 0; adjm[y1][x1] = 0;
            adjm[x2][y2] = 0; adjm[y2][x2] = 0;
            adjm[x1][y2] = 1; adjm[y2][x1] = 1;
            adjm[x2][y1] = 1; adjm[y1][x2] = 1;
            int nc = eval_cost();
            int delta = nc - cost;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                ey[i] = y1;
                ey[j] = y2;
                adjm[x1][y2] = 0; adjm[y2][x1] = 0;
                adjm[x2][y1] = 0; adjm[y1][x2] = 0;
                adjm[x1][y1] = 1; adjm[y1][x1] = 1;
                adjm[x2][y2] = 1; adjm[y2][x2] = 1;
            }
        } else {
            /* move one endpoint of an edge to another deficient vertex of the same colour */
            int i = rndi(m_);
            int a = ex[i], b = ey[i];
            int side = rndi(2);
            int keep = side ? b : a;
            int old = side ? a : b;
            int colr = side ? 0 : 1;
            int nv = -1;
            for (int t = 0; t < 40; t++) {
                int v = rndi(n_);
                if (v != old && col[v] == colr && deg[v] < d_ && !adjm[keep][v]) {
                    nv = v;
                    break;
                }
            }
            if (nv < 0) continue;
            if (side) ex[i] = nv;
            else ey[i] = nv;
            deg[old]--;
            deg[nv]++;
            adjm[keep][old] = 0; adjm[old][keep] = 0;
            adjm[keep][nv] = 1; adjm[nv][keep] = 1;
            int nc = eval_cost();
            int delta = nc - cost;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                if (side) ex[i] = old;
                else ey[i] = old;
                deg[old]++;
                deg[nv]--;
                adjm[keep][nv] = 0; adjm[nv][keep] = 0;
                adjm[keep][old] = 1; adjm[old][keep] = 1;
            }
        }
        if (cost == 0) return 1;
    }
}

static void add_vertex(int c) {
    col[n_] = c;
    deg[n_] = 0;
    n_++;
}

static void save_best(void) {
    bn_ = n_;
    bm_ = m_;
    memcpy(bex, ex, sizeof(int) * (size_t)m_);
    memcpy(bey, ey, sizeof(int) * (size_t)m_);
}

static void restore_best(void) {
    n_ = bn_;
    m_ = bm_;
    memcpy(ex, bex, sizeof(int) * (size_t)m_);
    memcpy(ey, bey, sizeof(int) * (size_t)m_);
    rebuild();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double t_end = now_s() + budget;
    bn_ = 0;
    bm_ = 0;
    if (d_ < 1 || d_ > MAXD - 2 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }

    static int rx[MAXE], ry[MAXE];
    static int dg[MAXN], q[MAXN];
    int n0 = 0, m0 = 0, bad = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || n0 > MAXN || m0 < 0 || m0 > MAXE) bad = 1;
    for (int e = 0; !bad && e < m0; e++) {
        if (scanf("%d %d", &rx[e], &ry[e]) != 2) bad = 1;
        else if (rx[e] < 0 || rx[e] >= n0 || ry[e] < 0 || ry[e] >= n0 || rx[e] == ry[e]) bad = 1;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    if (n0 == 0) {
        n_ = 2 * d_;
        m_ = 0;
        for (int v = 0; v < n_; v++) col[v] = (v < d_) ? 0 : 1;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++) {
                ex[m_] = i;
                ey[m_] = d_ + j;
                m_++;
            }
    } else {
        for (int v = 0; v < n0; v++) {
            dg[v] = 0;
            adjd[v] = 0;
            col[v] = -1;
        }
        for (int e = 0; e < m0; e++) {
            dg[rx[e]]++;
            dg[ry[e]]++;
        }
        for (int v = 0; v < n0; v++)
            if (dg[v] > d_) bad = 1;
        if (bad) {
            printf("0 0\n");
            return 0;
        }
        for (int e = 0; e < m0; e++) {
            adjl[rx[e]][adjd[rx[e]]++] = ry[e];
            adjl[ry[e]][adjd[ry[e]]++] = rx[e];
        }
        int conflict = 0;
        for (int s = 0; s < n0 && !conflict; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && !conflict) {
                int u = q[qh++];
                for (int k = 0; k < adjd[u]; k++) {
                    int w = adjl[u][k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        q[qt++] = w;
                    } else if (col[w] == col[u]) {
                        conflict = 1;
                        break;
                    }
                }
            }
        }
        if (conflict) {
            printf("0 0\n");
            return 0;
        }
        n_ = n0;
        m_ = 0;
        for (int e = 0; e < m0; e++) {
            if (col[rx[e]] == 0) {
                ex[m_] = rx[e];
                ey[m_] = ry[e];
            } else {
                ex[m_] = ry[e];
                ey[m_] = rx[e];
            }
            m_++;
        }
    }

    rebuild();
    if (eval_cost() == 0) save_best();
    else if (anneal(now_s() + 0.2 * budget)) save_best();

    if (bn_ > 0) {
        for (;;) {
            double rem = t_end - now_s();
            if (rem < 0.05 || n_ + 1 > MAXN) break;
            int c0 = 0, c1 = 0;
            for (int v = 0; v < n_; v++) {
                if (col[v] == 0) c0++;
                else c1++;
            }
            add_vertex(c0 <= c1 ? 0 : 1);
            if (anneal(now_s() + 0.4 * rem)) {
                save_best();
                continue;
            }
            restore_best();

            rem = t_end - now_s();
            if (rem < 0.05 || n_ + 2 > MAXN) break;
            add_vertex(0);
            add_vertex(1);
            if (anneal(now_s() + 0.6 * rem)) {
                save_best();
                continue;
            }
            restore_best();
            break;
        }
    }

    printf("%d %d\n", bn_, bm_);
    for (int e = 0; e < bm_; e++) printf("%d %d\n", bex[e], bey[e]);
    return 0;
}
'''


def _grow_with_c(d, D, start, seed, budget, timeout):
    """Run the C growth engine from `start`; return (n, edges) or None on any failure."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=start, timeout=timeout)
        return lib.parse_graph_text(out)
    except Exception:
        return None


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

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.25 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return instantly.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Grow the best start with the C repair-annealing engine.
    remaining = 0.9 * time_limit - (time.monotonic() - t0)
    budget = remaining - 2.5
    if budget >= 1.0:
        res = _grow_with_c(d, D, best, seed, budget, timeout=remaining + 3.0)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
