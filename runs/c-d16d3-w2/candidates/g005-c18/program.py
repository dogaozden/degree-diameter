import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing with growth on bipartite graphs (diameter <= D).
#
# Cost = number of unordered vertex pairs at distance > D. Every move keeps
# max degree <= d and bipartiteness (each vertex has a fixed side, and every
# edge joins opposite sides). Moves are logged so they can be undone.
#   rewire : a-b  ->  a-w   (w on b's side, spare degree)
#   swap   : u-v, x-y -> u-y, x-v   (degree preserving)
#   add    : join two spare vertices on opposite sides
#   remove : delete an edge
#   grow   : new vertex joined to d opposite vertices; a full partner gives up
#            one random edge (the "stealing" growth move)
# Whenever cost is 0 the engine records the graph and grows it. It restarts
# from the best valid graph after a long stall. Output is always a valid
# graph (or "0 0"); Python re-checks everything with lib.is_valid.
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
#define DCAP 40
#define MAXE (MAXN * DCAP / 2 + 64)
#define LOGMAX 8192

typedef struct { int type, u, v; } Op;

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static Op logv[LOGMAX];
static int logn = 0, logging = 0;
static uint64_t rs = 1;
static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];
static int cand[MAXN], cand2[MAXN];
static int vis[MAXN], qbuf[MAXN];
static int cu[MAXE], cv[MAXE];
static int iu[MAXE], iv[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void raw_add(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1;
    adjm[v][u] = 1;
}

static void raw_rm1(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            deg[u]--;
            nb[u][i] = nb[u][deg[u]];
            return;
        }
    }
}

static void raw_del(int u, int v) {
    raw_rm1(u, v);
    raw_rm1(v, u);
    adjm[u][v] = 0;
    adjm[v][u] = 0;
}

static void logop(int t, int u, int v) {
    if (logn < LOGMAX) {
        logv[logn].type = t;
        logv[logn].u = u;
        logv[logn].v = v;
        logn++;
    }
}

static void add_e(int u, int v) {
    raw_add(u, v);
    if (logging) logop(0, u, v);
}

static void del_e(int u, int v) {
    raw_del(u, v);
    if (logging) logop(1, u, v);
}

static void undo_all(void) {
    for (int i = logn - 1; i >= 0; i--) {
        Op o = logv[i];
        if (o.type == 0) raw_del(o.u, o.v);
        else if (o.type == 1) raw_add(o.u, o.v);
        else n--;
    }
    logn = 0;
}

static long bad_pairs(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void color_all(void) {
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        vis[s] = 1;
        side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) {
                    vis[v] = 1;
                    side[v] = 1 - side[u];
                    qbuf[qt++] = v;
                }
            }
        }
    }
    int nc = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v && side[u] == side[v] && nc < MAXE) {
                cu[nc] = u;
                cv[nc] = v;
                nc++;
            }
        }
    }
    for (int k = 0; k < nc; k++) raw_del(cu[k], cv[k]);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (v > u && m < MAXE) {
                bestU[m] = u;
                bestV[m] = v;
                m++;
            }
        }
    }
    bestN = n;
    bestM = m;
}

static void restart_from_best(void) {
    if (bestN == 0) return;
    n = bestN;
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    memset(adjm, 0, sizeof(adjm));
    for (int i = 0; i < bestM; i++) raw_add(bestU[i], bestV[i]);
    color_all();
    logn = 0;
}

static int move_rewire(void) {
    int a = -1;
    for (int t = 0; t < 32 && a < 0; t++) {
        int c = rndi(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rndi(deg[a])];
    int k = 0;
    for (int c = 0; c < n; c++)
        if (side[c] == side[b] && c != b && deg[c] < d && !adjm[a][c]) cand[k++] = c;
    if (k == 0) return 0;
    int w = cand[rndi(k)];
    del_e(a, b);
    add_e(a, w);
    return 1;
}

static int move_swap(void) {
    int u = -1;
    for (int t = 0; t < 32 && u < 0; t++) {
        int c = rndi(n);
        if (deg[c] > 0) u = c;
    }
    if (u < 0) return 0;
    int v = nb[u][rndi(deg[u])];
    int k = 0;
    for (int c = 0; c < n; c++)
        if (c != u && side[c] == side[u] && deg[c] > 0) cand[k++] = c;
    if (k == 0) return 0;
    int x = cand[rndi(k)];
    int y = nb[x][rndi(deg[x])];
    if (y == v) return 0;
    if (adjm[u][y] || adjm[x][v]) return 0;
    del_e(u, v);
    del_e(x, y);
    add_e(u, y);
    add_e(x, v);
    return 1;
}

static int move_add(void) {
    int k = 0;
    for (int c = 0; c < n; c++)
        if (deg[c] < d) cand[k++] = c;
    if (k == 0) return 0;
    for (int t = 0; t < 12; t++) {
        int x = cand[rndi(k)];
        int m = 0;
        for (int c = 0; c < n; c++)
            if (deg[c] < d && side[c] != side[x] && !adjm[x][c]) cand2[m++] = c;
        if (m) {
            add_e(x, cand2[rndi(m)]);
            return 1;
        }
    }
    return 0;
}

static int move_remove(void) {
    int u = -1;
    for (int t = 0; t < 32 && u < 0; t++) {
        int c = rndi(n);
        if (deg[c] > 0) u = c;
    }
    if (u < 0) return 0;
    int v = nb[u][rndi(deg[u])];
    del_e(u, v);
    return 1;
}

static int move_grow(void) {
    if (n >= MAXN - 1) return 0;
    int w = n;
    int s = rndi(2);
    int k = 0;
    for (int c = 0; c < n; c++)
        if (side[c] != s) cand[k++] = c;
    int want = d < k ? d : k;
    for (int i = 0; i < want; i++) {
        int j = i + rndi(k - i);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    side[w] = s;
    deg[w] = 0;
    if (logging) logop(2, w, 0);
    n++;
    for (int i = 0; i < want; i++) {
        int p = cand[i];
        if (deg[p] >= d) {
            int q = nb[p][rndi(deg[p])];
            del_e(p, q);
        }
        add_e(w, p);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    clock_t t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0 || n0 > MAXN - 2 ||
        d < 1 || d > DCAP || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int mi = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (mi < MAXE) {
            iu[mi] = u;
            iv[mi] = v;
            mi++;
        }
    }
    n = n0;
    memset(deg, 0, sizeof(deg));
    memset(adjm, 0, sizeof(adjm));
    for (int i = 0; i < mi; i++) {
        int u = iu[i], v = iv[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || adjm[u][v]) continue;
        raw_add(u, v);
    }
    color_all();
    logging = 0;
    logn = 0;
    long cur_bad = bad_pairs();
    if (cur_bad == 0) save_best();

    long it = 0, last_imp = 0;
    const long CYC = 40000, STALL = 100000;
    const double THI = 1.2, TLO = 0.05;

    for (;;) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > budget) break;
        }
        it++;

        if (cur_bad == 0) {
            if (n > bestN) {
                save_best();
                last_imp = it;
            }
            logging = 0;
            logn = 0;
            if (!move_grow()) break;
            cur_bad = bad_pairs();
            continue;
        }

        if (bestN > 0 && it - last_imp > STALL) {
            restart_from_best();
            cur_bad = bad_pairs();
            last_imp = it;
            continue;
        }

        double ph = (double)(it % CYC) / (double)CYC;
        double T = THI * pow(TLO / THI, ph);
        logn = 0;
        logging = 1;
        int r = rndi(100), ok;
        if (r < 40) ok = move_rewire();
        else if (r < 60) ok = move_swap();
        else if (r < 80) ok = move_add();
        else ok = move_remove();
        if (!ok) {
            logging = 0;
            logn = 0;
            continue;
        }
        long nbad = bad_pairs();
        long delta = nbad - cur_bad;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            cur_bad = nbad;
            if (cur_bad == 0 && n > bestN) {
                save_best();
                last_imp = it;
            }
        } else {
            undo_all();
        }
        logging = 0;
        logn = 0;
    }

    if (cur_bad == 0 && n > bestN) save_best();

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q). Let s = d - q - 1 (spare degree per vertex). Pick
# point set SA and line set SB:
#   each line holds <= s points of SA, and each point lies on <= s lines of SB.
# Add an A-vertex per point of SA (joined to the q+1 lines through it) and a
# B-vertex per line of SB (joined to the q+1 points on it). Conics and
# hyperovals give arcs of size q+1 (q+2 for even q), which is the largest for
# s = 2. For d = 16, q = 13 this gives 2(q^2+q+1) + 2(q+1) = 394.
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
    """True if every target is hit at most s times by the elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy set with every target hit at most s times; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Return (n, edges) candidates from PG(2, q) plus arc-extension vertices, q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: best arc-extended projective plane graph as the start.
#   D == 4: generalized quadrangle W(q) as the start when available.
#   else  : K_{d,d} (diameter 2, valid for any D >= 2).
# The C engine then grows the best valid graph for most of the time budget.
# Every candidate is checked with lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    try:
        if D == 3:
            for g in _arc_extensions(d, t_start + 0.15 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    budget = end - time.monotonic()
    if budget >= 1.0 and best[0] >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 10.0)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
