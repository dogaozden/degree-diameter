import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine.
#
# Two modes share one binary:
#  * default: simulated annealing on bipartite graphs with a fixed vertex set.
#    Cost = number of unordered pairs at distance > D. Whenever the cost hits 0
#    it saves the graph and appends one isolated vertex.
#  * "arc" (new): load-constrained packing by annealing. Input is a point-line
#    incidence graph of PG(2,q) (points 0..m-1, lines m..2m-1). Each point P has
#    spare capacity s = d - (q+1). Choose a set S of points so every line holds
#    at most s points of S and every point lies on at most s lines indexed by S
#    (line index P of the same point P). Then add A_P (joined to lines through P)
#    and B_P (joined to points on line P) for P in S. Diameter 3 holds for ANY
#    feasible S, so only degree constraints matter. The mode maximises |S| with a
#    penalised objective |S| - lam * overflow, using toggle and swap moves, and
#    prints the extended graph.
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
#define AMAXM 1200
#define AQD 64

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

static int tmpbadv[MAXN], ntmp = 0;
static int curbadv[MAXN], ncurbadv = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* ---------------- arc mode: load-constrained packing ---------------- */

static int a_m, a_s, a_over, a_size;
static int a_pl[AMAXM][AQD], a_npl[AMAXM];   /* lines through point P */
static int a_lp[AMAXM][AQD], a_npt[AMAXM];   /* points on line L */
static int a_lload[AMAXM], a_pload[AMAXM];
static int a_in[AMAXM], a_best_in[AMAXM];

/* Apply +1 (sg=1) or -1 (sg=-1) for candidate P, updating the overflow count. */
static void a_touch(int P, int sg) {
    int k1 = a_npl[P];
    for (int i = 0; i < k1; i++) {
        int L = a_pl[P][i];
        int old = a_lload[L];
        a_lload[L] = old + sg;
        if (sg > 0) { if (old + 1 > a_s) a_over++; }
        else if (old > a_s) a_over--;
    }
    int k2 = a_npt[P];
    for (int i = 0; i < k2; i++) {
        int Q = a_lp[P][i];
        int old = a_pload[Q];
        a_pload[Q] = old + sg;
        if (sg > 0) { if (old + 1 > a_s) a_over++; }
        else if (old > a_s) a_over--;
    }
}
static void a_add(int P) { a_in[P] = 1; a_size++; a_touch(P, 1); }
static void a_del(int P) { a_in[P] = 0; a_size--; a_touch(P, -1); }

static void print_input(int nn, const int *iu, const int *iv, int me) {
    printf("%d %d\n", nn, me);
    for (int i = 0; i < me; i++) printf("%d %d\n", iu[i], iv[i]);
}

static void arc_mode(int dd, int nn, const int *iu, const int *iv, int me, double tl, clock_t t0) {
    static int degc[2 * AMAXM];
    int mm = nn / 2;
    int ok = (nn >= 2 && (nn % 2) == 0 && mm <= AMAXM);
    if (ok) {
        for (int v = 0; v < nn; v++) degc[v] = 0;
        for (int i = 0; i < me && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u > v) { int t = u; u = v; v = t; }
            if (u < 0 || u >= mm || v < mm || v >= nn) ok = 0;
            else { degc[u]++; degc[v]++; }
        }
    }
    int maxdeg = 0;
    if (ok) for (int v = 0; v < nn; v++) if (degc[v] > maxdeg) maxdeg = degc[v];
    if (!ok || maxdeg > AQD || dd - maxdeg < 1) { print_input(nn, iu, iv, me); return; }

    a_m = mm;
    a_s = dd - maxdeg;
    a_over = 0; a_size = 0;
    for (int P = 0; P < mm; P++) {
        a_npl[P] = 0; a_npt[P] = 0;
        a_lload[P] = 0; a_pload[P] = 0;
        a_in[P] = 0; a_best_in[P] = 0;
    }
    for (int i = 0; i < me; i++) {
        int u = iu[i], v = iv[i];
        if (u > v) { int t = u; u = v; v = t; }
        int P = u, L = v - mm;
        a_pl[P][a_npl[P]++] = L;
        a_lp[L][a_npt[L]++] = P;
    }

    static const double lams[3] = {0.7, 1.0, 1.4};
    const long CYC = 1500000;
    double lam = 1.0;
    int best_size = 0;
    long it = 0;
    for (;;) {
        if ((it & 1023) == 0) {
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        }
        long ph = it % CYC;
        if (ph == 0) lam = lams[rint_(3)];
        double T = 1.2 * pow(0.015 / 1.2, (double)ph / (double)CYC);
        it++;
        double f0 = (double)a_size - lam * (double)a_over;

        if (rint_(3) == 0) {
            /* swap: add P (not in S), remove Q (in S) */
            int P = rint_(mm), Q = -1;
            if (a_in[P]) continue;
            for (int t = 0; t < 20; t++) {
                int c = rint_(mm);
                if (a_in[c]) { Q = c; break; }
            }
            if (Q < 0) continue;
            a_del(Q); a_add(P);
            double f1 = (double)a_size - lam * (double)a_over;
            double df = f1 - f0;
            if (!(df >= 0 || rdbl() < exp(df / T))) {
                a_del(P); a_add(Q);
                continue;
            }
        } else {
            /* toggle P */
            int P = rint_(mm);
            int was = a_in[P];
            if (was) a_del(P); else a_add(P);
            double f1 = (double)a_size - lam * (double)a_over;
            double df = f1 - f0;
            if (!(df >= 0 || rdbl() < exp(df / T))) {
                if (was) a_add(P); else a_del(P);
                continue;
            }
        }
        if (a_over == 0 && a_size > best_size) {
            best_size = a_size;
            memcpy(a_best_in, a_in, sizeof(int) * (size_t)mm);
        }
    }

    /* Output: the input PG graph plus A_P and B_P for every P in the best set. */
    int k = best_size;
    long extra = 0;
    for (int P = 0; P < mm; P++) if (a_best_in[P]) extra += a_npl[P] + a_npt[P];
    printf("%d %ld\n", 2 * mm + 2 * k, (long)me + extra);
    for (int i = 0; i < me; i++) printf("%d %d\n", iu[i], iv[i]);
    int t = 0;
    for (int P = 0; P < mm; P++) {
        if (!a_best_in[P]) continue;
        int A = 2 * mm + t, B = 2 * mm + k + t;
        for (int i = 0; i < a_npl[P]; i++) printf("%d %d\n", A, mm + a_pl[P][i]);
        for (int i = 0; i < a_npt[P]; i++) printf("%d %d\n", a_lp[P][i], B);
        t++;
    }
}

/* ---------------- default mode: annealing on fixed vertex set ---------------- */

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
    ntmp = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        int miss = n - c;
        bad += miss;
        if (miss > 0) tmpbadv[ntmp++] = v;
    }
    return (int)(bad / 2);
}

static void adopt(void) {
    memcpy(curbadv, tmpbadv, sizeof(int) * (size_t)ntmp);
    ncurbadv = ntmp;
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

static int pick_vertex(void) {
    if (ncurbadv > 0 && rdbl() < 0.6) {
        return curbadv[rint_(ncurbadv)];
    }
    return rint_(n);
}

static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = pick_vertex();
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
        int c = pick_vertex();
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

    if (argc >= 6 && strcmp(argv[5], "arc") == 0) {
        arc_mode(d, n, iu, iv, m0, tl, t0);
        return 0;
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
    adopt();
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
            adopt();
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
            adopt();
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
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each vertex has
# spare capacity s = d - q - 1. Choose S so that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. Add an A-vertex joined
# to the q+1 lines through each P in S, and a B-vertex joined to the q+1 points
# on each line j in S. Diameter 3 holds for every such S.
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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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


def _pg_candidates(d):
    """Prime powers q with spare degree s = d-q-1 >= 1, as (upper bound on order, q), best first.

    The bound 2m + 2*floor(s*m/(q+1)) holds because each chosen point uses q+1 line slots,
    and there are only s*m slots in total.
    """
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        out.append((2 * m + 2 * (s * m // (q + 1)), q))
    out.sort(reverse=True)
    return out


def _arc_sa(d, q, seed, budget):
    """Run the C arc-packing annealer on PG(2,q); returns the extended graph (n, edges)."""
    n, edges = lib.projective_plane_incidence(q)
    out = lib.run_c(C_SOURCE, [d, 3, seed, round(budget, 2), "arc"],
                    stdin_graph=(n, edges), timeout=budget + 10.0)
    return lib.parse_graph_text(out)


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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.88 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3), greedy and conic baselines.
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D == 3:
        bound = lib.moore_bound(d, D)

        # New: load-constrained packing search (C "arc" mode) on PG(2,q).
        # The top candidates by upper bound get the bulk of the arc budget.
        arc_pool = 0.75 * (end - time.monotonic())
        for idx, (pbound, q) in enumerate(_pg_candidates(d)[:2]):
            if best[0] >= bound:
                break
            if pbound <= best[0]:
                continue
            remaining = end - time.monotonic()
            if remaining < 4.0:
                break
            share = 0.7 if idx == 0 else 0.3
            budget = min(arc_pool * share, remaining - 3.0)
            if budget < 1.0:
                break
            try:
                consider(_arc_sa(d, q, seed + idx, budget))
            except Exception:
                pass

        # Focused annealing repair: adds vertices to the best graph, with moves aimed
        # at vertices that take part in bad pairs.
        cbudget = end - time.monotonic()
        if best[0] < bound and cbudget > 3.0:
            try:
                start_graph = (best[0] + 1, list(best[1]))  # one extra isolated vertex
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2)],
                                stdin_graph=start_graph, timeout=cbudget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    # Voltage-lift annealing for D >= 4 (unchanged from parent).
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
