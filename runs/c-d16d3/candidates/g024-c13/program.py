import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing with greedy vertex insertion.
#
# State: a bipartite graph on sides 0/1 with max degree d. Cost = number of
# ordered vertex pairs at distance > D (computed exactly with bitset balls).
# Moves: rewire an edge endpoint, add a cross edge, remove an edge (Metropolis).
# Whenever cost hits 0 the graph is a valid record; a new vertex is then
# inserted, with neighbours chosen by greedy set cover of the (D-1)-balls.
# If the annealing stalls, it restarts from the best valid snapshot with a
# fresh vertex and a random temperature.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WMAX 16
#define MAXDEG 64
#define MAXE 32768
#define STALL 3000

typedef uint64_t u64;

static int N = 0, DEG = 3, DIA = 3;
static int side_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXDEG];
static unsigned char A_[MAXN][MAXN];
static u64 X1[MAXN][WMAX];
static u64 X2[MAXN][WMAX];
static u64 BALL[MAXN][WMAX];
static u64 SCR[MAXN][WMAX];
static u64 rs = 88172645463325252ULL;

static int snap_n = 0, snap_m = 0, snap_ok = 0;
static int snap_u[MAXE], snap_v[MAXE];
static int EU[MAXE], EV[MAXE];

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int nw(void) { return (N + 63) >> 6; }

/* out[v] = bitset of vertices within distance r of v. */
static void compute_balls(int r, u64 out[MAXN][WMAX]) {
    int w = nw(), v, t, k, j;
    u64 (*cur)[WMAX] = X1;
    u64 (*nxt)[WMAX] = X2;
    u64 (*tmp)[WMAX];
    for (v = 0; v < N; v++) {
        for (j = 0; j < w; j++) cur[v][j] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (t = 0; t < r; t++) {
        for (v = 0; v < N; v++) {
            for (j = 0; j < w; j++) nxt[v][j] = cur[v][j];
            for (k = 0; k < deg_[v]; k++) {
                int u = nb_[v][k];
                for (j = 0; j < w; j++) nxt[v][j] |= cur[u][j];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    for (v = 0; v < N; v++)
        for (j = 0; j < w; j++) out[v][j] = cur[v][j];
}

static long long eval_cost(void) {
    int w = nw(), v, j;
    long long bad = 0;
    compute_balls(DIA, SCR);
    for (v = 0; v < N; v++) {
        int c = 0;
        for (j = 0; j < w; j++) c += pc(SCR[v][j]);
        bad += N - c;
    }
    return bad;
}

static void add_edge(int a, int b) {
    A_[a][b] = 1;
    A_[b][a] = 1;
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
}

static void rem_nb(int a, int b) {
    int k;
    for (k = 0; k < deg_[a]; k++) {
        if (nb_[a][k] == b) {
            nb_[a][k] = nb_[a][deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    A_[a][b] = 0;
    A_[b][a] = 0;
    rem_nb(a, b);
    rem_nb(b, a);
}

static int add_vertex(int s) {
    int w = N++, j;
    for (j = 0; j < MAXN; j++) {
        A_[w][j] = 0;
        A_[j][w] = 0;
    }
    side_[w] = s;
    deg_[w] = 0;
    return w;
}

static void take_snapshot(void) {
    int a, k, b;
    snap_m = 0;
    for (a = 0; a < N; a++) {
        for (k = 0; k < deg_[a]; k++) {
            b = nb_[a][k];
            if (a < b && snap_m < MAXE) {
                snap_u[snap_m] = a;
                snap_v[snap_m] = b;
                snap_m++;
            }
        }
    }
    snap_n = N;
}

static void restore(void) {
    int i, j, k;
    for (i = 0; i < N; i++) {
        deg_[i] = 0;
        for (j = 0; j < N; j++) A_[i][j] = 0;
    }
    N = snap_n;
    for (k = 0; k < snap_m; k++) add_edge(snap_u[k], snap_v[k]);
}

/* Greedy set cover of the existing vertices by (D-1)-balls of spare vertices on side 1-s. */
static int greedy_cover(int s, int *chosen, int *nch_out) {
    static int cand[MAXN];
    static char used[MAXN];
    u64 covered[WMAX];
    int w = nw(), nc = 0, nch = 0, t, j, v, bestc, bestg, ties, g, cnt = 0;
    for (v = 0; v < N; v++)
        if (side_[v] != s && deg_[v] < DEG) cand[nc++] = v;
    for (j = 0; j < w; j++) covered[j] = 0;
    memset(used, 0, sizeof(char) * N);
    while (nch < DEG) {
        bestc = -1; bestg = 0; ties = 0;
        for (t = 0; t < nc; t++) {
            v = cand[t];
            if (used[v]) continue;
            g = 0;
            for (j = 0; j < w; j++) g += pc(BALL[v][j] & ~covered[j]);
            if (g > bestg) {
                bestg = g; bestc = v; ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) bestc = v;
            }
        }
        if (bestc < 0) break;
        used[bestc] = 1;
        chosen[nch++] = bestc;
        for (j = 0; j < w; j++) covered[j] |= BALL[bestc][j];
        cnt = 0;
        for (j = 0; j < w; j++) cnt += pc(covered[j]);
        if (cnt >= N) break;
    }
    cnt = 0;
    for (j = 0; j < w; j++) cnt += pc(covered[j]);
    *nch_out = nch;
    return cnt;
}

/* Insert one vertex adjacent to a greedy cover. Returns 1 if the cover was complete. */
static int grow(void) {
    int ord0, tryi, s, nch = 0, cnt, bestS = -1, bestN = 0, bestCnt = -1, i, wn, Nold;
    int chosen[MAXDEG], bestChosen[MAXDEG];
    if (N >= MAXN - 2) return 0;
    compute_balls(DIA - 1, BALL);
    ord0 = rndint(2);
    for (tryi = 0; tryi < 2; tryi++) {
        s = (tryi == 0) ? ord0 : 1 - ord0;
        cnt = greedy_cover(s, chosen, &nch);
        if (nch > 0 && cnt > bestCnt) {
            bestCnt = cnt;
            bestS = s;
            bestN = nch;
            for (i = 0; i < nch; i++) bestChosen[i] = chosen[i];
        }
        if (bestCnt >= N) break;
    }
    if (bestS < 0) return 0;
    Nold = N;
    wn = add_vertex(bestS);
    for (i = 0; i < bestN; i++) add_edge(wn, bestChosen[i]);
    return bestCnt >= Nold;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    int n, m, i, k, a, b, c, cntE = 0, changed, mv;
    double tl, T = 1.0;
    clock_t t0;
    long long cur, nc2, lbest;
    int stall = 0;
    unsigned long long iter = 0;
    long seed;

    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    seed = atol(argv[3]);
    tl = atof(argv[4]);
    if (DEG < 1) DEG = 1;
    if (DEG > MAXDEG) DEG = MAXDEG;
    if (DIA < 1) DIA = 1;
    rs = (u64)seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 20; i++) rnd();

    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 2 || n > MAXN - 8 || m <= 0) {
        N = 2;
        side_[0] = 0;
        side_[1] = 1;
        add_edge(0, 1);
    } else {
        N = n;
        for (i = 0; i < m; i++) {
            if (scanf("%d %d", &a, &b) != 2) break;
            if (a < 0 || a >= n || b < 0 || b >= n || a == b) continue;
            if (cntE < MAXE) {
                EU[cntE] = a;
                EV[cntE] = b;
                cntE++;
            }
        }
        for (i = 0; i < N; i++) side_[i] = -1;
        for (i = 0; i < N; i++) {
            if (side_[i] >= 0) continue;
            side_[i] = 0;
            changed = 1;
            while (changed) {
                changed = 0;
                for (k = 0; k < cntE; k++) {
                    a = EU[k];
                    b = EV[k];
                    if (side_[a] >= 0 && side_[b] < 0) {
                        side_[b] = 1 - side_[a];
                        changed = 1;
                    } else if (side_[b] >= 0 && side_[a] < 0) {
                        side_[a] = 1 - side_[b];
                        changed = 1;
                    }
                }
            }
        }
        for (k = 0; k < cntE; k++) {
            a = EU[k];
            b = EV[k];
            if (side_[a] == side_[b]) continue;
            if (deg_[a] >= DEG || deg_[b] >= DEG || A_[a][b]) continue;
            add_edge(a, b);
        }
    }

    cur = eval_cost();
    take_snapshot();
    snap_ok = (cur == 0);
    lbest = cur;
    t0 = clock();

    while (1) {
        if ((iter & 31ULL) == 0ULL) {
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        }
        iter++;

        if (cur == 0) {
            if (!snap_ok || N > snap_n) {
                take_snapshot();
                snap_ok = 1;
            }
            if (N < MAXN - 2) {
                int before = N;
                grow();
                if (N > before) {
                    cur = eval_cost();
                    lbest = cur;
                    stall = 0;
                    continue;
                }
            }
        }

        mv = rndint(3);
        if (mv == 0) {
            /* rewire one endpoint of an edge to a new partner on the other side */
            a = rndint(N);
            if (deg_[a] == 0) continue;
            b = nb_[a][rndint(deg_[a])];
            c = rndint(N);
            if (side_[c] == side_[a] || c == b || deg_[c] >= DEG || A_[a][c]) continue;
            del_edge(a, b);
            add_edge(a, c);
            nc2 = eval_cost();
            if (accept(nc2 - cur, T)) {
                cur = nc2;
            } else {
                del_edge(a, c);
                add_edge(a, b);
            }
        } else if (mv == 1) {
            /* add a cross edge between two spare vertices */
            a = rndint(N);
            c = rndint(N);
            if (a == c || side_[a] == side_[c] || deg_[a] >= DEG || deg_[c] >= DEG || A_[a][c]) continue;
            add_edge(a, c);
            nc2 = eval_cost();
            if (accept(nc2 - cur, T)) {
                cur = nc2;
            } else {
                del_edge(a, c);
            }
        } else {
            /* remove a random edge */
            a = rndint(N);
            if (deg_[a] == 0) continue;
            b = nb_[a][rndint(deg_[a])];
            del_edge(a, b);
            nc2 = eval_cost();
            if (accept(nc2 - cur, T)) {
                cur = nc2;
            } else {
                add_edge(a, b);
            }
        }

        if (cur < lbest) {
            lbest = cur;
            stall = 0;
        } else {
            stall++;
        }
        if (stall > STALL) {
            T = 0.4 + 2.0 * rnd01();
            if (snap_ok) {
                restore();
                if (N < MAXN - 2) grow();
            }
            cur = eval_cost();
            lbest = cur;
            stall = 0;
        }
    }

    printf("%d %d\n", snap_n, snap_m);
    for (i = 0; i < snap_m; i++) printf("%d %d\n", snap_u[i], snap_v[i]);
    return 0;
}
'''


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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed * 7919 + d)

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
        arcs = _arc_extensions(d, t0 + 0.12 * time_limit, rng)
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealing + vertex insertion in C, started from the best graph so far.
    deadline = t0 + 0.88 * time_limit
    budget = deadline - time.monotonic() - 1.0
    if budget > 0.5:
        hard_timeout = max(1.0, time_limit * 0.97 - (time.monotonic() - t0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=hard_timeout)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
