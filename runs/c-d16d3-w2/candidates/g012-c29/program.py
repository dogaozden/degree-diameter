import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: wall-clock local search that grows a valid bipartite graph.
#
# It starts from a valid graph (or any graph; it anneals to validity first).
# Each growth step adds one vertex on one side, joined to spare-capacity
# vertices on the other side, then runs simulated annealing with degree-
# preserving 2-switches, edge additions and endpoint rewiring to drive the
# number of vertex pairs at distance > D to zero. Bipartiteness is preserved
# by construction because every edge joins side 0 to side 1.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)
#define ITERS 15000LL
#define MAXFAIL 5

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

static int d_, D_, N, W;
static int side[MAXN], deg[MAXN], nb[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static long long cur_cost = 0;
static int have_best = 0, saved_N = 0, saved_E = 0;
static int saved_side[MAXN];
static int saved_e[MAXE][2];
static int in_u[MAXE], in_v[MAXE], in_m = 0;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) {
    return (int)(rnd() % (uint64_t)n);
}

static double runif(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    A[a][b] = 1;
    A[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_list(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    A[a][b] = 0;
    A[b][a] = 0;
    del_list(a, b);
    del_list(b, a);
}

/* Number of ordered pairs (x, y) with dist(x, y) > D_. Zero means valid. */
static long long cost_eval(void) {
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) bufA[v][w] = 0;
        bufA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pop64(cur[v][w]);
        bad += N - c;
    }
    return bad;
}

/* Random side-0 vertex with positive degree and a random neighbour (side 1). */
static void pick_edge_side0(int *a, int *b) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < N; v++) {
        if (side[v] == 0 && deg[v] > 0) {
            cnt++;
            if (rint_(cnt) == 0) pick = v;
        }
    }
    if (pick < 0) {
        *a = -1;
        *b = -1;
        return;
    }
    *a = pick;
    *b = nb[pick][rint_(deg[pick])];
}

/* Random vertex on side s with spare capacity, not equal to exclude; -1 if none. */
static int pick_spare(int s, int exclude) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < N; v++) {
        if (side[v] == s && deg[v] < d_ && v != exclude) {
            cnt++;
            if (rint_(cnt) == 0) pick = v;
        }
    }
    return pick;
}

static int gen_move(Move *m) {
    int t = rint_(3);
    m->nr = 0;
    m->na = 0;
    if (t == 0) {
        /* degree-preserving 2-switch */
        int a, b, a2, b2;
        pick_edge_side0(&a, &b);
        pick_edge_side0(&a2, &b2);
        if (a < 0 || a2 < 0 || a == a2 || b == b2) return 0;
        if (A[a][b2] || A[a2][b]) return 0;
        m->nr = 2;
        m->ra[0] = a; m->rb[0] = b;
        m->ra[1] = a2; m->rb[1] = b2;
        m->na = 2;
        m->aa[0] = a; m->ab[0] = b2;
        m->aa[1] = a2; m->ab[1] = b;
    } else if (t == 1) {
        /* add an edge between two spare vertices */
        int a = pick_spare(0, -1);
        int b = pick_spare(1, -1);
        if (a < 0 || b < 0 || A[a][b]) return 0;
        m->na = 1;
        m->aa[0] = a; m->ab[0] = b;
    } else {
        /* rewire one endpoint of a random edge to a spare vertex */
        int a, b;
        pick_edge_side0(&a, &b);
        if (a < 0) return 0;
        if (rint_(2) == 0) {
            int b2 = pick_spare(1, b);
            if (b2 < 0 || A[a][b2]) return 0;
            m->nr = 1; m->ra[0] = a; m->rb[0] = b;
            m->na = 1; m->aa[0] = a; m->ab[0] = b2;
        } else {
            int a2 = pick_spare(0, a);
            if (a2 < 0 || A[a2][b]) return 0;
            m->nr = 1; m->ra[0] = a; m->rb[0] = b;
            m->na = 1; m->aa[0] = a2; m->ab[0] = b;
        }
    }
    return 1;
}

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->ra[i], m->rb[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->aa[i], m->ab[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ra[i], m->rb[i]);
}

static void anneal(long long iters, double T0, double T1, double deadline) {
    for (long long it = 0; it < iters && cur_cost > 0; it++) {
        if (now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        Move m;
        if (!gen_move(&m)) continue;
        apply_move(&m);
        long long c2 = cost_eval();
        long long delta = c2 - cur_cost;
        if (delta <= 0 || runif() < exp(-(double)delta / T)) {
            cur_cost = c2;
        } else {
            undo_move(&m);
        }
    }
}

static void save_state(void) {
    saved_N = N;
    saved_E = 0;
    for (int v = 0; v < N; v++) {
        saved_side[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u > v && saved_E < MAXE) {
                saved_e[saved_E][0] = v;
                saved_e[saved_E][1] = u;
                saved_E++;
            }
        }
    }
    have_best = 1;
}

static void restore(void) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) A[v][nb[v][k]] = 0;
        deg[v] = 0;
    }
    N = saved_N;
    for (int v = 0; v < N; v++) side[v] = saved_side[v];
    for (int i = 0; i < saved_E; i++) add_edge(saved_e[i][0], saved_e[i][1]);
}

static int count_spare(int s) {
    int c = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == s && deg[v] < d_) c++;
    return c;
}

/* Add a new vertex joined to up to d spare vertices on the opposite side. */
static int grow(void) {
    if (N >= MAXN - 1) return 0;
    int c = rint_(2);
    if (count_spare(1 - c) < d_ / 2) c = 1 - c;
    int opp = 1 - c;
    int cand[MAXN], nc = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == opp && deg[v] < d_) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int x = N;
    side[x] = c;
    deg[x] = 0;
    N++;
    int k = nc < d_ ? nc : d_;
    for (int i = 0; i < k; i++) add_edge(x, cand[i]);
    return 1;
}

static int bfs_sides(int n) {
    static int q[MAXN];
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                if (side[u] < 0) {
                    side[u] = 1 - side[v];
                    q[t++] = u;
                } else if (side[u] == side[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_input(int n) {
    printf("%d %d\n", n, in_m);
    for (int i = 0; i < in_m; i++) printf("%d %d\n", in_u[i], in_v[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    double t_start = now_s();
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 88172645463325252ULL;
    double budget = atof(argv[4]);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    if (d_ < 1 || d_ > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    int bad_input = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad_input = 1;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] ||
            deg[u] >= MAXDEG || deg[v] >= MAXDEG) {
            bad_input = 1;
            continue;
        }
        add_edge(u, v);
        in_u[in_m] = u;
        in_v[in_m] = v;
        in_m++;
    }
    if (bad_input) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) {
        if (deg[v] > d_) {
            print_input(n);
            return 0;
        }
    }
    if (!bfs_sides(n)) {
        print_input(n);
        return 0;
    }

    cur_cost = cost_eval();
    double deadline = t_start + budget;
    if (cur_cost == 0) save_state();

    int fails = 0;
    while (now_s() < deadline) {
        if (cur_cost == 0) {
            save_state();
            if (!grow()) break;
            cur_cost = cost_eval();
            fails = 0;
            continue;
        }
        anneal(ITERS, 1.5, 0.05, deadline);
        if (cur_cost > 0) {
            fails++;
            if (fails >= MAXFAIL && have_best) {
                restore();
                cur_cost = cost_eval();
                fails = 0;
            }
        }
    }
    if (cur_cost == 0) save_state();

    if (have_best) {
        printf("%d %d\n", saved_N, saved_E);
        for (int i = 0; i < saved_E; i++)
            printf("%d %d\n", saved_e[i][0], saved_e[i][1]);
    } else {
        print_input(n);
    }
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


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
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
# Simulated annealing over bi-Cayley voltage lifts.
# ----------------------------------------------------------------------------

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


_BIG = 10 ** 9


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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Keep a margin for C compilation and process startup.
    total = max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.1 * total, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Python group-lift annealing, kept as a strong fallback source.
    group_deadline = t0 + 0.25 * total
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < group_deadline:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, group_deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Bold step: C wall-clock search that grows the best valid graph by
    # adding vertices and repairing distances with local search.
    remaining = t0 + total - time.monotonic()
    if remaining > 3.0:
        budget_c = remaining - 2.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget_c:.2f}"],
                            stdin_graph=best, timeout=budget_c + 15.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
