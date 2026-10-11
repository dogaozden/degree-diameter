"""Combined diameter-3 search: arc-extended projective plane starts, the Araujo-Pardo-Lopez
record when it applies, and a C engine with two phases. Phase A adds one vertex at a time
through a greedy cover (always valid). Phase B grows by two vertices with annealed
degree-preserving swaps, keeping only states that pass a full validity check."""
import random
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXDEG 64

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} Snap;

static int d, D, N;
static long moore;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static int badv[MAXN];
static uint64_t RB[MAXN][MAXW];
static uint64_t BALL[MAXN][MAXW];
static uint64_t TMP[MAXN][MAXW];
static Snap best;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { return __builtin_popcountll(x); }

static long compute_moore(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_half(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
}

static void del_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
}

/* R[v] = bitset of vertices within distance r of v. */
static void reach(int r, uint64_t R[MAXN][MAXW]) {
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < MAXW; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) TMP[v][w] = R[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) TMP[v][w] |= R[u][w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) R[v][w] = TMP[v][w];
    }
}

static long bad_pairs(void) {
    int W = (N + 63) / 64;
    reach(D, RB);
    long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(RB[v][w]);
        badv[v] = N - c;
        total += N - c;
    }
    return total / 2;
}

static int valid_graph(void) {
    if (N <= 0 || N > MAXN) return 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] > d) return 0;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (u < 0 || u >= N || u == v || side[u] == side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == u) return 0;
        }
    }
    return bad_pairs() == 0;
}

static void save(Snap *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->adj, adj, sizeof adj);
    memcpy(s->side, side, sizeof side);
}

static void load(const Snap *s) {
    N = s->n;
    memcpy(deg, s->deg, sizeof deg);
    memcpy(adj, s->adj, sizeof adj);
    memcpy(side, s->side, sizeof side);
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2) return 0;
    N = n;
    for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = -1; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= MAXDEG || deg[v] >= MAXDEG)
            return 0;
        add_edge(u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (side[u] < 0) {
                    side[u] = 1 - side[v];
                    q[t++] = u;
                } else if (side[u] == side[v]) {
                    return 0;
                }
            }
        }
    }
    return valid_graph();
}

static void print_graph(void) {
    long m = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m++;
    printf("%d %ld\n", N, m);
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
}

/* Phase A: add one vertex on side X joined to a set T of spare vertices on the other side.
   Every vertex lies within D-1 of T, so the new vertex is within D of everything. */
static int try_add(int X) {
    if (N + 1 >= MAXN) return 0;
    int W = (N + 63) / 64;
    reach(D - 1, BALL);
    uint64_t U[MAXW];
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    static int sel[MAXN];
    for (int v = 0; v < N; v++) sel[v] = 0;
    int T[MAXDEG];
    int nt = 0;
    while (nt < d) {
        int bv = -1;
        long bs = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= d || sel[v]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(BALL[v][w] & U[w]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bs) { bs = sc; bv = v; }
        }
        if (bv < 0) break;
        sel[bv] = 1;
        T[nt++] = bv;
        for (int w = 0; w < W; w++) U[w] &= ~BALL[bv][w];
    }
    for (int w = 0; w < W; w++)
        if (U[w]) return 0;
    if (nt == 0) return 0;
    int x = N;
    N++;
    side[x] = X;
    deg[x] = 0;
    for (int k = 0; k < nt; k++) add_edge(x, T[k]);
    return 1;
}

static void phase_a(double until) {
    int fails = 0;
    while (now() < until && fails < 3000 && N + 1 < MAXN && N + 1 <= moore) {
        if (try_add(rndint(2))) fails = 0;
        else fails++;
    }
}

/* Phase B: insert two new vertices x (side 0) and y (side 1) joined to each other,
   steal edges to give them degree d, then anneal swaps until no pair is too far. */
static int grow_once(double until) {
    int n = N;
    if (n + 2 > moore || n + 2 >= MAXN) return 0;
    int x = n, y = n + 1;
    N = n + 2;
    deg[x] = deg[y] = 0;
    side[x] = 0;
    side[y] = 1;
    add_edge(x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (side[a] != 0 || used[a] == stamp || deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(a, b);
        add_edge(x, b);
        add_edge(y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs();
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = rndint(N);
        for (int tt = 0; tt < 30 && badv[v] == 0; tt++) v = rndint(N);
        if (deg[v] == 0) continue;
        int u = adj[v][rndint(deg[v])];
        int s = rndint(N);
        if (s == v || side[s] != side[v] || deg[s] == 0) continue;
        int t = adj[s][rndint(deg[s])];
        if (t == u || has_edge(v, t) || has_edge(s, u)) continue;
        del_edge(v, u);
        del_edge(s, t);
        add_edge(v, t);
        add_edge(s, u);
        long nb = bad_pairs();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(v, t);
            del_edge(s, u);
            add_edge(v, u);
            add_edge(s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || D < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (!read_input()) {
        printf("0 0\n");
        return 0;
    }
    moore = compute_moore();
    save(&best);

    if (D >= 2 && N < moore) {
        phase_a(t0 + 0.15 * limit);
        if (valid_graph()) save(&best);
        else load(&best);

        while (now() < t_end && N + 2 <= moore && N + 2 < MAXN) {
            double left = t_end - now();
            double slice = (left / 4 > 4.0) ? left / 4 : (left < 4.0 ? left : 4.0);
            if (grow_once(now() + slice) && valid_graph()) save(&best);
            load(&best);
        }
    }
    load(&best);
    print_graph();
    return 0;
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Diameter 3."""
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
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def known_start(d, D):
    """Closed-form record or optimal graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        cands = _arc_extensions(d, t0 + 0.12 * time_limit, rng)
        for cand in sorted(cands, key=lambda g: -g[0]):
            consider(cand)

    # Hand the best construction to C. Compilation counts against the wall clock too,
    # so keep a generous margin.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0 and d <= 60 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 6)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass  # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
