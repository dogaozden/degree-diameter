import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow a valid bipartite graph one vertex at a time.
#
# Start from the given valid graph. To grow, add a vertex on the lighter side,
# join it greedily to spare-degree vertices on the other side, then run
# simulated annealing on the number of ordered pairs at distance > D. Moves keep
# degrees <= d and the bipartition fixed: degree-preserving 2-switches, adding
# edges between spare vertices, and moving one endpoint of an edge to a spare
# vertex. Distances use bitset balls of radius D. On success the state is saved;
# on failure it is restored. The best valid state is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define WMAX (NMAX / 64)
#define MAXIT 15000L

static int DEG, RAD;
static int n;
static int col[NMAX];
static int deg[NMAX];
static int *nb;
static unsigned char A[NMAX][NMAX];
static uint64_t bufA[NMAX * WMAX];
static uint64_t bufB[NMAX * WMAX];
static int L[2][NMAX];
static int cnt[2];
static uint64_t rs;
static int *snap_nb;
static int snap_deg[NMAX], snap_col[NMAX], snap_n;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Sum over v of (n - |ball_RAD(v)|): ordered pairs at distance > RAD. Zero means valid. */
static long cost_eval(void) {
    int w = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < RAD; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            memcpy(dst, cur + (size_t)v * w, sizeof(uint64_t) * (size_t)w);
            const int *q = nb + (size_t)v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)q[k] * w;
                for (int i = 0; i < w; i++) dst[i] |= src[i];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *b = cur + (size_t)v * w;
        int c = 0;
        for (int i = 0; i < w; i++) c += pc64(b[i]);
        total += n - c;
    }
    return total;
}

static int find_nb(int a, int b) {
    const int *q = nb + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (q[k] == b) return k;
    return -1;
}

static void add_edge(int a, int b) {
    nb[(size_t)a * DEG + deg[a]++] = b;
    nb[(size_t)b * DEG + deg[b]++] = a;
    A[a][b] = 1;
    A[b][a] = 1;
}

static void del_edge(int a, int b) {
    int k = find_nb(a, b);
    nb[(size_t)a * DEG + k] = nb[(size_t)a * DEG + deg[a] - 1];
    deg[a]--;
    k = find_nb(b, a);
    nb[(size_t)b * DEG + k] = nb[(size_t)b * DEG + deg[b] - 1];
    deg[b]--;
    A[a][b] = 0;
    A[b][a] = 0;
}

typedef struct {
    int nr, ra[2], rb[2];
    int na, aa[2], ab[2];
} Op;

static Op op;

static void apply_op(void) {
    for (int i = 0; i < op.nr; i++) del_edge(op.ra[i], op.rb[i]);
    for (int i = 0; i < op.na; i++) add_edge(op.aa[i], op.ab[i]);
}

static void undo_op(void) {
    for (int i = 0; i < op.na; i++) del_edge(op.aa[i], op.ab[i]);
    for (int i = 0; i < op.nr; i++) add_edge(op.ra[i], op.rb[i]);
}

/* Propose a move into `op`. Returns 0 if the attempt is not applicable. */
static int propose(void) {
    op.nr = 0;
    op.na = 0;
    if (cnt[0] < 1 || cnt[1] < 1) return 0;
    int r = rndint(100);
    if (r < 40) {
        /* degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b) */
        int a = L[0][rndint(cnt[0])];
        int c = L[0][rndint(cnt[0])];
        if (a == c || deg[a] == 0 || deg[c] == 0) return 0;
        int b = nb[(size_t)a * DEG + rndint(deg[a])];
        int e = nb[(size_t)c * DEG + rndint(deg[c])];
        if (A[a][e] || A[c][b]) return 0;
        op.nr = 2;
        op.ra[0] = a; op.rb[0] = b;
        op.ra[1] = c; op.rb[1] = e;
        op.na = 2;
        op.aa[0] = a; op.ab[0] = e;
        op.aa[1] = c; op.ab[1] = b;
        return 1;
    } else if (r < 65) {
        /* add an edge between two spare vertices */
        for (int t = 0; t < 6; t++) {
            int a = L[0][rndint(cnt[0])];
            int b = L[1][rndint(cnt[1])];
            if (deg[a] < DEG && deg[b] < DEG && !A[a][b]) {
                op.na = 1;
                op.aa[0] = a;
                op.ab[0] = b;
                return 1;
            }
        }
        return 0;
    } else {
        /* move one endpoint of an edge to a spare vertex */
        int a = L[0][rndint(cnt[0])];
        if (deg[a] == 0) return 0;
        int b = nb[(size_t)a * DEG + rndint(deg[a])];
        if (rndint(2)) {
            int b2 = L[1][rndint(cnt[1])];
            if (b2 == b || deg[b2] >= DEG || A[a][b2]) return 0;
            op.nr = 1; op.ra[0] = a; op.rb[0] = b;
            op.na = 1; op.aa[0] = a; op.ab[0] = b2;
        } else {
            int a2 = L[0][rndint(cnt[0])];
            if (a2 == a || deg[a2] >= DEG || A[a2][b]) return 0;
            op.nr = 1; op.ra[0] = a; op.rb[0] = b;
            op.na = 1; op.aa[0] = a2; op.ab[0] = b;
        }
        return 1;
    }
}

/* Simulated annealing at fixed vertex count. Returns 1 if cost reaches zero. */
static int anneal(long maxit, double T0, double T1, double deadline) {
    long cur = cost_eval();
    if (cur == 0) return 1;
    double ratio = T1 / T0;
    for (long it = 0; it < maxit; it++) {
        if ((it & 63) == 0 && wall() > deadline) return 0;
        if (!propose()) continue;
        double T = T0 * pow(ratio, (double)it / (double)maxit);
        apply_op();
        long nc = cost_eval();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_op();
        }
    }
    return 0;
}

static void take_snapshot(void) {
    snap_n = n;
    memcpy(snap_deg, deg, sizeof(int) * (size_t)n);
    memcpy(snap_col, col, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++)
        memcpy(snap_nb + (size_t)v * DEG, nb + (size_t)v * DEG, sizeof(int) * (size_t)deg[v]);
}

static void restore_snapshot(void) {
    n = snap_n;
    memcpy(deg, snap_deg, sizeof(int) * (size_t)n);
    memcpy(col, snap_col, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++)
        memcpy(nb + (size_t)v * DEG, snap_nb + (size_t)v * DEG, sizeof(int) * (size_t)deg[v]);
    cnt[0] = 0;
    cnt[1] = 0;
    for (int v = 0; v < n; v++) L[col[v]][cnt[col[v]]++] = v;
    memset(A, 0, sizeof A);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) A[v][nb[(size_t)v * DEG + k]] = 1;
}

/* Add a vertex on the lighter side and connect it greedily to spare opposite vertices. */
static int add_vertex(void) {
    if (n >= NMAX - 1) return 0;
    int c = (cnt[0] <= cnt[1]) ? 0 : 1;
    int v = n++;
    col[v] = c;
    deg[v] = 0;
    L[c][cnt[c]++] = v;
    int o = 1 - c;
    int m = cnt[o];
    int *perm = malloc(sizeof(int) * (size_t)(m + 1));
    if (!perm) return 1;
    memcpy(perm, L[o], sizeof(int) * (size_t)m);
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i];
        perm[i] = perm[j];
        perm[j] = t;
    }
    for (int i = 0; i < m && deg[v] < DEG; i++) {
        int u = perm[i];
        if (deg[u] < DEG && !A[u][v]) add_edge(u, v);
    }
    free(perm);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    double t0 = wall();
    DEG = atoi(argv[1]);
    RAD = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    double deadline = t0 + tl - 0.2;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 >= NMAX - 1 || DEG < 1 || RAD < 1 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    nb = malloc(sizeof(int) * (size_t)NMAX * (size_t)DEG);
    snap_nb = malloc(sizeof(int) * (size_t)NMAX * (size_t)DEG);
    if (!nb || !snap_nb) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] || deg[u] >= DEG || deg[v] >= DEG) {
            bad = 1;
            break;
        }
        add_edge(u, v);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the start graph; it must be bipartite. */
    for (int v = 0; v < n; v++) col[v] = -1;
    int *queue = malloc(sizeof(int) * NMAX);
    if (!queue) {
        printf("0 0\n");
        return 0;
    }
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[(size_t)u * DEG + k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                }
            }
        }
    }
    free(queue);
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    cnt[0] = 0;
    cnt[1] = 0;
    for (int v = 0; v < n; v++) L[col[v]][cnt[col[v]]++] = v;
    if (cnt[0] == 0 || cnt[1] == 0) {
        printf("0 0\n");
        return 0;
    }

    int ok = 1;
    if (cost_eval() != 0) ok = anneal(MAXIT * 4, 2.0, 0.05, deadline);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    take_snapshot();

    while (wall() < deadline - 0.1) {
        if (!add_vertex()) break;
        if (anneal(MAXIT, 2.0, 0.05, deadline)) take_snapshot();
        else restore_snapshot();
    }

    restore_snapshot();
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }

    long m = 0;
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (nb[(size_t)v * DEG + k] > v) m++;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[(size_t)v * DEG + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane graphs (D = 3) and the
# generalized quadrangle W(q) (D = 4). These are the starting points for the C engine.
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
    """True if every target is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets so that every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
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
    """Return (n, edges) candidates from arc-extended PG(2, q) for each prime power q with q + 1 <= d."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
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
# Driver: fallback, then arc/GQ starts, then the C growth search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        try:
            n, e = cand
        except (TypeError, ValueError):
            return
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Construction phase (kept under about 15% of the budget).
    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, rng)
        for cand in sorted(cands, key=lambda t: -t[0]):
            consider(cand)

    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # C growth search (only useful for D >= 3; K_{d,d} is optimal for D = 2).
    elapsed = time.monotonic() - t0
    c_budget = 0.72 * time_limit - elapsed - 2.0
    if D >= 3 and c_budget >= 2.0 and best_n >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=best, timeout=c_budget + 2.0)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
