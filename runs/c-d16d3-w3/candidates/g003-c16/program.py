import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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
# C engine A (NEW, bold): abelian Haar graphs via difference covers.
#
# Bipartite graph on Z_G x {A, B}: a_g ~ b_{g+s} for s in S, |S| = d.
# Diameter <= 3 holds iff S - S covers the whole group (A-A distances <= 2
# force it, and then (S-S)+S covers G so the A-B and B-B pairs are fine).
# So we search for a d-subset S of an abelian group of order G whose
# difference set covers G, for G from a lower bound upward.
# Group = Z_A x Z_B (A*B = G). Simulated annealing on the number of uncovered
# nonzero elements, with incremental difference counts.
# Output: the largest valid Haar graph found (or "0 0").
# ----------------------------------------------------------------------------

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXG 1024
#define MAXK 64

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int G, K, GA, GB;
static int addt[MAXG * MAXG];
static int negt[MAXG];
static int dif[MAXG * MAXG];
static int cnt[MAXG];
static int inS[MAXG];
static int S[MAXK];
static int sz, uncov;

static void build_group(int a, int b) {
    GA = a; GB = b; G = a * b;
    for (int e = 0; e < G; e++) {
        int x = e / GB, y = e % GB;
        for (int f = 0; f < G; f++) {
            int x2 = f / GB, y2 = f % GB;
            addt[e * G + f] = ((x + x2) % GA) * GB + (y + y2) % GB;
        }
    }
    for (int e = 0; e < G; e++) {
        int x = e / GB, y = e % GB;
        negt[e] = ((GA - x) % GA) * GB + (GB - y) % GB;
    }
    for (int e = 0; e < G; e++)
        for (int f = 0; f < G; f++)
            dif[e * G + f] = addt[e * G + negt[f]];
}

static void add_elem(int y) {
    for (int i = 0; i < sz; i++) {
        int s = S[i];
        if (cnt[dif[y * G + s]]++ == 0) uncov--;
        if (cnt[dif[s * G + y]]++ == 0) uncov--;
    }
    S[sz++] = y;
    inS[y] = 1;
}

static void remove_at(int i) {
    int x = S[i];
    sz--;
    S[i] = S[sz];
    inS[x] = 0;
    for (int j = 0; j < sz; j++) {
        int s = S[j];
        if (--cnt[dif[x * G + s]] == 0) uncov++;
        if (--cnt[dif[s * G + x]] == 0) uncov++;
    }
}

static void reset_state(void) {
    memset(cnt, 0, sizeof(int) * (size_t)G);
    memset(inS, 0, sizeof(int) * (size_t)G);
    sz = 0;
    uncov = G - 1;
    for (int k = 0; k < K; k++) {
        int y;
        do { y = rndint(G); } while (inS[y]);
        add_elem(y);
    }
}

static int anneal(long iters, double T0, double T1) {
    double T = T0;
    double fac = pow(T1 / T0, 1.0 / (double)iters);
    for (long it = 0; it < iters; it++) {
        if (uncov == 0) return 1;
        int i = rndint(K);
        int y;
        do { y = rndint(G); } while (inS[y]);
        int x = S[i];
        int old = uncov;
        remove_at(i);
        add_elem(y);
        int dc = uncov - old;
        if (!(dc <= 0 || rnd01() < exp(-dc / T))) {
            remove_at(sz - 1);
            add_elem(x);
        }
        T *= fac;
    }
    return uncov == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = (unsigned long long)atoll(argv[3]);
    double tl = atof(argv[4]);
    int mlo = atoi(argv[5]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    K = d;
    if (D != 3 || K < 3 || K > 32) { printf("0 0\n"); return 0; }
    int mhi = K * (K - 1) + 1;
    if (mhi > MAXG - 1) mhi = MAXG - 1;
    if (mlo < K + 1) mlo = K + 1;

    int bestm = 0, bestA = 1, bestB = 1;
    int bestS[MAXK];
    double t0 = now();

    for (int m = mlo; m <= mhi; m++) {
        if (now() - t0 > tl) break;
        int fa[64], fb[64], nf = 0;
        fa[nf] = 1; fb[nf] = m; nf++;
        for (int a = 2; a * a <= m && nf < 63; a++)
            if (m % a == 0) { fa[nf] = a; fb[nf] = m / a; nf++; }

        double dl = now() + 0.4 * (tl - (now() - t0));
        int found = 0;
        int att = 0;
        while (!found && now() < dl) {
            int f = att % nf;
            att++;
            build_group(fa[f], fb[f]);
            reset_state();
            if (anneal(1500000L, 1.5, 0.05)) {
                found = 1;
                bestm = m;
                bestA = fa[f];
                bestB = fb[f];
                for (int i = 0; i < K; i++) bestS[i] = S[i];
            }
        }
        if (!found) break;
    }

    if (bestm == 0) { printf("0 0\n"); return 0; }
    build_group(bestA, bestB);
    printf("%d %d\n", 2 * G, G * K);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < K; i++)
            printf("%d %d\n", g, G + addt[g * G + bestS[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine B: dominating-set insertion with ruin-and-recreate.
#
# State: a bipartite graph with max degree d and diameter <= D.
# Insertion: a new vertex v on side 1-c is joined to a set of at most
# d spare vertices on side c whose radius-(D-1) balls cover all current vertices.
# Then ecc(v) <= D, and adding v only shortens old distances, so validity is kept.
# Distances are maintained incrementally in O(n^2) per insertion.
# Perturbation: remove one or two random vertices if the diameter stays <= D.
# The best graph seen is kept, and the search restores it after a large drop.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define INF 100
typedef uint64_t u64;

static int D_, DEG_, CAP, W, n;
static int *deg, *adj, *col, *queue_, *cand, *dv, *sel, *best_sel;
static unsigned char *dist, *used;
static u64 *ball, *unc;
static unsigned long long rs = 88172645463325252ULL;

typedef struct { int n; int *deg; int *adj; int *col; } Snap;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[(size_t)a * DEG_ + deg[a]++] = b;
    adj[(size_t)b * DEG_ + deg[b]++] = a;
}

static void recompute_dist(void) {
    for (int s = 0; s < n; s++) {
        unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++) row[x] = INF;
        row[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (row[v] == INF) {
                    row[v] = (unsigned char)(row[u] + 1);
                    queue_[t++] = v;
                }
            }
        }
    }
}

static int diam_ok(void) {
    for (int s = 0; s < n; s++) {
        const unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] > D_) return 0;
    }
    return 1;
}

static void build_balls(void) {
    for (int v = 0; v < n; v++) {
        u64 *b = ball + (size_t)v * W;
        memset(b, 0, sizeof(u64) * (size_t)W);
        const unsigned char *row = dist + (size_t)v * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] <= D_ - 1) b[x >> 6] |= 1ULL << (x & 63);
    }
}

/* Greedy set cover of all current vertices by balls of spare vertices of colour c.
   Returns the number of chosen neighbours (<= DEG_) written to best_sel, or -1. */
static int try_insert(int c, int restarts) {
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == c && deg[v] < DEG_) cand[nc++] = v;
    if (nc == 0) return -1;
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < W; w++) unc[w] = 0;
        for (int x = 0; x < n; x++) unc[x >> 6] |= 1ULL << (x & 63);
        int uncount = n, ns = 0;
        memset(used, 0, (size_t)nc);
        while (uncount > 0 && ns < DEG_) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used[i]) continue;
                const u64 *b = ball + (size_t)cand[i] * W;
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(b[w] & unc[w]);
                if (g == 0) continue;
                long long key = (long long)g * 4096 + (long long)(rnd() % 4096);
                if (key > bkey) { bkey = key; bi = i; }
            }
            if (bi < 0) break;
            used[bi] = 1;
            sel[ns++] = cand[bi];
            const u64 *b = ball + (size_t)cand[bi] * W;
            uncount = 0;
            for (int w = 0; w < W; w++) {
                unc[w] &= ~b[w];
                uncount += pc64(unc[w]);
            }
        }
        if (uncount == 0) {
            for (int k = 0; k < ns; k++) best_sel[k] = sel[k];
            return ns;
        }
    }
    return -1;
}

/* Insert a new vertex of colour 1-c adjacent to best_sel[0..ns-1]; update distances. */
static void insert_vertex(int c, int ns) {
    int v = n++;
    col[v] = 1 - c;
    deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(v, best_sel[k]);
    for (int x = 0; x < v; x++) {
        int m = INF;
        for (int k = 0; k < ns; k++) {
            int t = dist[(size_t)x * CAP + best_sel[k]];
            if (t < m) m = t;
        }
        int dd = m + 1;
        if (dd > INF) dd = INF;
        dv[x] = dd;
    }
    for (int x = 0; x < v; x++) {
        dist[(size_t)x * CAP + v] = (unsigned char)dv[x];
        dist[(size_t)v * CAP + x] = (unsigned char)dv[x];
    }
    dist[(size_t)v * CAP + v] = 0;
    for (int x = 0; x < v; x++) {
        unsigned char *row = dist + (size_t)x * CAP;
        for (int y = 0; y < v; y++) {
            int t = dv[x] + dv[y];
            if (t > INF) t = INF;
            if (t < row[y]) row[y] = (unsigned char)t;
        }
    }
}

static void del_nbr(int u, int x) {
    int *a = adj + (size_t)u * DEG_;
    for (int j = 0; j < deg[u]; j++) {
        if (a[j] == x) {
            a[j] = a[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_vertex(int r) {
    int last = n - 1;
    for (int k = 0; k < deg[r]; k++) del_nbr(adj[(size_t)r * DEG_ + k], r);
    deg[r] = 0;
    if (r != last) {
        for (int k = 0; k < deg[last]; k++) {
            int u = adj[(size_t)last * DEG_ + k];
            int *a = adj + (size_t)u * DEG_;
            for (int j = 0; j < deg[u]; j++) {
                if (a[j] == last) { a[j] = r; break; }
            }
        }
        memcpy(adj + (size_t)r * DEG_, adj + (size_t)last * DEG_, sizeof(int) * (size_t)DEG_);
        deg[r] = deg[last];
        col[r] = col[last];
    }
    deg[last] = 0;
    col[last] = -1;
    n--;
    recompute_dist();
}

static void snap_init(Snap *s) {
    s->n = 0;
    s->deg = calloc((size_t)CAP, sizeof(int));
    s->adj = calloc((size_t)CAP * DEG_, sizeof(int));
    s->col = calloc((size_t)CAP, sizeof(int));
}

static void snap_save(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * DEG_);
}

static void snap_load(Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * DEG_);
    recompute_dist();
}

static void emit_state(int nn, const int *dg, const int *ad) {
    long m = 0;
    for (int v = 0; v < nn; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", nn, m);
    for (int v = 0; v < nn; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = ad[(size_t)v * DEG_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tl = atof(argv[4]);
    DEG_ = d;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0) nin = 0;
    if (min_ < 0) min_ = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 2));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 2));
    int m_read = 0;
    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= nin || b >= nin || a == b) continue;
        eu[m_read] = a;
        ev[m_read] = b;
        m_read++;
    }
    if (nin == 0) {
        nin = 2;
        m_read = 1;
        eu[0] = 0;
        ev[0] = 1;
    }

    CAP = nin + 1500;
    W = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG_, sizeof(int));
    col = malloc(sizeof(int) * (size_t)CAP);
    queue_ = malloc(sizeof(int) * (size_t)CAP);
    cand = malloc(sizeof(int) * (size_t)CAP);
    dv = malloc(sizeof(int) * (size_t)CAP);
    sel = malloc(sizeof(int) * (size_t)DEG_ + sizeof(int));
    best_sel = malloc(sizeof(int) * (size_t)DEG_ + sizeof(int));
    dist = malloc((size_t)CAP * CAP);
    used = malloc((size_t)CAP);
    ball = calloc((size_t)CAP * W, sizeof(u64));
    unc = calloc((size_t)W, sizeof(u64));

    n = nin;
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int i = 0; i < m_read; i++)
        if (deg[eu[i]] < DEG_ && deg[ev[i]] < DEG_) add_edge(eu[i], ev[i]);

    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue_[t++] = v; }
                else if (col[v] == col[u]) bip = 0;
            }
        }
    }
    recompute_dist();
    if (!bip || !diam_ok()) {
        emit_state(n, deg, adj);
        return 0;
    }

    Snap best, tmp;
    snap_init(&best);
    snap_init(&tmp);
    snap_save(&best);
    int best_n = n;

    double t0 = now();
    while (now() - t0 < tl) {
        if (n + 2 >= CAP) break;
        build_balls();
        int inserted = 0;
        int first = rndint(2);
        for (int t = 0; t < 2 && !inserted; t++) {
            int c = (t == 0) ? first : 1 - first;
            int ns = try_insert(c, 6);
            if (ns > 0) {
                insert_vertex(c, ns);
                inserted = 1;
            }
        }
        if (inserted) {
            if (n > best_n) {
                best_n = n;
                snap_save(&best);
            }
            continue;
        }
        snap_save(&tmp);
        int k = 1 + rndint(2);
        for (int j = 0; j < k && n > 2; j++) remove_vertex(rndint(n));
        if (!diam_ok()) snap_load(&tmp);
        if (n < best_n - 3) snap_load(&best);
    }

    emit_state(best.n, best.deg, best.adj);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _start_graph(d, D, deadline, seed):
    """Best of the algebraic constructions that fit the deadline, or K_{d,d}."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq
    return best


def _haar_search(d, seed, m_lo, budget):
    """Search abelian Haar graphs of degree d, diameter 3, with per-side order m >= m_lo.

    Returns (n, edges) for a valid graph, or None.
    """
    if d < 3 or d > 32:
        return None
    m_hi = d * (d - 1) + 1
    if m_lo > m_hi:
        return None
    out = lib.run_c(HAAR_C, [d, 3, seed, round(budget, 2), m_lo],
                    stdin_graph=None, timeout=budget + 8.0)
    n, edges = lib.parse_graph_text(out)
    if n > 0 and lib.is_valid(n, edges, d, 3):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _start_graph(d, D, t0 + 0.15 * time_limit, seed)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    def usable():
        return 0.85 * time_limit - 3.0 - (time.monotonic() - t0)

    # Bold branch (diameter 3): difference-cover Haar graphs, beyond the parent's order.
    if D == 3 and usable() > 4.0:
        try:
            cand = _haar_search(d, seed, best[0] // 2 + 1, 0.5 * usable())
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except (RuntimeError, ValueError):
            pass

    # Insertion engine on whatever start we have (safe: it only keeps valid graphs).
    rem = usable()
    if rem >= 1.5:
        budget = max(0.5, rem - 1.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
