import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW (bold) construction for D = 3: cyclic Haar graphs from difference covers.
#
# Haar graph H(m, S): parts a_i, b_j (i, j in Z_m), a_i ~ b_{i+s} for s in S, |S| = d.
# It is d-regular and bipartite with 2m vertices. Its diameter is at most 3 exactly
# when S - S covers all of Z_m:
#   a_x to a_y (and b to b): distance 2 iff y - x in S - S;
#   a_x to b_y: distance 1 if y - x in S, else 3 since (S - S) + S = Z_m.
# Since |S - S| <= d(d-1) + 1, m <= d^2 - d + 1 (order 2(d^2-d+1), the Moore bound).
# A perfect difference set would give that bound; for d = 16 it is not known to exist,
# so we search for large m with a 16-element difference cover by simulated annealing.
#
# Old fallback path (kept): Araujo-style PG(2,q) arc extensions, then the
# insertion engine (C_SOURCE below).
# ----------------------------------------------------------------------------

C_COVER = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXM 4096
#define MAXK 64

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int M, K;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int zeros;

static void adjust(int x, int sgn) {
    if (sgn > 0) { if (cnt[x] == 0) zeros--; cnt[x]++; }
    else { cnt[x]--; if (cnt[x] == 0) zeros++; }
}

/* Add (sgn=+1) or remove (sgn=-1) all ordered differences involving position idx with value val. */
static void apply_elem(int idx, int val, int sgn) {
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        int x = val - S[j]; if (x < 0) x += M;
        int y = S[j] - val; if (y < 0) y += M;
        adjust(x, sgn);
        adjust(y, sgn);
    }
}

/* One annealing run. Returns 1 and leaves S valid if S - S covers Z_M. */
static int anneal(double deadline, long steps, double T0, double T1) {
    memset(inS, 0, sizeof(int) * (size_t)M);
    S[0] = 0; inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int v;
        do { v = rndint(M); } while (inS[v]);
        S[i] = v; inS[v] = 1;
    }
    for (int x = 0; x < M; x++) cnt[x] = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) {
                int x = S[i] - S[j]; if (x < 0) x += M;
                cnt[x]++;
            }
    zeros = 0;
    for (int x = 1; x < M; x++) if (cnt[x] == 0) zeros++;
    if (zeros == 0) return 1;

    double T = T0;
    for (long st = 0; st < steps; st++) {
        if ((st & 4095) == 0 && now() > deadline) break;
        if ((st & 1023) == 0) T = T0 * pow(T1 / T0, (double)st / (double)steps);
        int idx = 1 + rndint(K - 1);
        int old = S[idx];
        int y;
        do { y = rndint(M); } while (inS[y]);
        int z0 = zeros;
        apply_elem(idx, old, -1);
        S[idx] = y;
        apply_elem(idx, y, +1);
        int delta = zeros - z0;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            inS[old] = 0; inS[y] = 1;
            if (zeros == 0) return 1;
        } else {
            apply_elem(idx, y, -1);
            S[idx] = old;
            apply_elem(idx, old, +1);
        }
    }
    return zeros == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    int d = atoi(argv[1]);
    rs ^= (unsigned long long)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tl = atof(argv[3]);
    int mlo = atoi(argv[4]), mhi = atoi(argv[5]);
    K = d;
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    if (mlo < K + 1) mlo = K + 1;

    double t0 = now();
    double slice = tl * 0.12;
    if (slice < 0.5) slice = 0.5;
    int best_m = 0, fails = 0;
    int bestS[MAXK];

    for (int m = mlo; m <= mhi; m++) {
        double tn = now();
        if (tn - t0 >= tl) break;
        M = m;
        double mdead = tn + slice;
        if (mdead > t0 + tl) mdead = t0 + tl;
        int ok = 0;
        while (!ok && now() < mdead) ok = anneal(mdead, 3000000L, 1.2, 0.12);
        if (ok) {
            best_m = m;
            fails = 0;
            for (int i = 0; i < K; i++) bestS[i] = S[i];
        } else if (++fails >= 3) {
            break;
        }
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_m, K);
    for (int i = 0; i < K; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""


def _cover_graph(d, budget, seed):
    """Run the difference-cover search and return the Haar graph (n, edges), or None."""
    kmax = d * d - d + 1
    mlo = max(d + 1, int(0.6 * kmax))
    text = lib.run_c(C_COVER, [d, seed, round(budget, 2), mlo, kmax],
                     stdin_graph=None, timeout=budget + 5.0)
    toks = text.split()
    if len(toks) < 2:
        return None
    m, k = int(toks[0]), int(toks[1])
    if m <= 0 or k != d:
        return None
    S = [int(x) for x in toks[2:2 + k]]
    if len(S) != k or len(set(S)) != k or any(not (0 <= s < m) for s in S):
        return None
    n = 2 * m
    edges = [(i, m + (i + s) % m) for i in range(m) for s in S]
    return n, edges


# ----------------------------------------------------------------------------
# Parent code (fallback path): arc-extended projective plane incidence graphs.
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
# C engine (fallback): dominating-set insertion with ruin-and-recreate.
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


def _parent_path(d, D, seed, t_start, remaining):
    """Previous pipeline: algebraic start graph, then insertion search in C. Returns a valid graph."""
    best = _start_graph(d, D, t_start + 0.2 * remaining, seed)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    rem = remaining - (time.monotonic() - t_start)
    if rem < 2.0:
        return best
    budget = max(0.5, 0.85 * rem - 1.5)
    if best[0] < 40:
        budget = min(budget, 3.0)
    timeout = max(budget + 1.0, 0.95 * rem)

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=timeout)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except (RuntimeError, ValueError):
        pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    end = t0 + time_limit - 2.0  # safety margin before the hard limit
    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    # New construction: cyclic Haar graphs from difference covers (diameter 3 only).
    if D == 3 and d >= 3:
        try:
            budget = max(1.0, 0.60 * time_limit - 2.0)
            g = _cover_graph(d, budget, seed)
            if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        except (RuntimeError, ValueError):
            pass

    # Previous pipeline on the remaining time; keep whichever is larger.
    remaining = end - time.monotonic()
    if remaining > 3.0:
        try:
            cand = _parent_path(d, D, seed, time.monotonic(), remaining)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
