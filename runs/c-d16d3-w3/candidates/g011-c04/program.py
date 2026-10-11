"""Combined diameter-3 search: arc-extended and conic starts, then a C engine.

Starts (each validated with lib.is_valid): conic blow-up of PG(2,q), arc-extended PG(2,q)
incidence graphs, Araujo-Pardo/Lopez and projective-plane graphs when they apply, W(q) for
D >= 4, and K_{d,d} as the fallback. The Moore-bound starts return at once.

C engine (run on the top two distinct starts, budget split between them):
  1. Dominating-set insertion: a new vertex on one side is joined to at most d spare
     vertices on the other side whose radius-(D-1) balls cover every current vertex, so
     its eccentricity is at most D and existing distances can only shrink.
  2. Ruin-and-recreate: remove one or two random vertices if the diameter stays <= D,
     otherwise restore. The best graph seen is kept and reloaded after a large drop.
  3. Grow-two annealing: add an adjacent pair of vertices by stealing degree-preserving
     edges, then anneal degree-preserving double-edge swaps until no pair is farther
     than D apart. Tried whenever insertion stalls.

Every output is re-validated in Python, and a valid fallback is always returned.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define INF 100
typedef uint64_t u64;

static int D_, DEG_, CAP, W, n;
static int *deg, *adj, *col, *qbuf, *cand, *dv, *sel, *bsel, *used, *mark;
static int stamp_ctr = 0;
static int balls_ok = 0;
static unsigned char *dist;
static u64 *ball, *unc, *rA, *rB;
static uint64_t rs = 88172645463325252ULL;

typedef struct { int n; int *deg; int *adj; int *col; } Snap;
static Snap best_s, tmp_s, sv_s;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int pc64(u64 x) { return __builtin_popcountll(x); }

#define AD(v, k) adj[(size_t)(v) * DEG_ + (k)]
#define DIST(a, b) dist[(size_t)(a) * CAP + (b)]

static void add_edge(int a, int b) {
    AD(a, deg[a]) = b; deg[a]++;
    AD(b, deg[b]) = a; deg[b]++;
}

static void del_nbr(int u, int x) {
    for (int j = 0; j < deg[u]; j++) {
        if (AD(u, j) == x) {
            AD(u, j) = AD(u, deg[u] - 1);
            deg[u]--;
            return;
        }
    }
}

static int has_edge(int u, int v) {
    for (int j = 0; j < deg[u]; j++)
        if (AD(u, j) == v) return 1;
    return 0;
}

static void recompute_dist(void) {
    for (int s = 0; s < n; s++) {
        unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++) row[x] = INF;
        row[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int u = qbuf[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = AD(u, k);
                if (row[v] == INF) {
                    row[v] = (unsigned char)(row[u] + 1);
                    qbuf[t++] = v;
                }
            }
        }
    }
    balls_ok = 0;
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
    int Wn = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        u64 *b = ball + (size_t)v * W;
        for (int w = 0; w < Wn; w++) b[w] = 0;
        const unsigned char *row = dist + (size_t)v * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] <= D_ - 1) b[x >> 6] |= 1ULL << (x & 63);
    }
    balls_ok = 1;
}

/* Greedy cover of all current vertices by radius-(D-1) balls of colour-c vertices with spare degree.
   Returns the number of chosen neighbours (written to bsel) or -1. */
static int try_insert(int c, int restarts) {
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == c && deg[v] < DEG_) cand[nc++] = v;
    if (nc == 0) return -1;
    int Wn = (n + 63) >> 6;
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < Wn; w++) unc[w] = 0;
        for (int x = 0; x < n; x++) unc[x >> 6] |= 1ULL << (x & 63);
        int uncount = n, ns = 0;
        for (int i = 0; i < nc; i++) used[i] = 0;
        while (uncount > 0 && ns < DEG_) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used[i]) continue;
                const u64 *b = ball + (size_t)cand[i] * W;
                int g = 0;
                for (int w = 0; w < Wn; w++) g += pc64(b[w] & unc[w]);
                if (g == 0) continue;
                long long key = (long long)g * 4096 + (long long)(rnd() % 4096);
                if (key > bkey) { bkey = key; bi = i; }
            }
            if (bi < 0) break;
            used[bi] = 1;
            sel[ns++] = cand[bi];
            const u64 *b = ball + (size_t)cand[bi] * W;
            uncount = 0;
            for (int w = 0; w < Wn; w++) {
                unc[w] &= ~b[w];
                uncount += pc64(unc[w]);
            }
        }
        if (uncount == 0 && ns > 0) {
            for (int k = 0; k < ns; k++) bsel[k] = sel[k];
            return ns;
        }
    }
    return -1;
}

static void insert_vertex(int c, int ns) {
    int v = n++;
    col[v] = 1 - c;
    deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(v, bsel[k]);
    for (int x = 0; x < v; x++) {
        int m = INF;
        for (int k = 0; k < ns; k++) {
            int t = DIST(x, bsel[k]);
            if (t < m) m = t;
        }
        int dd = m + 1;
        if (dd > INF) dd = INF;
        dv[x] = dd;
    }
    for (int x = 0; x < v; x++) {
        DIST(x, v) = (unsigned char)dv[x];
        DIST(v, x) = (unsigned char)dv[x];
    }
    DIST(v, v) = 0;
    for (int x = 0; x < v; x++) {
        unsigned char *row = dist + (size_t)x * CAP;
        for (int y = 0; y < v; y++) {
            int t = dv[x] + dv[y];
            if (t > INF) t = INF;
            if (t < row[y]) row[y] = (unsigned char)t;
        }
    }
    balls_ok = 0;
}

static void remove_vertex(int r) {
    int last = n - 1;
    for (int k = 0; k < deg[r]; k++) del_nbr(AD(r, k), r);
    deg[r] = 0;
    if (r != last) {
        for (int k = 0; k < deg[last]; k++) {
            int u = AD(last, k);
            for (int j = 0; j < deg[u]; j++) {
                if (AD(u, j) == last) { AD(u, j) = r; break; }
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

static void emit(const Snap *s) {
    long m = 0;
    for (int v = 0; v < s->n; v++) m += s->deg[v];
    printf("%d %ld\n", s->n, m / 2);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++) {
            int u = s->adj[(size_t)v * DEG_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

/* Number of unordered pairs at distance > D_, via bitset reach sets. */
static long bad_count(void) {
    int Wn = (n + 63) >> 6;
    u64 *cur = rA, *nxt = rB;
    for (int v = 0; v < n; v++) {
        u64 *r = cur + (size_t)v * W;
        for (int w = 0; w < Wn; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D_; it++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < Wn; w++) dst[w] = src[w];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *s = cur + (size_t)AD(v, k) * W;
                for (int w = 0; w < Wn; w++) dst[w] |= s[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const u64 *s = cur + (size_t)v * W;
        for (int w = 0; w < Wn; w++) c += pc64(s[w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Add an adjacent pair (x on side 0, y on side 1) by stealing degree-preserving edges,
   then anneal swaps until no pair is farther than D_. Restores the graph on failure. */
static int grow_two(long steps, double until) {
    if (n + 2 >= CAP) return 0;
    snap_save(&sv_s);
    int old = n;
    int x = n, y = n + 1;
    n += 2;
    deg[x] = 0; deg[y] = 0;
    col[x] = 0; col[y] = 1;
    add_edge(x, y);
    int st = ++stamp_ctr;
    mark[x] = st; mark[y] = st;
    int k = 0;
    for (int tries = 0; k < DEG_ - 1 && tries < 20000; tries++) {
        int a = rndint(old);
        if (col[a] != 0 || mark[a] == st || deg[a] == 0) continue;
        int b = AD(a, rndint(deg[a]));
        if (mark[b] == st) continue;
        del_nbr(a, b); del_nbr(b, a);
        add_edge(x, b);
        add_edge(y, a);
        mark[a] = st; mark[b] = st;
        k++;
    }
    if (k < DEG_ - 1) {
        snap_load(&sv_s);
        return 0;
    }
    long bad = bad_count();
    double T = 0.6;
    for (long it = 0; bad > 0 && it < steps; it++) {
        if ((it & 31) == 0 && now() > until) break;
        int v = rndint(n);
        if (deg[v] == 0) continue;
        int u = AD(v, rndint(deg[v]));
        int s = rndint(n);
        if (s == v || col[s] != col[v] || deg[s] == 0) continue;
        int t = AD(s, rndint(deg[s]));
        if (t == u || has_edge(v, t) || has_edge(s, u)) continue;
        del_nbr(v, u); del_nbr(u, v);
        del_nbr(s, t); del_nbr(t, s);
        add_edge(v, t);
        add_edge(s, u);
        long nb = bad_count();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_nbr(v, t); del_nbr(t, v);
            del_nbr(s, u); del_nbr(u, s);
            add_edge(v, u);
            add_edge(s, t);
        }
        T *= 0.999;
        if (T < 0.05) T = 0.6;
    }
    if (bad == 0) {
        recompute_dist();
        if (diam_ok()) return 1;
    }
    snap_load(&sv_s);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    DEG_ = d;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0) nin = 0;
    if (min_ < 0) min_ = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 2));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 2));
    int me = 0;
    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= nin || b >= nin || a == b) continue;
        eu[me] = a; ev[me] = b; me++;
    }
    if (nin == 0) {
        nin = 2;
        me = 1;
        eu[0] = 0; ev[0] = 1;
    }

    CAP = nin + 1000;
    W = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG_, sizeof(int));
    col = malloc(sizeof(int) * (size_t)CAP);
    qbuf = malloc(sizeof(int) * (size_t)CAP);
    cand = malloc(sizeof(int) * (size_t)CAP);
    dv = malloc(sizeof(int) * (size_t)CAP);
    used = malloc(sizeof(int) * (size_t)CAP);
    mark = calloc((size_t)CAP, sizeof(int));
    sel = malloc(sizeof(int) * (size_t)(DEG_ + 2));
    bsel = malloc(sizeof(int) * (size_t)(DEG_ + 2));
    dist = malloc((size_t)CAP * CAP);
    ball = calloc((size_t)CAP * W, sizeof(u64));
    unc = calloc((size_t)W, sizeof(u64));
    rA = calloc((size_t)CAP * W, sizeof(u64));
    rB = calloc((size_t)CAP * W, sizeof(u64));

    n = nin;
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int i = 0; i < me; i++)
        if (deg[eu[i]] < DEG_ && deg[ev[i]] < DEG_) add_edge(eu[i], ev[i]);

    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int u = qbuf[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = AD(u, k);
                if (col[v] < 0) { col[v] = 1 - col[u]; qbuf[t++] = v; }
                else if (col[v] == col[u]) bip = 0;
            }
        }
    }
    recompute_dist();

    snap_init(&best_s);
    snap_init(&tmp_s);
    snap_init(&sv_s);
    if (!bip || !diam_ok()) {
        emit_fallback:
        snap_save(&best_s);
        emit(&best_s);
        return 0;
    }
    snap_save(&best_s);
    int best_n = n;

    double t0 = now();
    long fails = 0;
    while (now() - t0 < tl) {
        if (n + 2 >= CAP) break;
        if (!balls_ok) build_balls();
        int inserted = 0;
        int first = rndint(2);
        for (int t = 0; t < 2 && !inserted; t++) {
            int c = (t == 0) ? first : 1 - first;
            int ns = try_insert(c, 4);
            if (ns > 0) {
                insert_vertex(c, ns);
                inserted = 1;
            }
        }
        if (inserted) {
            fails = 0;
            if (n > best_n) { best_n = n; snap_save(&best_s); }
            continue;
        }
        fails++;
        if (fails % 6 == 0) {
            if (grow_two(3000, t0 + tl)) {
                fails = 0;
                if (n > best_n) { best_n = n; snap_save(&best_s); }
                continue;
            }
        }
        snap_save(&tmp_s);
        int k = 1 + rndint(2);
        for (int j = 0; j < k && n > 4; j++) remove_vertex(rndint(n));
        if (!diam_ok()) snap_load(&tmp_s);
        if (n < best_n - 3) snap_load(&best_s);
    }
    emit(&best_s);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Moore graph (projective plane) or Araujo-Pardo/Lopez graph for D = 3."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 40, deadline)
        SB = _greedy_side(m, s, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    rng = random.Random(seed * 7919 + d)

    cands = []
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    for g in starts(d, D, t0 + 0.12 * time_limit, rng):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if not cands:
        return 1, []

    cands.sort(key=lambda g: -g[0])
    best = cands[0]
    moore = lib.moore_bound(d, D)
    tops = cands[:2] if time_limit >= 20 else cands[:1]

    for i, g in enumerate(tops):
        if g[0] >= moore:
            continue
        remaining = hard_end - time.monotonic() - 1.0
        share = remaining / (len(tops) - i)
        if share < 1.0:
            break
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 31 + i, f"{share:.2f}"],
                            stdin_graph=g, timeout=share + 8.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
