import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bad-pair simulated annealing with grow-on-success.
#
# State: a bipartite graph (sides fixed per vertex) with max degree d. Cost is
# the number of unordered vertex pairs at distance > D, computed with
# bitset BFS. Moves: degree-preserving 2-switches, edge additions and removals,
# and vertex insertion. Whenever cost hits zero the current order is recorded
# and a new vertex is inserted with a forced accept. Undo uses an op log.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXLOG 8192
#define MAXE (MAXN * MAXDEG / 2)
#define STAG 20000

typedef struct { int type, u, v; } Op;

static int dd, DD;
static int n_;
static int side_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXDEG];
static uint64_t rA[MAXN][MAXW], rB[MAXN][MAXW];
static Op log_[MAXLOG];
static int nlog_;
static int best_n, best_m;
static int bs_[MAXN];
static int bu_[MAXE], bv_[MAXE];
static uint64_t rs_;

static uint64_t xr(void) {
    rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17;
    return rs_;
}
static int rnd(int k) { return (int)(xr() % (uint64_t)k); }
static double urand(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static void log_push(int t, int u, int v) {
    if (nlog_ < MAXLOG) {
        log_[nlog_].type = t; log_[nlog_].u = u; log_[nlog_].v = v;
        nlog_++;
    }
}

static void raw_add(int u, int v) {
    nb_[u][deg_[u]++] = v;
    nb_[v][deg_[v]++] = u;
}

static void raw_del(int u, int v) {
    for (int i = 0; i < deg_[u]; i++)
        if (nb_[u][i] == v) { nb_[u][i] = nb_[u][--deg_[u]]; break; }
    for (int i = 0; i < deg_[v]; i++)
        if (nb_[v][i] == u) { nb_[v][i] = nb_[v][--deg_[v]]; break; }
}

static void add_e(int u, int v) { raw_add(u, v); log_push(0, u, v); }
static void del_e(int u, int v) { raw_del(u, v); log_push(1, u, v); }

static int new_vertex(int s) {
    int x = n_++;
    side_[x] = s;
    deg_[x] = 0;
    log_push(2, x, 0);
    return x;
}

static void undo_all(void) {
    while (nlog_ > 0) {
        Op o = log_[--nlog_];
        if (o.type == 0) raw_del(o.u, o.v);
        else if (o.type == 1) raw_add(o.u, o.v);
        else {
            while (deg_[o.u] > 0) raw_del(o.u, nb_[o.u][0]);
            n_--;
        }
    }
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg_[u]; i++) if (nb_[u][i] == v) return 1;
    return 0;
}

/* mode 0: deg < dd; mode 1: deg > 0. Returns -1 if no vertex found. */
static int pick(int s, int mode) {
    for (int t = 0; t < 200; t++) {
        int v = rnd(n_);
        if (side_[v] != s) continue;
        if (mode == 0 && deg_[v] >= dd) continue;
        if (mode == 1 && deg_[v] == 0) continue;
        return v;
    }
    return -1;
}

static int move_switch(void) {
    int a = pick(0, 1), c = pick(0, 1);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = nb_[a][rnd(deg_[a])];
    int e = nb_[c][rnd(deg_[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    del_e(a, b); del_e(c, e);
    add_e(a, e); add_e(c, b);
    return 1;
}

static int move_add(void) {
    int x = pick(0, 0), y = pick(1, 0);
    if (x < 0 || y < 0 || has_edge(x, y)) return 0;
    add_e(x, y);
    return 1;
}

static int move_remove(void) {
    int a = pick(0, 1);
    if (a < 0) return 0;
    int b = nb_[a][rnd(deg_[a])];
    del_e(a, b);
    return 1;
}

/* Insert a vertex on a random side joined to up to dd vertices of the other side.
   Full neighbours give up one edge to the new vertex's side. */
static int move_insert(void) {
    if (n_ >= MAXN - 1 || n_ < 2) return 0;
    int s = rnd(2);
    int x = new_vertex(s);
    int cand = 0;
    for (int v = 0; v < n_ - 1; v++) if (side_[v] == 1 - s) cand++;
    int k = dd < cand ? dd : cand;
    int chosen[MAXDEG];
    int nc = 0;
    for (int tries = 0; nc < k && tries < 2000; tries++) {
        int y = rnd(n_ - 1);
        if (side_[y] != 1 - s) continue;
        int dup = 0;
        for (int i = 0; i < nc; i++) if (chosen[i] == y) { dup = 1; break; }
        if (!dup) chosen[nc++] = y;
    }
    for (int i = 0; i < nc; i++) {
        int y = chosen[i];
        if (deg_[y] >= dd) {
            int z = nb_[y][rnd(deg_[y])];
            del_e(y, z);
        }
        add_e(x, y);
    }
    return 1;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DD. Zero means valid. */
static long cost_full(void) {
    int n = n_;
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) rA[v][w] = 0;
        rA[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    uint64_t (*cur)[MAXW] = rA;
    uint64_t (*nxt)[MAXW] = rB;
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                int u = nb_[v][i];
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
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_best(void) {
    best_n = n_;
    best_m = 0;
    for (int v = 0; v < n_; v++) {
        bs_[v] = side_[v];
        for (int i = 0; i < deg_[v]; i++) {
            int u = nb_[v][i];
            if (u > v && best_m < MAXE) {
                bu_[best_m] = v; bv_[best_m] = u; best_m++;
            }
        }
    }
}

static void restore_best(void) {
    for (int v = 0; v < MAXN; v++) deg_[v] = 0;
    n_ = best_n;
    for (int v = 0; v < n_; v++) side_[v] = bs_[v];
    for (int e = 0; e < best_m; e++) raw_add(bu_[e], bv_[e]);
    nlog_ = 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs_ = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs_ == 0) rs_ = 1;
    double limit = atof(argv[4]);
    if (dd < 1 || dd > MAXDEG || DD < 1) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN || m < 0) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    int bad = 0;
    for (int i = 0; i < m && !bad; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            deg_[u] >= dd || deg_[v] >= dd || has_edge(u, v)) {
            bad = 1;
            break;
        }
        raw_add(u, v);
    }
    if (bad) { printf("0 0\n"); return 0; }

    /* 2-colour the start graph; a conflict means it is not bipartite. */
    static int queue_[MAXN];
    for (int v = 0; v < n; v++) side_[v] = -1;
    for (int s = 0; s < n && !bad; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int i = 0; i < deg_[u]; i++) {
                int w = nb_[u][i];
                if (side_[w] < 0) { side_[w] = 1 - side_[u]; queue_[qt++] = w; }
                else if (side_[w] == side_[u]) { bad = 1; break; }
            }
            if (bad) break;
        }
    }
    if (bad) { printf("0 0\n"); return 0; }

    best_n = 0;
    nlog_ = 0;
    long cur = cost_full();
    if (cur == 0) save_best();

    clock_t t0 = clock();
    double T = 1.0;
    long since = 0, it = 0;
    while (1) {
        if ((it & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= limit) break;
        it++;
        nlog_ = 0;
        if (cur == 0) {
            if (n_ >= MAXN - 1) break;
            if (move_insert()) {
                cur = cost_full();
                nlog_ = 0;
                if (cur == 0 && n_ > best_n) save_best();
                T = 1.0;
                since = 0;
            }
            continue;
        }
        int mv = rnd(100), ok;
        if (mv < 50) ok = move_switch();
        else if (mv < 75) ok = move_add();
        else if (mv < 90) ok = move_remove();
        else ok = move_insert();
        since++;
        if (!ok) { nlog_ = 0; continue; }
        long nc = cost_full();
        long dl = nc - cur;
        if (dl <= 0 || urand() < exp(-(double)dl / T)) {
            cur = nc;
            nlog_ = 0;
            if (cur == 0 && n_ > best_n) save_best();
        } else {
            undo_all();
        }
        if (T > 0.3) T *= 0.9995;
        if (since > STAG && best_n > 0) {
            restore_best();
            cur = 0;
            T = 1.0;
            since = 0;
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", bu_[e], bv_[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. A new vertex per chosen point (joined
# to its q+1 lines) and per chosen line (joined to its q+1 points), with every
# old vertex receiving at most s new edges. Diameter stays 3.
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained selection."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus new A-vertices (per SA point) and B-vertices (per SB line)."""
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
# Generalized quadrangle W(q) baseline (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

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

    # Constructive starts (Python, short budget).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to search for.
    if best_n >= lib.moore_bound(d, D):
        return best

    # C repair/growth search, starting from the best valid graph found so far.
    left = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if left >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{left:.2f}"], stdin_graph=best,
                            timeout=max(1.0, 0.92 * time_limit - (time.monotonic() - t0)))
            consider(*lib.parse_graph_text(out))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
