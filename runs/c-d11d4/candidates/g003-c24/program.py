import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for this island: a two-phase C search.
#
# Phase 1 is the parent's rarest-first cover growth. It runs until stuck.
# Phase 2 is new: simulated annealing on a fixed-size bipartite graph.
#   * When a vertex is missing, it is added with the neighbourhood that
#     covers the most vertices (partial cover), and the spare degree is filled.
#   * The cost is the number of vertex pairs at distance > D.
#   * Moves are degree-preserving double-edge swaps across the bipartition,
#     plus endpoint shifts that move a spare slot to another vertex.
#   * Every zero-cost state is verified and snapshotted, so the output is
#     always a valid graph, and it is the input graph if nothing improves.
# Python checks the returned graph with lib.is_valid, and falls back to the best
# valid start (or K_{d,d}) otherwise.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6144
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define ATTEMPTS 40
#define LS_ITERS 150
#define EPOCH_S 2.0

typedef uint64_t u64;

static int dd, DD, n, W;
static int color[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static u64 ball[MAXN][MAXW];
static u64 tmpb[MAXN][MAXW];
static int cntx[MAXN];
static int cand[MAXN];
static int ncand;
static char taken[MAXN];
static int chosen[MAXD];
static int nch;
static u64 rs = 88172645463325252ULL;
static double deadline_s;
static int n_in, m_in;
static int eu[MAXE], ev[MAXE];
static int bn, bm;
static int bu[MAXE], bv[MAXE];
static int mv_type, ma, mb, mc, me, mvv;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int k) {
    return (int)(rnd64() % (u64)k);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int count_bits(const u64 *a) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(a[w]);
    return c;
}

static int count_union(const u64 *a, const u64 *b) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(a[w] | b[w]);
    return c;
}

/* ball[v] = all vertices within distance r of v. */
static void compute_balls(int r) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(ball[v], 0, sizeof(u64) * W);
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            u64 *t = tmpb[v];
            memcpy(t, ball[v], sizeof(u64) * W);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *bu_ = ball[adj[v][k]];
                for (int w = 0; w < W; w++) t[w] |= bu_[w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(ball[v], tmpb[v], sizeof(u64) * W);
    }
}

static int bipartite_color(void) {
    static int queue[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (color[v] == -1) {
                    color[v] = 1 - color[u];
                    queue[qt++] = v;
                } else if (color[v] == color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Greedy rarest-first cover of all n vertices by at most dd candidate balls. */
static int greedy_cover(void) {
    u64 cov[MAXW];
    for (int x = 0; x < n; x++) cntx[x] = 0;
    for (int i = 0; i < ncand; i++) {
        const u64 *b = ball[cand[i]];
        for (int w = 0; w < W; w++) {
            u64 bits = b[w];
            while (bits) {
                cntx[(w << 6) + __builtin_ctzll(bits)]++;
                bits &= bits - 1;
            }
        }
    }
    memset(cov, 0, sizeof(u64) * W);
    nch = 0;
    int covered = 0;
    while (covered < n && nch < dd) {
        int bx = -1, bc = 0x7fffffff, ties = 0;
        for (int x = 0; x < n; x++) {
            if ((cov[x >> 6] >> (x & 63)) & 1ULL) continue;
            if (cntx[x] <= 0) return 0;
            if (cntx[x] < bc) {
                bc = cntx[x];
                bx = x;
                ties = 1;
            } else if (cntx[x] == bc) {
                ties++;
                if (rnd_int(ties) == 0) bx = x;
            }
        }
        int noisy = (rnd_int(100) < 15);
        int bs = -1;
        long long bsc = -1;
        for (int i = 0; i < ncand; i++) {
            int s = cand[i];
            if (taken[s]) continue;
            if (!((ball[s][bx >> 6] >> (bx & 63)) & 1ULL)) continue;
            long long sc;
            if (noisy) {
                sc = rnd_int(1 << 30);
            } else {
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(ball[s][w] & ~cov[w]);
                sc = (long long)g * 4096 + rnd_int(4096);
            }
            if (sc > bsc) {
                bsc = sc;
                bs = s;
            }
        }
        if (bs < 0) return 0;
        taken[bs] = 1;
        chosen[nch++] = bs;
        for (int w = 0; w < W; w++) {
            u64 bits = ball[bs][w];
            covered += pc64(bits & ~cov[w]);
            cov[w] |= bits;
            while (bits) {
                cntx[(w << 6) + __builtin_ctzll(bits)]--;
                bits &= bits - 1;
            }
        }
    }
    return covered == n;
}

/* Swap-based local search on a full set of dd chosen candidates. */
static int cover_ls(void) {
    u64 cc[MAXW], rest[MAXW];
    for (int it = 0; it <= LS_ITERS; it++) {
        memset(cc, 0, sizeof(u64) * W);
        for (int j = 0; j < nch; j++)
            for (int w = 0; w < W; w++) cc[w] |= ball[chosen[j]][w];
        int cur = n - count_bits(cc);
        if (cur == 0) return 1;
        if (it == LS_ITERS) break;
        int i = rnd_int(nch);
        memset(rest, 0, sizeof(u64) * W);
        for (int j = 0; j < nch; j++) {
            if (j == i) continue;
            for (int w = 0; w < W; w++) rest[w] |= ball[chosen[j]][w];
        }
        int bc = -1, bu2 = 0x7fffffff;
        for (int t = 0; t < 60; t++) {
            int c = cand[rnd_int(ncand)];
            if (taken[c]) continue;
            int u = n - count_union(rest, ball[c]);
            if (u < bu2) {
                bu2 = u;
                bc = c;
            }
        }
        if (bc >= 0 && bu2 <= cur) {
            taken[chosen[i]] = 0;
            chosen[i] = bc;
            taken[bc] = 1;
        }
    }
    return 0;
}

static void add_vertex(int c) {
    int v = n++;
    color[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        adj[s][deg[s]++] = v;
        adj[v][deg[v]++] = s;
    }
}

static int try_add(void) {
    int first = rnd_int(2);
    for (int t = 0; t < 2; t++) {
        int c = (t == 0) ? first : 1 - first;
        ncand = 0;
        for (int v = 0; v < n; v++)
            if (color[v] == 1 - c && deg[v] < dd) cand[ncand++] = v;
        if (ncand == 0) continue;
        for (int att = 0; att < ATTEMPTS; att++) {
            if (now_s() > deadline_s) return 0;
            for (int i = 0; i < ncand; i++) taken[cand[i]] = 0;
            int ok = greedy_cover();
            if (!ok && nch == dd) ok = cover_ls();
            if (ok) {
                add_vertex(c);
                return 1;
            }
        }
    }
    return 0;
}

/* Full validity check of the current state (balls recomputed at radius DD). */
static int check_state(void) {
    compute_balls(DD);
    for (int v = 0; v < n; v++) {
        if (deg[v] > dd) return 0;
        if (count_bits(ball[v]) != n) return 0;
        for (int k = 0; k < deg[v]; k++)
            if (color[adj[v][k]] == color[v]) return 0;
    }
    return 1;
}

/* Number of unordered pairs at distance > DD (unreachable pairs included). */
static long long total_cost(void) {
    compute_balls(DD);
    long long bad = 0;
    for (int v = 0; v < n; v++) bad += n - count_bits(ball[v]);
    return bad / 2;
}

static void snap(void) {
    bn = n;
    bm = 0;
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v && bm < MAXE) {
                bu[bm] = v;
                bv[bm] = adj[v][k];
                bm++;
            }
}

static void try_snap(void) {
    if (n <= bn) return;
    if (check_state()) snap();
}

static void print_best(void) {
    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            break;
        }
    for (int k = 0; k < deg[b]; k++)
        if (adj[b][k] == a) {
            adj[b][k] = adj[b][--deg[b]];
            break;
        }
}

/* Degree-preserving double-edge swap across the bipartition. */
static int do_swap(void) {
    for (int tries = 0; tries < 50; tries++) {
        int a = rnd_int(n);
        if (deg[a] == 0) continue;
        int b = adj[a][rnd_int(deg[a])];
        int c = rnd_int(n);
        if (c == a || color[c] != color[a] || deg[c] == 0) continue;
        int e = adj[c][rnd_int(deg[c])];
        if (e == b || has_edge(a, e) || has_edge(c, b)) continue;
        del_one(a, b);
        del_one(c, e);
        add_edge(a, e);
        add_edge(c, b);
        mv_type = 0;
        ma = a;
        mb = b;
        mc = c;
        me = e;
        return 1;
    }
    return 0;
}

/* Move the endpoint b of edge (a,b) to a vertex v with spare degree and the same colour. */
static int do_shift(void) {
    static int spare[2][MAXN];
    int ns[2] = {0, 0};
    for (int v = 0; v < n; v++)
        if (deg[v] < dd) spare[color[v]][ns[color[v]]++] = v;
    for (int tries = 0; tries < 50; tries++) {
        int a = rnd_int(n);
        if (deg[a] == 0) continue;
        int b = adj[a][rnd_int(deg[a])];
        int cb = color[b];
        if (ns[cb] == 0) return 0;
        int v = spare[cb][rnd_int(ns[cb])];
        if (v == b || v == a || has_edge(a, v)) continue;
        del_one(a, b);
        add_edge(a, v);
        mv_type = 1;
        ma = a;
        mb = b;
        mvv = v;
        return 1;
    }
    return 0;
}

static void undo_move(void) {
    if (mv_type == 0) {
        del_one(ma, me);
        del_one(mc, mb);
        add_edge(ma, mb);
        add_edge(mc, me);
    } else {
        del_one(ma, mvv);
        add_edge(ma, mb);
    }
}

/* Fill spare degrees with random edges between spare vertices of opposite colours.
   Adding edges never increases the cost. */
static void fill_spare(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= dd) continue;
        if (color[v] == 0) A[na++] = v;
        else B[nb++] = v;
    }
    long long lim = 30LL * (na + nb) + 1000;
    for (long long t = 0; t < lim && na > 0 && nb > 0; t++) {
        int i = rnd_int(na), j = rnd_int(nb);
        int a = A[i], b = B[j];
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        if (deg[a] >= dd) A[i] = A[--na];
        if (deg[b] >= dd) B[j] = B[--nb];
    }
}

/* Choose up to dd spare opposite-colour vertices greedily by new coverage (radius DD-1 balls). */
static void partial_cover(int c) {
    u64 cov[MAXW];
    memset(cov, 0, sizeof(u64) * W);
    nch = 0;
    ncand = 0;
    for (int v = 0; v < n; v++)
        if (color[v] == 1 - c && deg[v] < dd) cand[ncand++] = v;
    for (int i = 0; i < ncand; i++) taken[cand[i]] = 0;
    while (nch < dd) {
        int bs = -1, bg = 0;
        for (int i = 0; i < ncand; i++) {
            int s = cand[i];
            if (taken[s]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(ball[s][w] & ~cov[w]);
            if (g > bg || (g == bg && bs >= 0 && g > 0 && rnd_int(2))) {
                bg = g;
                bs = s;
            }
        }
        if (bs < 0 || bg <= 0) break;
        taken[bs] = 1;
        chosen[nch++] = bs;
        for (int w = 0; w < W; w++) cov[w] |= ball[bs][w];
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double grow_frac = atof(argv[5]);
    if (grow_frac < 0) grow_frac = 0;
    if (grow_frac > 1) grow_frac = 1;
    if (scanf("%d %d", &n, &m_in) != 2 || n <= 0 || n > MAXN - 2 ||
        m_in < 0 || m_in > MAXE || dd < 1 || dd > MAXD) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || deg[u] >= dd || deg[v] >= dd) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        eu[i] = u;
        ev[i] = v;
    }
    n_in = n;
    bn = n_in;
    bm = m_in;
    for (int i = 0; i < m_in; i++) {
        bu[i] = eu[i];
        bv[i] = ev[i];
    }
    if (DD < 2 || !bipartite_color()) {
        print_best();
        return 0;
    }

    double t_start = now_s();
    double end_s = t_start + budget;

    /* Phase 1: rarest-first cover growth until stuck. */
    deadline_s = t_start + grow_frac * budget;
    compute_balls(DD - 1);
    while (n < MAXN - 2 && now_s() < deadline_s) {
        if (!try_add()) break;
        compute_balls(DD - 1);
    }
    deadline_s = end_s;
    try_snap();

    /* Phase 2: annealing with partial-cover vertex insertion. */
    fill_spare();
    long long cur = total_cost();
    double ep = now_s();
    while (now_s() < end_s) {
        if (cur == 0) {
            try_snap();
            ep = now_s();
            if (n >= MAXN - 2) break;
            compute_balls(DD - 1);
            if (!try_add()) {
                int c = rnd_int(2);
                partial_cover(c);
                if (nch == 0) {
                    c = 1 - c;
                    partial_cover(c);
                }
                if (nch == 0) break;
                add_vertex(c);
            }
            fill_spare();
            cur = total_cost();
            continue;
        }
        double ph = fmod(now_s() - ep, EPOCH_S) / EPOCH_S;
        double T = pow(0.02, ph);
        int ok = (rnd_int(2)) ? do_swap() : do_shift();
        if (!ok) ok = (rnd_int(2)) ? do_shift() : do_swap();
        if (!ok) continue;
        long long nw = total_cost();
        long long dl = nw - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur = nw;
        else undo_move();
    }
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): incidence graph, degree q+1, diameter 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Order 2(q+1)(q^2+1), degree q+1, diameter 4.
    """
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


def _largest_q(d):
    """Largest prime power q <= min(16, d-1), or None."""
    for q in range(min(16, d - 1), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# Non-cyclic voltage lifts (semidirect products), used when no start graph exists.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _c_repair(n, edges, d, D, budget, seed):
    """Run the two-phase C search from a valid start graph; return (n, edges) or None."""
    if budget < 2.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 0.35],
                        stdin_graph=(n, edges), timeout=budget + 6.0)
        gn, ge = lib.parse_graph_text(out)
    except Exception:
        return None
    if gn > n and lib.is_valid(gn, ge, d, D):
        return gn, ge
    return None


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    hard_end = t_start + 0.80 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(gn, ge):
        nonlocal best, best_n
        if gn > best_n and lib.is_valid(gn, ge, d, D):
            best = (gn, ge)
            best_n = gn

    # One start graph per family: the largest prime-power parameter gives the largest order.
    starts = []
    if D == 3:
        q = _largest_q(d)
        if q is not None:
            starts.append(lib.projective_plane_incidence(q))
    elif D == 4:
        q = _largest_q(d)
        if q is not None:
            starts.append(_gq_w(q))
    for sn, se in starts:
        consider(sn, se)

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    if starts:
        # Bold phase: two-phase C search (growth, then annealing) from the largest start.
        sn, se = max(starts, key=lambda g: g[0])
        remaining = hard_end - time.monotonic()
        res = _c_repair(sn, se, d, D, remaining - 2.0, seed)
        if res is not None:
            consider(res[0], res[1])
    elif D >= 4:
        # No algebraic start: fall back to non-cyclic group-lift search.
        G_next = {1: 2, 2: 2, 3: 2, 4: 2}
        while time.monotonic() < hard_end - 1.0:
            k = rng.choice([1, 2, 3, 4])
            G = max(G_next[k], best_n // (2 * k) + 1, 2)
            res = _group_search(d, D, k, G, rng, 200, hard_end)
            if res is not None:
                consider(res[0], res[1])
                G_next[k] = G + 1
            else:
                G_next[k] = G

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
