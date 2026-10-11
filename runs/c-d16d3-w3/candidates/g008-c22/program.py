"""Combined diameter-3 search: structured starts, then one C engine.

Starts (all validated with lib.is_valid):
  - Araujo-Pardo/Lopez graph or PG(2,q) incidence when they apply, and the conic blow-up.
  - Arc-extended PG(2,q) graphs. Each q gets a joint arc set (plateau local search) and
    separate per-side greedy sets, whichever is larger.
  - W(q) for D >= 4 with small q, and K_{d,d} as the always-valid fallback.

C engine (distance matrix kept incrementally):
  1. Insertion: a new vertex on one side, joined to a greedy set cover of spare vertices
     on the other side. Every vertex is within D-1 of the cover, so no distance exceeds D.
  2. Grow-by-two: add an adjacent pair, steal edges to attach them, then repair the
     remaining bad pairs with annealed degree-preserving swaps. Failed attempts are reverted.

The best valid graph is kept throughout. Python validates every output and falls back
to the best start on any failure.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXC 1024
#define MAXDEG 64
#define WMAX (MAXC / 64)
#define INF 100

typedef struct {
    int n;
    int deg[MAXC];
    int adj[MAXC][MAXDEG];
    int col[MAXC];
} Snap;

static int d, D, n, dmax;
static int deg[MAXC];
static int adj[MAXC][MAXDEG];
static int col[MAXC];
static unsigned char dist[MAXC][MAXC];
static uint64_t ball[MAXC][WMAX];
static Snap best, tmp;
static int cand[MAXC], used_[MAXC], sel_[MAXDEG], best_sel[MAXDEG], dv[MAXC];
static int used2[MAXC];
static int stamp2 = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void del_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static void recompute_dist(void) {
    static int q[MAXC];
    for (int s = 0; s < n; s++) {
        unsigned char *row = dist[s];
        for (int x = 0; x < n; x++) row[x] = INF;
        row[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (row[v] == INF) {
                    row[v] = (unsigned char)(row[u] + 1);
                    q[t++] = v;
                }
            }
        }
    }
}

static long bad_count(void) {
    long b = 0;
    for (int s = 0; s < n; s++)
        for (int x = s + 1; x < n; x++)
            if (dist[s][x] > D) b++;
    return b;
}

static void build_balls(void) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < WMAX; w++) ball[v][w] = 0;
        for (int x = 0; x < n; x++)
            if (dist[v][x] <= D - 1) ball[v][x >> 6] |= 1ULL << (x & 63);
    }
}

/* Greedy cover of all vertices by balls of spare vertices on side c. Returns count or -1. */
static int try_insert(int c, int restarts) {
    int nc = 0, Wn = (n + 63) / 64;
    for (int v = 0; v < n; v++)
        if (col[v] == c && deg[v] < dmax) cand[nc++] = v;
    if (nc == 0) return -1;
    uint64_t unc[WMAX];
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < Wn; w++) unc[w] = 0;
        for (int x = 0; x < n; x++) unc[x >> 6] |= 1ULL << (x & 63);
        int uncount = n, ns = 0;
        for (int i = 0; i < nc; i++) used_[i] = 0;
        while (uncount > 0 && ns < dmax) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used_[i]) continue;
                const uint64_t *b = ball[cand[i]];
                int g = 0;
                for (int w = 0; w < Wn; w++) g += __builtin_popcountll(b[w] & unc[w]);
                if (g == 0) continue;
                long long key = (long long)g * 4096 + (long long)(rnd() % 4096);
                if (key > bkey) {
                    bkey = key;
                    bi = i;
                }
            }
            if (bi < 0) break;
            used_[bi] = 1;
            sel_[ns++] = cand[bi];
            const uint64_t *b = ball[cand[bi]];
            uncount = 0;
            for (int w = 0; w < Wn; w++) {
                unc[w] &= ~b[w];
                uncount += __builtin_popcountll(unc[w]);
            }
        }
        if (uncount == 0) {
            for (int k = 0; k < ns; k++) best_sel[k] = sel_[k];
            return ns;
        }
    }
    return -1;
}

static void insert_vertex(int c, int ns) {
    int v = n++;
    col[v] = 1 - c;
    deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(v, best_sel[k]);
    for (int x = 0; x < v; x++) {
        int m = INF;
        for (int k = 0; k < ns; k++) {
            int t = dist[x][best_sel[k]];
            if (t < m) m = t;
        }
        int dd = m + 1;
        if (dd > INF) dd = INF;
        dv[x] = dd;
    }
    for (int x = 0; x < v; x++) {
        dist[x][v] = (unsigned char)dv[x];
        dist[v][x] = (unsigned char)dv[x];
    }
    dist[v][v] = 0;
    for (int x = 0; x < v; x++)
        for (int y = 0; y < v; y++) {
            int t = dv[x] + dv[y];
            if (t > INF) t = INF;
            if (t < dist[x][y]) dist[x][y] = (unsigned char)t;
        }
}

static void snap_save(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * MAXDEG);
}

static void snap_load(const Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * MAXDEG);
    recompute_dist();
}

/* Add a pair (x on side 0, y on side 1) joined by an edge, steal edges to attach them,
   then anneal degree-preserving swaps until the diameter is at most D. */
static int grow_two(double until) {
    int base = n;
    if (n + 2 > MAXC - 2) return 0;
    int x = n, y = n + 1;
    n += 2;
    deg[x] = 0;
    deg[y] = 0;
    col[x] = 0;
    col[y] = 1;
    add_edge(x, y);
    stamp2++;
    int k = 0;
    for (int tries = 0; k < dmax - 1 && tries < 20000; tries++) {
        int a = rndint(base);
        if (col[a] != 0 || deg[a] == 0 || used2[a] == stamp2) continue;
        int b = adj[a][rndint(deg[a])];
        if (b >= base || used2[b] == stamp2) continue;
        del_edge(a, b);
        add_edge(x, b);
        add_edge(y, a);
        used2[a] = stamp2;
        used2[b] = stamp2;
        k++;
    }
    recompute_dist();
    long bad = bad_count();
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = rndint(n);
        if (deg[v] == 0) continue;
        int u = adj[v][rndint(deg[v])];
        int s = rndint(n);
        if (s == v || col[s] != col[v] || deg[s] == 0) continue;
        int t = adj[s][rndint(deg[s])];
        if (t == u || has_edge(v, t) || has_edge(s, u)) continue;
        del_edge(v, u);
        del_edge(s, t);
        add_edge(v, t);
        add_edge(s, u);
        recompute_dist();
        long nb = bad_count();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(v, t);
            del_edge(s, u);
            add_edge(v, u);
            add_edge(s, t);
            recompute_dist();
        }
        T *= 0.999;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 2 || d > MAXDEG - 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    dmax = d;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin <= 0 || nin > MAXC - 300) {
        printf("0 0\n");
        return 0;
    }
    n = nin;
    for (int i = 0; i < n; i++) {
        deg[i] = 0;
        col[i] = -1;
    }
    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) continue;
        if (deg[a] >= dmax || deg[b] >= dmax || has_edge(a, b)) continue;
        add_edge(a, b);
    }

    static int q[MAXC];
    int ok = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    recompute_dist();
    if (bad_count() > 0) {
        printf("0 0\n");
        return 0;
    }

    snap_save(&best);
    while (now() < tl && n + 2 <= MAXC - 2) {
        build_balls();
        int first = rndint(2), inserted = 0;
        for (int t = 0; t < 2 && !inserted; t++) {
            int c = (t == 0) ? first : 1 - first;
            int ns = try_insert(c, 4);
            if (ns > 0) {
                insert_vertex(c, ns);
                inserted = 1;
            }
        }
        if (inserted) {
            snap_save(&best);
            continue;
        }
        snap_save(&tmp);
        double left = tl - now();
        double slice = left / 6.0;
        if (slice < 0.5) slice = 0.5;
        double until = now() + slice;
        if (until > tl) until = tl;
        if (grow_two(until)) snap_save(&best);
        else snap_load(&tmp);
    }

    long m = 0;
    for (int v = 0; v < best.n; v++) m += best.deg[v];
    m /= 2;
    printf("%d %ld\n", best.n, m);
    for (int v = 0; v < best.n; v++)
        for (int k = 0; k < best.deg[v]; k++)
            if (v < best.adj[v][k]) printf("%d %d\n", v, best.adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _ok(g, d, D):
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


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


def _side_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _loads_ok(S, s, m, pl, lp):
    """Joint constraint: S used as points (lines loaded) and as lines (points loaded)."""
    return _side_ok(S, s, m, pl) and _side_ok(S, s, m, lp)


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


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_arc(m, s, pl, lp, rng, init, deadline, iters):
    """Plateau local search for a large joint set S (line loads and point loads both <= s)."""
    inS = [False] * m
    cl = [0] * m
    cp = [0] * m
    S = []

    def fits(P):
        return all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P])

    def put(P):
        inS[P] = True
        S.append(P)
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def take(P):
        inS[P] = False
        S.remove(P)
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    for P in init:
        if not inS[P] and fits(P):
            put(P)
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            put(P)
        else:
            fullL = {L for L in pl[P] if cl[L] >= s}
            fullQ = {Q for Q in lp[P] if cp[Q] >= s}
            blockers = [Q for Q in S
                        if any(L in fullL for L in pl[Q])
                        or any(R in fullQ for R in lp[Q])]
            if len(blockers) != 1:
                continue
            b = blockers[0]
            take(b)
            if fits(P):
                put(P)
            else:
                put(b)
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, SA, SB):
    """Old PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in lp[j]:
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
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        F = lib.GF(q) if q >= 3 else None
        conic = _conic_set(q, index, F) if (s >= 2 and q >= 3) else None

        # Joint set S used on both sides.
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if conic is not None and _loads_ok(conic, s, m, pl, lp):
            cands.append(conic)
        init = max(cands, key=len)
        loc = _local_arc(m, s, pl, lp, rng, init,
                         min(deadline, time.monotonic() + 0.5), 4000)
        cands.append(loc)
        S = max(cands, key=len)
        if _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S, S))

        # Separate sets for the A-side and the B-side.
        SA = _greedy_side(m, s, pl, rng, 40, deadline)
        SB = _greedy_side(m, s, lp, rng, 40, deadline)
        if conic is not None:
            if len(conic) > len(SA) and _side_ok(conic, s, m, pl):
                SA = conic
            if len(conic) > len(SB) and _side_ok(conic, s, m, lp):
                SB = conic
        if _side_ok(SA, s, m, pl) and _side_ok(SB, s, m, lp):
            out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


def _gq_w(q):
    """Incidence graph of the generalized quadrangle W(q); diameter 4."""
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


def known_start(d, D):
    """Directly constructible D = 3 graphs: projective plane or Araujo-Pardo/Lopez."""
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
    if D >= 4 and d - 1 <= 8:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    try:
        for g in starts(d, D, t0 + 0.15 * time_limit, rng):
            if _ok(g, d, D):
                cands.append(g)
    except Exception:
        pass
    if _ok(fallback, d, D):
        cands.append(fallback)
    if not cands:
        return fallback
    best = max(cands, key=lambda g: g[0])

    # Calibration-sized cases already at the Moore bound need no search.
    if d < 3 or best[0] >= lib.moore_bound(d, D):
        return best

    hard_end = t0 + 0.80 * time_limit
    budget = hard_end - time.monotonic() - 2.0
    if budget >= 1.0:
        timeout = max(budget + 1.0, t0 + time_limit - 1.5 - time.monotonic())
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=timeout)
            g2 = lib.parse_graph_text(out)
            if g2[0] > best[0] and _ok(g2, d, D):
                best = g2
        except Exception:
            pass

    if not _ok(best, d, D):
        best = fallback
    return best
