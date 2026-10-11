import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: spare-slot annealing for bipartite graphs with diameter <= D.
#
# State: a bipartite graph with max degree d and vertex sides 0/1.
# Moves:
#   swap   - 2-switch on two edges (a,b),(c,e) -> (a,e),(c,b); degrees fixed.
#   delete - remove a random edge, freeing a slot on each endpoint.
#   insert - add a new vertex joined to up to d spare opposite-side vertices.
#   fill   - add edges between spare opposite-side vertices (never raises cost).
# Cost = number of unordered pairs at distance > D, computed by bitset BFS.
# Metropolis acceptance on the cost; the best cost-0 graph with the most
# vertices is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40
#define MAXE 20480
#define WMAX 16

static int d_, D_;
static int n_, ne_;
static int side_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXD];
static int eu_[MAXE], ev_[MAXE];

static uint64_t rs_ = 88172645463325252ULL;
static uint64_t rnd(void) { rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17; return rs_; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static uint64_t bufA[MAXN][WMAX], bufB[MAXN][WMAX];

static int cost_eval(void) {
    int n = n_;
    int wn = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < wn; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < wn; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                int u = nb_[v][i];
                for (int w = 0; w < wn; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < wn; w++) c += popc(cur[v][w]);
        total += n - c;
    }
    return (int)(total / 2);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) if (nb_[a][i] == b) return 1;
    return 0;
}

static void rem_adj(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (nb_[a][i] == b) {
            nb_[a][i] = nb_[a][deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    if (side_[a] == 1) { int t = a; a = b; b = t; }
    eu_[ne_] = a;
    ev_[ne_] = b;
    ne_++;
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
}

static void del_edge_idx(int i) {
    int a = eu_[i], b = ev_[i];
    rem_adj(a, b);
    rem_adj(b, a);
    ne_--;
    if (i != ne_) { eu_[i] = eu_[ne_]; ev_[i] = ev_[ne_]; }
}

static int swap_move(void) {
    if (ne_ < 2) return 0;
    int i = rndi(ne_), j = rndi(ne_);
    if (i == j) return 0;
    int a = eu_[i], b = ev_[i], c = eu_[j], e = ev_[j];
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    rem_adj(a, b); rem_adj(b, a);
    rem_adj(c, e); rem_adj(e, c);
    nb_[a][deg_[a]++] = e; nb_[e][deg_[e]++] = a;
    nb_[c][deg_[c]++] = b; nb_[b][deg_[b]++] = c;
    eu_[i] = a; ev_[i] = e;
    eu_[j] = c; ev_[j] = b;
    return 1;
}

static int try_insert(void) {
    if (n_ >= MAXN - 1) return -1;
    int s = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < n_; v++)
        if (side_[v] != s && deg_[v] < d_) cand[nc++] = v;
    if (nc == 0) return -1;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int k = nc < d_ ? nc : d_;
    if (rndu() < 0.2) k = 1 + rndi(k);
    int x = n_++;
    side_[x] = s;
    deg_[x] = 0;
    for (int i = 0; i < k; i++) add_edge(x, cand[i]);
    return x;
}

static void fill(void) {
    static int A[MAXN], B[MAXN];
    int fails = 0;
    while (fails < 200) {
        int na = 0, nbb = 0;
        for (int v = 0; v < n_; v++) {
            if (deg_[v] < d_) {
                if (side_[v] == 0) A[na++] = v;
                else B[nbb++] = v;
            }
        }
        if (na == 0 || nbb == 0) return;
        int a = A[rndi(na)], b = B[rndi(nbb)];
        if (has_edge(a, b)) { fails++; continue; }
        add_edge(a, b);
        fails = 0;
    }
}

typedef struct {
    int n, ne;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXD];
    int eu[MAXE], ev[MAXE];
} Snap;

static Snap sv_;

static void save_state(void) {
    sv_.n = n_;
    sv_.ne = ne_;
    memcpy(sv_.side, side_, sizeof(int) * n_);
    memcpy(sv_.deg, deg_, sizeof(int) * n_);
    for (int v = 0; v < n_; v++) memcpy(sv_.nb[v], nb_[v], sizeof(int) * deg_[v]);
    memcpy(sv_.eu, eu_, sizeof(int) * ne_);
    memcpy(sv_.ev, ev_, sizeof(int) * ne_);
}

static void restore_state(void) {
    n_ = sv_.n;
    ne_ = sv_.ne;
    memcpy(side_, sv_.side, sizeof(int) * n_);
    memcpy(deg_, sv_.deg, sizeof(int) * n_);
    for (int v = 0; v < n_; v++) memcpy(nb_[v], sv_.nb[v], sizeof(int) * deg_[v]);
    memcpy(eu_, sv_.eu, sizeof(int) * ne_);
    memcpy(ev_, sv_.ev, sizeof(int) * ne_);
}

static int bestn_, bestne_;
static int bEu_[MAXE], bEv_[MAXE];

static void save_best(void) {
    bestn_ = n_;
    bestne_ = ne_;
    memcpy(bEu_, eu_, sizeof(int) * ne_);
    memcpy(bEv_, ev_, sizeof(int) * ne_);
}

static static_dummy_unused_guard;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs_ ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    clock_t c0 = clock();

    int n = 0, m = 0, ok = 1;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    static int tu[MAXE], tv[MAXE];
    if (n > 0) {
        if (n > MAXN - 2 || m < 0 || m > MAXE) ok = 0;
        for (int i = 0; ok && i < m; i++) {
            if (scanf("%d %d", &tu[i], &tv[i]) != 2) { ok = 0; break; }
            if (tu[i] < 0 || tu[i] >= n || tv[i] < 0 || tv[i] >= n || tu[i] == tv[i]) ok = 0;
        }
    } else {
        ok = 0;
    }

    n_ = 0;
    ne_ = 0;
    if (ok) {
        n_ = n;
        for (int v = 0; v < n; v++) { side_[v] = -1; deg_[v] = 0; }
        int changed = 1;
        while (ok) {
            while (changed) {
                changed = 0;
                for (int i = 0; i < m; i++) {
                    int u = tu[i], v = tv[i];
                    if (side_[u] < 0 && side_[v] < 0) continue;
                    if (side_[u] < 0) { side_[u] = 1 - side_[v]; changed = 1; }
                    else if (side_[v] < 0) { side_[v] = 1 - side_[u]; changed = 1; }
                    else if (side_[u] == side_[v]) { ok = 0; break; }
                }
                if (!ok) break;
            }
            if (!ok) break;
            int found = 0;
            for (int i = 0; i < m; i++) {
                if (side_[tu[i]] < 0 && side_[tv[i]] < 0) {
                    side_[tu[i]] = 0;
                    found = 1;
                    changed = 1;
                    break;
                }
            }
            if (!found) break;
        }
        if (ok) {
            for (int v = 0; v < n; v++) if (side_[v] < 0) side_[v] = 0;
            for (int i = 0; ok && i < m; i++) {
                int a = tu[i], b = tv[i];
                if (side_[a] == side_[b]) { ok = 0; break; }
                if (deg_[a] >= d_ || deg_[b] >= d_ || has_edge(a, b)) { ok = 0; break; }
                add_edge(a, b);
            }
        }
    }

    int have = 0;
    if (ok && n_ > 0 && cost_eval() == 0) have = 1;
    if (!have) {
        n_ = 2 * d_;
        ne_ = 0;
        for (int v = 0; v < n_; v++) { side_[v] = (v >= d_); deg_[v] = 0; }
        for (int a = 0; a < d_; a++)
            for (int b = d_; b < 2 * d_; b++)
                add_edge(a, b);
    }

    save_best();

    int cur = cost_eval();
    double T0 = 0.6, T = T0;
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < tl) {
        save_state();
        double r = rndu();
        int moved = 0;
        if (r < 0.5) {
            moved = swap_move();
        } else if (r < 0.72) {
            if (ne_ > 0) { del_edge_idx(rndi(ne_)); moved = 1; }
        } else if (r < 0.97) {
            if (try_insert() >= 0) { fill(); moved = 1; }
        } else {
            fill();
            moved = 1;
        }
        if (!moved) continue;

        int nc = cost_eval();
        int delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = nc;
        else restore_state();

        if (cur == 0 && n_ > bestn_) save_best();

        T *= 0.9996;
        if (T < 0.08) T = T0;
    }

    printf("%d %d\n", bestn_, bestne_);
    for (int i = 0; i < bestne_; i++) printf("%d %d\n", bEu_[i], bEv_[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), from the parent.
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Multisets of points (A-side) and
# lines (B-side) each get one new vertex per entry, subject to load <= s.
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
    """True if every target t is hit by <= s entries of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets with per-target load <= s; returns the largest seen."""
    order = list(range(m))

    def fill_s(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill_s([], [0] * m)
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
        S = fill_s(S, load)
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D = 4), from the parent.
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
# Helper: run the C spare-slot annealer on a valid start graph.
# ----------------------------------------------------------------------------

def _c_search(graph, d, D, seed, budget):
    """Run the C engine from `graph` for about `budget` seconds; return the parsed output."""
    n, e = graph
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, e), timeout=budget + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.25 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if d < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    # Spend the remaining budget in C, starting from the best construction.
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            cand = _c_search(best, d, D, seed, budget)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
