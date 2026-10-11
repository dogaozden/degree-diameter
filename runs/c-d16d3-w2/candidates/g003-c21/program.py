import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with a penalty.
#
# State: a bipartite graph with max degree d on alive vertices (indices < cap).
# Moves:
#   add    : activate a dead slot on a random side and join it to up to d
#            opposite-side vertices (a full partner loses one random edge),
#   remove : deactivate a random alive vertex,
#   swap   : double-edge swap (u,v),(x,y) -> (u,y),(x,v) preserving degrees
#            and bipartiteness.
# Energy: E = bad - BETA * nalive, where bad = number of unordered alive pairs
# at distance > D. The best state with bad == 0 is kept and printed, relabelled
# to 0..n-1. Python validates the output and falls back on any failure.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int nalive;
    int cap;
} State;

static State cur, bak, best;
static int have_best = 0;
static int d, D;
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) if (cur.adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    cur.adj[u][cur.deg[u]++] = v;
    cur.adj[v][cur.deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) {
        if (cur.adj[u][i] == v) {
            cur.adj[u][i] = cur.adj[u][cur.deg[u] - 1];
            cur.deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

static long long compute_bad(void) {
    int cap = cur.cap;
    int W = (cap + 63) >> 6;
    if (W < 1) W = 1;
    for (int v = 0; v < cap; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        if (cur.alive[v]) reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < cur.deg[v]; i++) {
                int u = cur.adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
        }
    }
    long long tot = 0;
    for (int v = 0; v < cap; v++) {
        if (!cur.alive[v]) continue;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(reach[v][w]);
        tot += cur.nalive - pc;
    }
    return tot / 2;
}

static int move_add(void) {
    int w = -1;
    for (int i = 0; i < MAXN; i++) if (!cur.alive[i]) { w = i; break; }
    if (w < 0) return 0;
    int side = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < cur.cap; v++)
        if (cur.alive[v] && cur.col[v] == 1 - side) cand[nc++] = v;
    if (nc == 0) return 0;
    int k = nc < d ? nc : d;
    for (int i = 0; i < k; i++) {
        int j = i + rndi(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    cur.alive[w] = 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    cur.nalive++;
    if (w + 1 > cur.cap) cur.cap = w + 1;
    for (int i = 0; i < k; i++) {
        int p = cand[i];
        if (cur.deg[p] >= d) {
            int q = cur.adj[p][rndi(cur.deg[p])];
            del_edge(p, q);
        }
        add_edge(w, p);
    }
    return 1;
}

static int move_remove(void) {
    if (cur.nalive <= 2) return 0;
    int w, tries = 0;
    do {
        w = rndi(cur.cap);
        tries++;
    } while (!cur.alive[w] && tries < 100000);
    if (!cur.alive[w]) return 0;
    while (cur.deg[w] > 0) {
        int u = cur.adj[w][0];
        del_edge(w, u);
    }
    cur.alive[w] = 0;
    cur.nalive--;
    return 1;
}

static int move_swap(void) {
    int u, x, tries = 0;
    do {
        u = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[u] || cur.deg[u] == 0) && tries < 100000);
    if (!cur.alive[u] || cur.deg[u] == 0) return 0;
    int v = cur.adj[u][rndi(cur.deg[u])];
    int s = cur.col[u];
    tries = 0;
    do {
        x = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) && tries < 100000);
    if (!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) return 0;
    int y = cur.adj[x][rndi(cur.deg[x])];
    if (x == u || y == v) return 0;
    if (has_edge(u, y) || has_edge(x, v)) return 0;
    del_edge(u, v);
    del_edge(x, y);
    add_edge(u, y);
    add_edge(x, v);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 64) { printf("0 0\n"); return 0; }
    memset(&cur, 0, sizeof(cur));
    cur.cap = N0;
    cur.nalive = N0;
    for (int i = 0; i < N0; i++) cur.alive[i] = 1;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int i = 0; i < N0; i++) cur.col[i] = -1;
    for (int s = 0; s < N0; s++) {
        if (cur.col[s] >= 0) continue;
        cur.col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (cur.col[v] < 0) {
                    cur.col[v] = 1 - cur.col[u];
                    queue[qt++] = v;
                }
            }
        }
    }
    /* drop any edge joining equal colours (only possible for non-bipartite input) */
    for (int u = 0; u < N0; u++) {
        for (int i = cur.deg[u] - 1; i >= 0; i--) {
            if (i >= cur.deg[u]) continue;
            int v = cur.adj[u][i];
            if (cur.col[v] == cur.col[u]) del_edge(u, v);
        }
    }

    clock_t t0 = clock();
    long long bad = compute_bad();
    const double BETA = 2.0;
    const double T0 = 2.0, T1 = 0.03;
    double E = (double)bad - BETA * cur.nalive;
    if (bad == 0) {
        memcpy(&best, &cur, sizeof(State));
        have_best = 1;
    }

    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > budget) break;
        double frac = budget > 0 ? el / budget : 1.0;
        double T = T0 * pow(T1 / T0, frac);

        memcpy(&bak, &cur, sizeof(State));
        double r = rndu();
        int ok;
        if (r < 0.35) ok = move_add();
        else if (r < 0.45) ok = move_remove();
        else ok = move_swap();
        if (!ok) continue;

        bad = compute_bad();
        double E2 = (double)bad - BETA * cur.nalive;
        if (E2 <= E || rndu() < exp(-(E2 - E) / T)) {
            E = E2;
            if (bad == 0 && (!have_best || cur.nalive > best.nalive)) {
                memcpy(&best, &cur, sizeof(State));
                have_best = 1;
            }
        } else {
            memcpy(&cur, &bak, sizeof(State));
        }
    }

    State *s = have_best ? &best : &cur;
    static int id[MAXN];
    int n = 0;
    for (int i = 0; i < s->cap; i++) id[i] = s->alive[i] ? n++ : -1;
    long m = 0;
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] > u) m++;
    }
    printf("%d %ld\n", n, m);
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) {
            int v = s->adj[u][i];
            if (v > u) printf("%d %d\n", id[u], id[v]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# New idea: "cover families" on the projective plane.
#
# Start from PG(2,q) incidence (degree q+1, spare s = d-q-1 on every vertex).
# A new point-side vertex x may be joined to a set S_x of lines provided:
#   (a) every point lies on some line of S_x     (so x is within distance 2
#       of all old points),
#   (b) every two new point-side vertices share a line (distance 2 between them),
#   (c) every line receives at most s new neighbours (degree bound).
# Every old line meets every line of S_x, so distance 3 to old lines is automatic,
# and the dual statement covers the line-side vertices. The mixed pairs are at
# distance <= 3 because the covering property on the other side is exactly what
# is needed. Hence any such pair of families gives a diameter-3 bipartite graph.
#
# Pencils (all lines through a point P) are covers of size q+1. Pencils of an
# arc (a set of points with at most s on each line) form a valid family, which
# is the parent's construction (2(q^2+q+5)-type records). We go beyond it with
# larger covers (size up to d) that use spare capacity: simulated annealing
# adds further sets, repairing coverage, load and pairwise-intersection costs.
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): a (q+1)- or (q+2)-set with at most 2 points on any line."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _family_search(cover, ntg, nel, s, sz, init, k, deadline, rng):
    """Find k subsets of elements with: every target covered by each subset,
    each element in at most s subsets, and every two subsets sharing an element.
    cover[e] lists the targets covered by element e. init is a list of valid
    starting subsets (kept as they are); new subsets are random of size sz.
    Returns the list of subsets with zero cost, or None on timeout."""
    tg_el = [[] for _ in range(ntg)]
    for e in range(nel):
        for t in cover[e]:
            tg_el[t].append(e)

    sets = [list(x) for x in init]
    while len(sets) < k:
        sets.append(rng.sample(range(nel), sz))
    K = len(sets)

    mem = [[False] * nel for _ in range(K)]
    cnt = [[0] * ntg for _ in range(K)]
    load = [0] * nel
    for i in range(K):
        for e in sets[i]:
            mem[i][e] = True
            load[e] += 1
            for t in cover[e]:
                cnt[i][t] += 1
    uncov = [sum(1 for c in cnt[i] if c == 0) for i in range(K)]
    inter = [[0] * K for _ in range(K)]
    for i in range(K):
        for j in range(K):
            if i != j:
                inter[i][j] = sum(1 for e in sets[i] if mem[j][e])

    def f(x):
        return x - s if x > s else 0

    total = sum(uncov) + sum(f(x) for x in load)
    total += sum(1 for i in range(K) for j in range(i + 1, K) if inter[i][j] == 0)
    if total == 0:
        return sets

    def apply(i, pos, ein):
        """Replace sets[i][pos] by ein, update all counters, return the cost changes."""
        eout = sets[i][pos]
        ci = cnt[i]
        dcov = 0
        for t in cover[eout]:
            ci[t] -= 1
            if ci[t] == 0:
                dcov += 1
        for t in cover[ein]:
            if ci[t] == 0:
                dcov -= 1
            ci[t] += 1
        le = load[eout]
        dload = f(le - 1) - f(le)
        load[eout] = le - 1
        le = load[ein]
        dload += f(le + 1) - f(le)
        load[ein] = le + 1
        mem[i][eout] = False
        mem[i][ein] = True
        dint = 0
        for j in range(K):
            if j == i:
                continue
            old = inter[i][j]
            new = old
            if mem[j][eout]:
                new -= 1
            if mem[j][ein]:
                new += 1
            if new != old:
                dint += (1 if new == 0 else 0) - (1 if old == 0 else 0)
                inter[i][j] = new
                inter[j][i] = new
        uncov[i] += dcov
        sets[i][pos] = ein
        return dcov, dload, dint

    T0, T1 = 0.7, 0.04
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-3)
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - t_start) / span
            T = T0 * (T1 / T0) ** frac
        i = rng.randrange(K)
        pos = rng.randrange(len(sets[i]))
        if uncov[i] > 0 and rng.random() < 0.8:
            unc = [t for t in range(ntg) if cnt[i][t] == 0]
            if not unc:
                continue
            ein = rng.choice(tg_el[rng.choice(unc)])
        else:
            ein = rng.randrange(nel)
        if mem[i][ein]:
            continue
        eout = sets[i][pos]
        dcov, dload, dint = apply(i, pos, ein)
        delta = dcov + dload + dint
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            total += delta
            if total == 0:
                return sets
        else:
            apply(i, pos, eout)


def _grow_family(cover, ntg, nel, s, sz, fam0, deadline, rng):
    """Start from a valid family fam0 and keep adding one more subset while time allows."""
    fam = [list(x) for x in fam0]
    while True:
        rem = deadline - time.monotonic()
        if rem < 0.3:
            break
        res = _family_search(cover, ntg, nel, s, sz, fam, len(fam) + 1,
                             time.monotonic() + 0.5 * rem, rng)
        if res is not None:
            fam = [list(x) for x in res]
    return fam


def _assemble(m, edges, famA, famB):
    """Old PG incidence plus new point-side vertices (joined to lines) and new line-side vertices (joined to points)."""
    E = list(edges)
    base = 2 * m
    for t, S in enumerate(famA):
        x = base + t
        for L in S:
            E.append((x, m + L))
    base2 = base + len(famA)
    for u, T in enumerate(famB):
        y = base2 + u
        for P in T:
            E.append((P, y))
    return base2 + len(famB), E


def _d3_construct(d, rng, deadline, consider):
    """D = 3 constructions: PG(2,q) with q the largest prime power <= d-1, then cover families."""
    q = max(p for p in range(2, d) if lib.is_prime_power(p))
    n0, e0 = lib.projective_plane_incidence(q)
    consider((n0, e0))
    s = d - q - 1
    if s < 2:
        return
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    SA = _conic_set(q, index, lib.GF(q))
    avail = deadline - time.monotonic()
    if avail < 1.0:
        return
    # Pencils of the arc: valid starting family for the point side (elements = lines).
    fam0A = [list(point_lines[P]) for P in SA]
    t1 = time.monotonic() + 0.4 * avail
    famA = _grow_family(line_points, m, m, s, d, fam0A, t1, rng)
    # Dual: elements = points, targets = lines.
    fam0B = [list(line_points[j]) for j in SA]
    t2 = time.monotonic() + 0.4 * avail
    famB = _grow_family(point_lines, m, m, s, d, fam0B, t2, rng)
    n, E = _assemble(m, edges, famA, famB)
    consider((n, E))


# ----------------------------------------------------------------------------
# C annealing wrapper.
# ----------------------------------------------------------------------------

def _c_anneal(graph, d, D, seed, budget):
    """Run the C annealer from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 3.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: PG(2,q) base, then cover-family search for extra vertices.
#   else  : K_{d,d} start for the C annealer.
# Every candidate is checked with lib.is_valid, and K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.86 * time_limit - 1.0
    rng = random.Random(seed * 1000003 + 97 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Always-valid fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3 and d >= 3:
        try:
            _d3_construct(d, rng, deadline, consider)
        except Exception:
            pass

    # Already at the Moore bound: nothing more to gain.
    if best[0] >= lib.moore_bound(d, D):
        return best

    left = deadline - time.monotonic()
    if left >= 1.0:
        consider(_c_anneal(best, d, D, seed, left - 0.5))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
