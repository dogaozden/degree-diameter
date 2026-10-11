"""Diameter-3 bipartite search: arc-extended PG(2,q) and plain PG(2,q) starts, plus a C engine.

New in this version (C engine):
- Min-conflict cover search for vertex insertion. A new vertex x on side X is joined to a set T
  of spare vertices on the other side. Exact validity: dist(x, y) <= D for all y iff every y lies
  within distance D-1 of T. The cover is found by a tabu-guided swap search over bitsets (cover
  counts, "uncovered" and "covered exactly once" masks), replacing one-shot greedy set cover.
- Delete-and-regrow plateau moves. When insertion stalls, the engine deletes one or two vertices
  whose removal keeps the graph valid (checked by BFS with the vertex skipped), regrows, and keeps
  the result if the order did not drop. Otherwise it restores the snapshot.

Every state the engine keeps is valid, and Python re-checks the output with lib.is_valid.
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
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 64
#define MAXIT 1200
#define STALL 20
#define TENURE 6
#define GROW_FAILS 60
#define DEL_TRIES 12

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];   /* vertices within Dist-1 of each vertex */
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static int cov[MAXN];
static uint64_t UB[WORDS], ONE[WORDS];

typedef struct {
    int n;
    int deg[MAXN];
    int side[MAXN];
    int adj[MAXN][MAXDEG];
} Snap;
static Snap bestS, backS;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static inline int getb(const uint64_t *b, int y) { return (int)((b[y >> 6] >> (y & 63)) & 1ULL); }
static inline void setb(uint64_t *b, int y) { b[y >> 6] |= 1ULL << (y & 63); }
static inline void clrb(uint64_t *b, int y) { b[y >> 6] &= ~(1ULL << (y & 63)); }

static int countb(const uint64_t *b) {
    int c = 0;
    for (int i = 0; i < W; i++) c += popc(b[i]);
    return c;
}

static int and_count(const uint64_t *a, const uint64_t *b) {
    int c = 0;
    for (int i = 0; i < W; i++) c += popc(a[i] & b[i]);
    return c;
}

/* Index of the r-th set bit (0-based) of b, or -1. */
static int nth_bit(const uint64_t *b, int r) {
    for (int i = 0; i < W; i++) {
        int c = popc(b[i]);
        if (r < c) {
            for (int j = 0; j < 64; j++) {
                if ((b[i] >> j) & 1ULL) {
                    if (r == 0) return i * 64 + j;
                    r--;
                }
            }
        }
        r -= c;
    }
    return -1;
}

/* Bitset of vertices within distance r of src, never passing through vertex skip (-1 = none). */
static void ball_skip(int src, int r, uint64_t *bits, int skip) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < WORDS; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (v == skip || mark[v] == stamp) continue;
            mark[v] = stamp;
            lev[v] = lev[u] + 1;
            bq[t++] = v;
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_skip(v, Dist - 1, ball[v], -1);
}

/* True if the graph without vertex skip (or the full graph if skip < 0) has diameter <= Dist. */
static int valid_skip(int skip) {
    uint64_t b[WORDS];
    int need = N - (skip >= 0 ? 1 : 0);
    for (int v = 0; v < N; v++) {
        if (v == skip) continue;
        ball_skip(v, Dist, b, skip);
        if (countb(b) != need) return 0;
    }
    return 1;
}

/* Remove vertex v, compacting labels by moving the last vertex into slot v. */
static void delete_vertex(int v) {
    for (int k = 0; k < deg[v]; k++) {
        int u = adj[v][k];
        for (int j = 0; j < deg[u]; j++) {
            if (adj[u][j] == v) {
                adj[u][j] = adj[u][--deg[u]];
                break;
            }
        }
    }
    int L = N - 1;
    if (v != L) {
        deg[v] = deg[L];
        for (int k = 0; k < deg[L]; k++) adj[v][k] = adj[L][k];
        side[v] = side[L];
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            for (int j = 0; j < deg[u]; j++) {
                if (adj[u][j] == L) {
                    adj[u][j] = v;
                    break;
                }
            }
        }
    }
    deg[L] = 0;
    N--;
    W = (N + 63) / 64;
    recompute_balls();
}

/* Add (sg>0) or remove (sg<0) the ball of t from the cover counts. */
static void cover_update(int t, int sg) {
    for (int i = 0; i < W; i++) {
        for (int j = 0; j < 64; j++) {
            if (!((ball[t][i] >> j) & 1ULL)) continue;
            int y = i * 64 + j;
            if (sg > 0) {
                cov[y]++;
                if (cov[y] == 1) {
                    clrb(UB, y);
                    setb(ONE, y);
                } else if (cov[y] == 2) {
                    clrb(ONE, y);
                }
            } else {
                cov[y]--;
                if (cov[y] == 0) {
                    setb(UB, y);
                    clrb(ONE, y);
                } else if (cov[y] == 1) {
                    setb(ONE, y);
                }
            }
        }
    }
}

/* Min-conflict cover search: find T (|T| <= Dd, spare vertices on side != X) whose radius-(D-1)
   balls cover all existing vertices. On success, add a new vertex on side X joined to T. */
static int try_add(int X) {
    static int inT[MAXN], tabu[MAXN], pool[MAXN];
    int T[MAXDEG];
    int nt = 0, np = 0;
    if (N < 1 || N + 1 >= MAXN) return 0;
    for (int v = 0; v < N; v++) {
        inT[v] = 0;
        tabu[v] = -1;
        cov[v] = 0;
        if (side[v] != X && deg[v] < Dd) pool[np++] = v;
    }
    if (np == 0) return 0;
    for (int i = 0; i < WORDS; i++) {
        UB[i] = 0;
        ONE[i] = 0;
    }
    for (int y = 0; y < N; y++) setb(UB, y);

    int success = 0;
    for (int it = 0; it < MAXIT; it++) {
        int unc = countb(UB);
        if (unc == 0) {
            success = 1;
            break;
        }
        int y = nth_bit(UB, rndint(unc));
        if (y < 0) break;
        if (nt < Dd) {
            int best = -1;
            long bsc = -(1L << 40);
            for (int p = 0; p < np; p++) {
                int t = pool[p];
                if (inT[t] || !getb(ball[t], y)) continue;
                long sc = (long)and_count(ball[t], UB) * 16 + rndint(16);
                if (tabu[t] > it) sc -= 100000;
                if (sc > bsc) {
                    bsc = sc;
                    best = t;
                }
            }
            if (best < 0) break;
            T[nt++] = best;
            inT[best] = 1;
            cover_update(best, +1);
        } else {
            /* Drop the member whose removal uncovers the fewest vertices. */
            int out = 0;
            long bl = 1L << 40;
            for (int k = 0; k < nt; k++) {
                long sc = (long)and_count(ball[T[k]], ONE) * 16 + rndint(16);
                if (sc < bl) {
                    bl = sc;
                    out = k;
                }
            }
            int t = T[out];
            cover_update(t, -1);
            inT[t] = 0;
            tabu[t] = it + TENURE;
            T[out] = T[--nt];
        }
    }
    if (!success || nt == 0) return 0;

    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        adj[x][k] = T[k];
        adj[T[k]][deg[T[k]]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

static void snap_save(Snap *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof(deg));
    memcpy(s->side, side, sizeof(side));
    memcpy(s->adj, adj, sizeof(adj));
}

static void snap_load(const Snap *s) {
    N = s->n;
    W = (N + 63) / 64;
    memcpy(deg, s->deg, sizeof(deg));
    memcpy(side, s->side, sizeof(side));
    memcpy(adj, s->adj, sizeof(adj));
    recompute_balls();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 2 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();
    snap_save(&bestS);

    double t_end = elapsed() + budget;
    int stall = 0;
    while (elapsed() < t_end && N < MAXN - 2) {
        if (try_add(rndint(2))) {
            stall = 0;
            if (N > bestS.n) snap_save(&bestS);
            continue;
        }
        if (++stall < STALL) continue;
        stall = 0;

        /* Plateau move: delete 1-2 vertices (each deletion keeps validity), then regrow. */
        snap_save(&backS);
        int curN = N, ok = 1;
        int k = 1 + rndint(2);
        for (int r = 0; r < k && ok; r++) {
            int found = 0;
            for (int tr = 0; tr < DEL_TRIES && !found; tr++) {
                int v = rndint(N);
                if (valid_skip(v)) {
                    delete_vertex(v);
                    found = 1;
                }
            }
            if (!found) ok = 0;
        }
        if (ok) {
            int f = 0;
            while (f < GROW_FAILS && elapsed() < t_end && N < MAXN - 2) {
                if (try_add(rndint(2))) {
                    f = 0;
                    if (N > bestS.n) snap_save(&bestS);
                } else {
                    f++;
                }
            }
        }
        if (!ok || N < curN || !valid_skip(-1)) snap_load(&backS);
    }

    snap_load(&bestS);
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane starts (diameter 3).
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
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


def _plain_start(d):
    """Plain incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 25), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 82% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.82 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2 among bipartite graphs with max degree d.
    fallback = lib.haar_graph(d, range(d))
    if D <= 2 or d == 1:
        if lib.is_valid(fallback[0], fallback[1], d, D):
            return fallback
        return 1, []

    rng = random.Random(seed * 7919 + d)
    starts = []
    starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    plain = _plain_start(d)
    if plain is not None:
        starts.append(plain)
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    starts.sort(key=lambda g: -g[0])
    best = starts[0]

    # Already at the Moore bound: nothing to gain.
    if best[0] >= lib.moore_bound(d, D):
        return best

    plan = starts[:2]
    for idx, src in enumerate(plan + [None]):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if src is None:
            src = best
            share = remaining
        else:
            share = 0.4 * remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 2.5)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
