import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: cover-guided vertex insertion followed by simulated-annealing
# repair. Moves are degree-preserving edge switches, endpoint rewires and greedy
# edge filling. The cost is the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define DMAX 32
#define WMAX ((NMAX + 63) / 64)
#define RESTARTS 8
#define GROW_ITERS 3000
#define KICK_ITERS 4000

typedef uint64_t Row[WMAX];

static int d_, D_;
static int n, W;
static int color[NMAX];
static int deg[NMAX];
static int adj[NMAX][DMAX];
static Row BD[NMAX], BM[NMAX], TB[NMAX];
static double deadline;
static uint64_t rs = 88172645463325252ULL;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_n(int m) {
    n = m;
    W = (n + 63) >> 6;
    if (W < 1) W = 1;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void raw_add(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void raw_del(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; break; }
    for (int k = 0; k < deg[b]; k++)
        if (adj[b][k] == a) { adj[b][k] = adj[b][--deg[b]]; break; }
}

typedef struct { int t, a, b; } Op;
static Op oplog[128];
static int nops = 0;

static void L_add(int a, int b) {
    raw_add(a, b);
    oplog[nops].t = 1; oplog[nops].a = a; oplog[nops].b = b;
    nops++;
}

static void L_del(int a, int b) {
    raw_del(a, b);
    oplog[nops].t = 0; oplog[nops].a = a; oplog[nops].b = b;
    nops++;
}

static void undo_log(void) {
    while (nops > 0) {
        Op o = oplog[--nops];
        if (o.t) raw_del(o.a, o.b);
        else raw_add(o.a, o.b);
    }
}

static void compute_balls(int r, Row *out) {
    for (int v = 0; v < n; v++) {
        memset(out[v], 0, sizeof(Row));
        out[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            memcpy(TB[v], out[v], sizeof(Row));
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = out[adj[v][k]];
                for (int w = 0; w < W; w++) TB[v][w] |= src[w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(out[v], TB[v], sizeof(Row));
    }
}

static long long cost_now(void) {
    compute_balls(D_, BD);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BD[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int pick_color(int col) {
    for (int t = 0; t < 60; t++) {
        int x = rndint(n);
        if (color[x] == col) return x;
    }
    return -1;
}

static int pick_def(int col) {
    for (int t = 0; t < 60; t++) {
        int x = rndint(n);
        if (color[x] == col && deg[x] < d_) return x;
    }
    return -1;
}

/* Degree-preserving switch of two B-endpoints across two A-vertices. */
static int move_switch(void) {
    int a = pick_color(0);
    int c = pick_color(0);
    if (a < 0 || c < 0 || a == c || deg[a] == 0 || deg[c] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int e = adj[c][rndint(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    L_del(a, b);
    L_del(c, e);
    L_add(a, e);
    L_add(c, b);
    return 1;
}

/* Move one edge endpoint to a deficient vertex on the same side. */
static int move_rewire(void) {
    int a = rndint(n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int b2 = pick_def(color[b]);
    if (b2 < 0 || b2 == b || has_edge(a, b2)) return 0;
    L_del(a, b);
    L_add(a, b2);
    return 1;
}

/* Add edges between non-adjacent deficient vertices of opposite sides. */
static int fill_pairs(int logged, int cap) {
    static int A[NMAX], B[NMAX];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (color[v] == 0) A[na++] = v;
            else B[nb++] = v;
        }
    }
    if (na == 0 || nb == 0) return 0;
    int added = 0;
    long long tries = logged ? (4LL * (na + nb) + 8) : (30LL * (na + nb));
    for (long long t = 0; t < tries && added < cap; t++) {
        int a = A[rndint(na)];
        int b = B[rndint(nb)];
        if (deg[a] >= d_ || deg[b] >= d_ || has_edge(a, b)) continue;
        if (logged) L_add(a, b);
        else raw_add(a, b);
        added++;
    }
    return added;
}

/* Greedy cover: choose up to d_ opposite-side vertices whose radius-(D-1) balls
   cover as many old vertices as possible. */
static int choose_nbrs(int oc, int *out) {
    static int cand[NMAX];
    static char taken[NMAX];
    static int gain_u[NMAX];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (color[u] == oc && deg[u] < d_) cand[nc++] = u;
    if (nc == 0) return 0;
    int best_cov = -1, best_k = 0;
    int bestset[DMAX];
    for (int r = 0; r < RESTARTS; r++) {
        Row cov;
        memset(cov, 0, sizeof(Row));
        memset(taken, 0, (size_t)n);
        int chosen[DMAX];
        int k = 0;
        while (k < d_) {
            int ng = 0;
            int bi = -1, bg = 0, ties = 0;
            for (int i = 0; i < nc; i++) {
                int u = cand[i];
                if (taken[u]) continue;
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(BM[u][w] & ~cov[w]);
                if (g > 0) gain_u[ng++] = u;
                if (g > bg) {
                    bg = g; bi = u; ties = 1;
                } else if (g == bg && g > 0) {
                    ties++;
                    if (rndint(ties) == 0) bi = u;
                }
            }
            if (bi < 0) break;
            if (r > 0 && ng > 0 && rnd01() < 0.3) bi = gain_u[rndint(ng)];
            taken[bi] = 1;
            chosen[k++] = bi;
            for (int w = 0; w < W; w++) cov[w] |= BM[bi][w];
        }
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cov[w]);
        if (c > best_cov) {
            best_cov = c;
            best_k = k;
            memcpy(bestset, chosen, sizeof(int) * (size_t)k);
        }
    }
    memcpy(out, bestset, sizeof(int) * (size_t)best_k);
    return best_k;
}

/* Insert a new vertex on side s, joined to a cover set of opposite-side vertices. */
static int grow_once(int s) {
    compute_balls(D_ - 1, BM);
    int ch[DMAX];
    int k = choose_nbrs(1 - s, ch);
    if (k == 0 || n + 1 >= NMAX) return 0;
    int v = n;
    set_n(n + 1);
    color[v] = s;
    deg[v] = 0;
    for (int i = 0; i < k; i++) raw_add(v, ch[i]);
    fill_pairs(0, 1 << 30);
    return 1;
}

static int sn;
static int scolor[NMAX], sdeg[NMAX];
static int sadj[NMAX][DMAX];

static void snapshot(void) {
    sn = n;
    memcpy(scolor, color, sizeof(int) * (size_t)n);
    memcpy(sdeg, deg, sizeof(int) * (size_t)n);
    memcpy(sadj, adj, sizeof(int) * DMAX * (size_t)n);
}

static void restore(void) {
    set_n(sn);
    memcpy(color, scolor, sizeof(int) * (size_t)n);
    memcpy(deg, sdeg, sizeof(int) * (size_t)n);
    memcpy(adj, sadj, sizeof(int) * DMAX * (size_t)n);
}

static int bestn = 0;
static int bdeg[NMAX];
static int badj[NMAX][DMAX];

static void save_best(void) {
    bestn = n;
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(int) * DMAX * (size_t)n);
}

static void print_best(void) {
    if (bestn == 0) {
        printf("0 0\n");
        return;
    }
    long long m = 0;
    for (int u = 0; u < bestn; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (badj[u][k] > u) m++;
    printf("%d %lld\n", bestn, m);
    for (int u = 0; u < bestn; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (badj[u][k] > u) printf("%d %d\n", u, badj[u][k]);
}

/* Simulated annealing on the bad-pair count. Returns the final cost; stops at 0. */
static long long repair(long long iters, double T0, double T1, long long cur) {
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now_sec() >= deadline) break;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        nops = 0;
        int ok = (rnd01() < 0.6) ? move_switch() : move_rewire();
        if (!ok) {
            nops = 0;
            continue;
        }
        fill_pairs(1, 4);
        long long nc = cost_now();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            nops = 0;
        } else {
            undo_log();
            nops = 0;
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double budget = atof(argv[4]);
    deadline = now_sec() + budget;

    if (d_ < 1 || d_ > DMAX || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > NMAX - 4 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    set_n(n0);
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        color[v] = -1;
    }
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { ok = 0; break; }
        if (a < 0 || b < 0 || a >= n || b >= n || a == b ||
            deg[a] >= d_ || deg[b] >= d_ || has_edge(a, b)) {
            ok = 0;
            break;
        }
        raw_add(a, b);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    static int queue[NMAX];
    for (int s = 0; s < n && ok; s++) {
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
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long long c = cost_now();
    if (c == 0) save_best();
    while (now_sec() < deadline) {
        if (c > 0) {
            c = repair(KICK_ITERS, 1.0, 0.1, c);
            if (c == 0 && n > bestn) save_best();
            continue;
        }
        if (n + 2 >= NMAX) break;
        snapshot();
        int grown = 0;
        int s0 = rndint(2);
        for (int t = 0; t < 2 && !grown; t++)
            grown = grow_once(t == 0 ? s0 : 1 - s0);
        if (!grown) break;
        c = cost_now();
        c = repair(GROW_ITERS, 0.7, 0.05, c);
        if (c == 0) {
            if (n > bestn) save_best();
        } else {
            restore();
            c = 0;
        }
    }
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (kept from the parent as starting points).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Python voltage-lift search over small groups (cheap starting points).
# ----------------------------------------------------------------------------

def _group_specs(lo, hi):
    """Cyclic groups and semidirect products Z_m x| Z_k with order in [lo, hi]."""
    specs = [("cyc", n) for n in range(lo, hi + 1)]
    for k in range(2, 13):
        for m in range(2, hi // k + 1):
            if not (lo <= m * k <= hi):
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append(("semi", m, k, r))
    return specs


def _make_group(spec):
    """Return (order, mul, inv) for a group spec from _group_specs."""
    if spec[0] == "cyc":
        return lib.cyclic_group(spec[1])
    _, m, k, r = spec
    return lib.semidirect_group(m, k, r)


def _random_base(a, d, rng, order):
    """Random base darts [i, j, g]: every A-vertex and B-vertex gets exactly d darts."""
    left = [i for i in range(a) for _ in range(d)]
    right = list(left)
    rng.shuffle(right)
    return [[left[k], right[k], rng.randrange(order)] for k in range(len(left))]


def _lift_adj(a, order, darts, R):
    """Adjacency lists of the lift. Side A is indices 0..a*order-1, side B is the rest."""
    N = 2 * a * order
    off = a * order
    adj = [[] for _ in range(N)]
    for i, j, g in darts:
        Rg = R[g]
        ba = i * order
        bb = off + j * order
        for x in range(order):
            u = ba + x
            v = bb + Rg[x]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _lift_cost(adj, a, order, D):
    """Number of (representative, vertex) pairs at distance > D, over the 2a representatives."""
    N = len(adj)
    total = 0
    sources = [i * order for i in range(a)] + [a * order + j * order for j in range(a)]
    for s in sources:
        seen = [False] * N
        seen[s] = True
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_edges(a, order, darts, R):
    """Sorted edge list of the lift (every edge joins side A to side B)."""
    off = a * order
    E = set()
    for i, j, g in darts:
        Rg = R[g]
        for x in range(order):
            E.add((i * order + x, off + j * order + Rg[x]))
    return sorted(E)


def _voltage_search(a, d, D, order, R, rng, iters, deadline):
    """Anneal darts of a random base until the lift has diameter <= D. Returns darts or None."""
    darts = _random_base(a, d, rng, order)
    cur = _lift_cost(_lift_adj(a, order, darts, R), a, order, D)
    for _ in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        new = [list(x) for x in darts]
        if rng.random() < 0.7:
            new[rng.randrange(len(new))][2] = rng.randrange(order)
        else:
            k1 = rng.randrange(len(new))
            k2 = rng.randrange(len(new))
            new[k1][1], new[k2][1] = new[k2][1], new[k1][1]
        c2 = _lift_cost(_lift_adj(a, order, new, R), a, order, D)
        if c2 <= cur or rng.random() < 0.02:
            darts, cur = new, c2
    return darts if cur == 0 else None


def _lift_stage(d, D, get_best, rng, deadline, consider):
    """Repeatedly search voltage lifts over random groups just above the current best order."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        best = get_best()
        avail = [a for a in (1, 2) if best // (2 * a) + 1 <= moore // (2 * a)]
        if not avail:
            return
        a = rng.choice(avail)
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 60)
        specs = _group_specs(lo, hi)
        if not specs:
            return
        spec = rng.choice(specs)
        order, mul, _ = _make_group(spec)
        R = [[mul(x, g) for x in range(order)] for g in range(order)]
        darts = _voltage_search(a, d, D, order, R, rng, 1500, deadline)
        if darts is not None:
            consider(2 * a * order, _lift_edges(a, order, darts, R))


# ----------------------------------------------------------------------------
# Driver: Python constructions, then the C cover-growth / annealing engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.93 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
            consider(n1, e1)
            if best_n >= moore:
                return best_n, list(best_e)

    # Quick voltage-lift starts, then a few twin-duplication pipelines.
    lift_end = start + 0.14 * time_limit
    if time.monotonic() < lift_end:
        _lift_stage(d, D, lambda: best_n, rng, lift_end, consider)

    trial_end = start + 0.20 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # New stage: C cover-growth with annealing repair, started from the best valid graph.
    c_budget = end - time.monotonic() - 1.5
    if D >= 2 and d <= 32 and c_budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=(best_n, best_e),
                             timeout=c_budget + 1.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
