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

#define MAXN 1100
#define MAXW 18
#define MAXD 40
#define MAXOPS 16

typedef uint64_t u64;
typedef u64 Row[MAXW];

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXD];
} Snap;

typedef struct { int type, a, b; } Op;

static int dgr, DIAM;
static int N;
static int side_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXD];
static int badv[MAXN];
static Row BA[MAXN], BB[MAXN];
static Op ops[MAXOPS];
static int nops;
static int cand[MAXN];
static u64 rs = 88172645463325252ULL;
static double deadline_;
static Snap bestS, accS;

static u64 rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---- adjacency primitives ---- */

static int has_edge(int a, int b) {
    for (int k = 0; k < deg_[a]; k++)
        if (nb_[a][k] == b) return 1;
    return 0;
}

static void add_e(int a, int b) {
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
}

static void rem_one(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) {
        if (nb_[a][k] == b) {
            nb_[a][k] = nb_[a][--deg_[a]];
            return;
        }
    }
}

static void del_e(int a, int b) {
    rem_one(a, b);
    rem_one(b, a);
}

/* logged operations, so a rejected annealing move can be undone */
static void do_add(int a, int b) {
    add_e(a, b);
    ops[nops].type = 0; ops[nops].a = a; ops[nops].b = b; nops++;
}
static void do_del(int a, int b) {
    del_e(a, b);
    ops[nops].type = 1; ops[nops].a = a; ops[nops].b = b; nops++;
}
static void undo_ops(void) {
    while (nops > 0) {
        Op o = ops[--nops];
        if (o.type == 0) del_e(o.a, o.b);
        else add_e(o.a, o.b);
    }
}

/* ---- distance cost: number of unordered pairs at distance > DIAM ---- */

static Row *balls(int r) {
    Row *cur = BA, *nxt = BB;
    int w = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt[v];
            memcpy(o, cur[v], sizeof(u64) * (size_t)w);
            for (int k = 0; k < deg_[v]; k++) {
                const u64 *s = cur[nb_[v][k]];
                for (int j = 0; j < w; j++) o[j] |= s[j];
            }
        }
        Row *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static long cost_full(void) {
    Row *b = balls(DIAM);
    int w = (N + 63) / 64;
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int j = 0; j < w; j++) c += pc(b[v][j]);
        badv[v] = N - c;
        tot += N - c;
    }
    return tot / 2;
}

/* ---- moves ---- */

/* random vertex on side s with deg > 0; if want_bad, prefer one with bad pairs */
static int rv(int s, int want_bad) {
    for (int t = 0; t < 80; t++) {
        int v = rndint(N);
        if (side_[v] != s || deg_[v] == 0) continue;
        if (want_bad && badv[v] == 0) continue;
        return v;
    }
    return -1;
}

/* double-edge switch: a,c on side s; b,e on side 1-s; degrees preserved */
static int move_switch(void) {
    int s = rndint(2);
    int a = rv(s, rndint(2));
    if (a < 0) a = rv(s, 0);
    int c = rv(s, 0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = nb_[a][rndint(deg_[a])];
    int e = nb_[c][rndint(deg_[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    do_del(a, b); do_del(c, e); do_add(a, e); do_add(c, b);
    return 1;
}

/* move one endpoint of an edge onto a vertex with spare degree */
static int move_rewire(void) {
    int s = rndint(2);
    int x = rv(s, rndint(2));
    if (x < 0) x = rv(s, 0);
    if (x < 0) return 0;
    int y = nb_[x][rndint(deg_[x])];
    int cnt = 0;
    for (int v = 0; v < N; v++) {
        if (side_[v] == 1 - s && deg_[v] < dgr && v != y && !has_edge(x, v))
            cand[cnt++] = v;
    }
    if (cnt == 0) return 0;
    int z = cand[rndint(cnt)];
    do_del(x, y);
    do_add(x, z);
    return 1;
}

/* add an edge between two random spare-degree vertices on opposite sides */
static int move_fill(void) {
    int a = -1, b = -1;
    for (int t = 0; t < 60 && a < 0; t++) {
        int v = rndint(N);
        if (side_[v] == 0 && deg_[v] < dgr) a = v;
    }
    for (int t = 0; t < 60 && b < 0; t++) {
        int v = rndint(N);
        if (side_[v] == 1 && deg_[v] < dgr) b = v;
    }
    if (a < 0 || b < 0 || has_edge(a, b)) return 0;
    do_add(a, b);
    return 1;
}

/* ---- growth ---- */

/* new vertex on a random side, joined greedily to a cover of the other side's
   radius-(DIAM-1) balls; saturated candidates lose one random edge */
static int grow_vertex(void) {
    if (N >= MAXN - 2) return 0;
    int s = rndint(2);
    Row *R = balls(DIAM - 1);
    int w = (N + 63) / 64;
    u64 covered[MAXW];
    memset(covered, 0, sizeof(covered));
    static int mark[MAXN];
    memset(mark, 0, sizeof(int) * (size_t)N);
    int chosen[MAXD];
    int nc = 0;
    while (nc < dgr) {
        int best = -1;
        double bsc = -1e18;
        for (int v = 0; v < N; v++) {
            if (side_[v] != 1 - s || mark[v]) continue;
            int g = 0;
            for (int j = 0; j < w; j++) g += pc(R[v][j] & ~covered[j]);
            if (g == 0) continue;
            double sc = g - (deg_[v] >= dgr ? 0.75 : 0.0) + 0.5 * rnd01();
            if (sc > bsc) { bsc = sc; best = v; }
        }
        if (best < 0) break;
        mark[best] = 1;
        chosen[nc++] = best;
        for (int j = 0; j < w; j++) covered[j] |= R[best][j];
    }
    if (nc == 0) return 0;
    int wv = N;
    N++;
    side_[wv] = s;
    deg_[wv] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg_[c] >= dgr) {
            int t = nb_[c][rndint(deg_[c])];
            del_e(c, t);
        }
        add_e(c, wv);
    }
    return 1;
}

/* remove vertex x, relabelling the last vertex into its slot */
static void kill_vertex(int x) {
    for (int k = 0; k < deg_[x]; k++) rem_one(nb_[x][k], x);
    deg_[x] = 0;
    int L = N - 1;
    if (x != L) {
        side_[x] = side_[L];
        deg_[x] = deg_[L];
        memcpy(nb_[x], nb_[L], sizeof(int) * MAXD);
        for (int k = 0; k < deg_[x]; k++) {
            int z = nb_[x][k];
            for (int j = 0; j < deg_[z]; j++)
                if (nb_[z][j] == L) nb_[z][j] = x;
        }
    }
    deg_[L] = 0;
    N--;
}

/* greedy addition of all possible cross edges (never increases cost) */
static void fill_all(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nbb = 0;
    for (int v = 0; v < N; v++) {
        if (deg_[v] >= dgr) continue;
        if (side_[v] == 0) A[na++] = v;
        else B[nbb++] = v;
    }
    for (int i = nbb - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = B[i]; B[i] = B[j]; B[j] = t;
    }
    for (int i = 0; i < na; i++) {
        int a = A[i];
        for (int j = 0; j < nbb; j++) {
            if (deg_[a] >= dgr) break;
            int b = B[j];
            if (deg_[b] < dgr && !has_edge(a, b)) add_e(a, b);
        }
    }
}

/* simulated annealing on bad-pair count; returns final cost (0 = valid) */
static long anneal(long iters, double T0, double T1) {
    long cur = cost_full();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > deadline_) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        nops = 0;
        int r = rndint(100);
        int ok;
        if (r < 60) ok = move_switch();
        else if (r < 90) ok = move_rewire();
        else ok = move_fill();
        if (!ok) { nops = 0; continue; }
        long nw = cost_full();
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            undo_ops();
        }
        nops = 0;
    }
    nops = 0;
    return cur;
}

/* ---- snapshots and I/O ---- */

static void snap(Snap *s) {
    s->n = N;
    memcpy(s->side, side_, sizeof(side_));
    memcpy(s->deg, deg_, sizeof(deg_));
    memcpy(s->nb, nb_, sizeof(nb_));
}

static void restore(const Snap *s) {
    N = s->n;
    memcpy(side_, s->side, sizeof(side_));
    memcpy(deg_, s->deg, sizeof(deg_));
    memcpy(nb_, s->nb, sizeof(nb_));
}

static void output(const Snap *s) {
    long m = 0;
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++)
            if (s->nb[v][k] > v) m++;
    printf("%d %ld\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++)
            if (s->nb[v][k] > v) printf("%d %d\n", v, s->nb[v][k]);
}

/* K_{d,d}: valid for DIAM >= 2 */
static void set_kdd(void) {
    int d = dgr;
    N = 2 * d;
    memset(deg_, 0, sizeof(deg_));
    for (int i = 0; i < N; i++) side_[i] = (i < d) ? 0 : 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_e(i, d + j);
}

/* read "n m" + edges; returns 0 (leaving state unspecified) if the input is unusable */
static int load_input(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 64 || m < 0) return 0;
    N = n;
    for (int v = 0; v < N; v++) { deg_[v] = 0; side_[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) return 0;
        if (deg_[u] >= dgr || deg_[v] >= dgr) return 0;
        if (has_edge(u, v)) return 0;
        add_e(u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < N; s++) {
        if (side_[s] != -1) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg_[u]; k++) {
                int v = nb_[u][k];
                if (side_[v] == -1) {
                    side_[v] = 1 - side_[u];
                    q[qt++] = v;
                } else if (side_[v] == side_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* ---- main ---- */

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (D < 2 || d < 1) {
        printf("1 0\n");
        return 0;
    }
    dgr = d;
    if (dgr > MAXD - 4) dgr = MAXD - 4;
    DIAM = D;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    deadline_ = now() + tl;
    nops = 0;

    int loaded = load_input();
    if (!loaded) set_kdd();
    if (cost_full() != 0) set_kdd();

    snap(&bestS);
    snap(&accS);

    int fails = 0;
    long iters = 5000;
    double T0 = 1.2, T1 = 0.05;
    while (now() < deadline_) {
        restore(&accS);
        if (N > 8 && rndint(4) == 0) kill_vertex(rndint(N));
        if (!grow_vertex()) break;
        fill_all();
        long c = anneal(iters, T0, T1);
        if (c == 0) {
            snap(&accS);
            fails = 0;
            if (N > bestS.n) snap(&bestS);
        } else {
            fails++;
            if (fails >= 30) {
                restore(&bestS);
                snap(&accS);
                fails = 0;
            }
        }
    }
    output(&bestS);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (Python): projective plane for D = 3, generalized
# quadrangle W(q) for D >= 4, followed by light cover growth and twins.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 keeps setup fast)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of the other side."""
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    try:
        base = _best_pg(d) if D == 3 else _best_gq(d)
    except Exception:
        base = None
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        if lib.is_valid(n0, e0, d, D):
            n1, e1 = _grow(n0, e0, d, D, t0 + 0.12 * time_limit, rng, attempts=30)
            consider(n1, e1)
            n2, e2 = _duplicate_twins(n1, e1, d, rng)
            e2 = _saturate_edges(n2, e2, d, rng)
            consider(n2, e2)

    # C annealing engine: grows the best start with cover vertices, repairs by
    # bipartite switches / endpoint rewiring on bad-pair cost, and kills+regrows.
    elapsed = time.monotonic() - t0
    avail = 0.9 * time_limit - elapsed - 2.0
    if avail >= 1.0:
        budget = avail * 0.92
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=avail + 0.5)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0], list(best[1])
