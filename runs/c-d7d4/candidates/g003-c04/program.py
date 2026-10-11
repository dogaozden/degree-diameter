"""Graph search for bipartite graphs with bounded degree and diameter.

Python builds the starting graph (projective plane, generalized quadrangle W(q),
cover extension, non-cyclic group lifts). A C annealing engine then grows it:
each new vertex's neighbours are chosen greedily so that their radius-(D-1) balls
cover the graph, and simulated annealing over degree-preserving bipartite edge swaps
minimises the number of vertex pairs at distance > D.
"""
import itertools
import math
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

#define MAXN 2048
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD / 2)
#define LOGCAP (1 << 18)
#define STALL_STEPS 20000
#define TEMP 0.4

static int d_, D_, n_, cap_;
static int deg_[MAXN];
static int nb_[MAXN][MAXD];
static unsigned char adj_[MAXN][MAXN];
static int side_[MAXN];
static uint64_t ball_[2][MAXN][MAXW];

static int bn_, bm_;
static int bu_[MAXE], bv_[MAXE];
static int eu_[MAXE], ev_[MAXE];
static int satA_[MAXN], satB_[MAXN];
static int cand_[MAXN], gain_[MAXN], qbuf_[MAXN];
static char used_[MAXN];

typedef struct { int type, a, b; } Op;
static Op log_[LOGCAP];
static int nlog_ = 0, logging_ = 0, logover_ = 0;

static uint64_t rs_ = 88172645463325252ULL;

static uint64_t rng_next(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rnd_int(int k) { return (int)(rng_next() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(rng_next() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---------- raw graph edits ---------- */

static void add_raw(int a, int b) {
    adj_[a][b] = adj_[b][a] = 1;
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
}

static void del_one(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (nb_[a][i] == b) {
            nb_[a][i] = nb_[a][--deg_[a]];
            return;
        }
    }
}

static void rem_raw(int a, int b) {
    adj_[a][b] = adj_[b][a] = 0;
    del_one(a, b);
    del_one(b, a);
}

static void push_log(int t, int a, int b) {
    if (nlog_ >= LOGCAP) { logover_ = 1; return; }
    log_[nlog_].type = t;
    log_[nlog_].a = a;
    log_[nlog_].b = b;
    nlog_++;
}

static void add_edge(int a, int b) {
    add_raw(a, b);
    if (logging_) push_log(1, a, b);
}

static void rem_edge(int a, int b) {
    rem_raw(a, b);
    if (logging_) push_log(0, a, b);
}

static void undo_all(void) {
    for (int i = nlog_ - 1; i >= 0; i--) {
        if (log_[i].type) rem_raw(log_[i].a, log_[i].b);
        else add_raw(log_[i].a, log_[i].b);
    }
    nlog_ = 0;
}

/* ---------- distance cost ---------- */

/* Bitmask balls of radius r over the current n_ vertices; returns buffer index. */
static int compute_balls(int r) {
    int n = n_, W = (n + 63) >> 6;
    int cur = 0;
    for (int v = 0; v < n; v++) {
        memset(ball_[0][v], 0, sizeof(uint64_t) * W);
        ball_[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = ball_[nx][v];
            memcpy(dst, ball_[cur][v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *src = ball_[cur][nb_[v][i]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        cur = nx;
    }
    return cur;
}

/* Number of unordered pairs at distance > D_ (unreachable pairs included). */
static long long eval_cost(void) {
    int n = n_, W = (n + 63) >> 6;
    int cur = compute_balls(D_);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(ball_[cur][v][w]);
        bad += n - pc;
    }
    return bad / 2;
}

/* ---------- moves ---------- */

static int pick_side(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rnd_int(n_);
        if (side_[v] == s && deg_[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving 2-swap: (a,b),(c,e) -> (a,e),(c,b), a and c on side 0. */
static int swap_move(void) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = nb_[a][rnd_int(deg_[a])];
    int e = nb_[c][rnd_int(deg_[c])];
    if (b == e) return 0;
    if (adj_[a][e] || adj_[c][b]) return 0;
    rem_edge(a, b);
    rem_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    return 1;
}

static void shuffle_arr(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Adding edges never increases distances, so fill spare degree greedily. */
static void saturate(void) {
    int na = 0, nbk = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] >= d_) continue;
        if (side_[v] == 0) satA_[na++] = v;
        else satB_[nbk++] = v;
    }
    if (na == 0 || nbk == 0) return;
    shuffle_arr(satA_, na);
    shuffle_arr(satB_, nbk);
    for (int i = 0; i < na; i++) {
        int a = satA_[i];
        for (int j = 0; j < nbk && deg_[a] < d_; j++) {
            int b = satB_[j];
            if (deg_[b] < d_ && !adj_[a][b]) add_edge(a, b);
        }
    }
}

/*
 * Cover-based vertex insertion: pick d_ opposite-side neighbours whose radius-(D-1)
 * balls cover as much as possible (randomised greedy). Full neighbours give up one
 * edge to make room; the saturation step later refills the slack.
 */
static int add_vertex(void) {
    if (n_ >= cap_ || d_ < 1) return 0;
    int n = n_, W = (n + 63) >> 6;
    int c = (int)(rng_next() & 1ULL);
    int cur = compute_balls(D_ - 1);
    uint64_t covered[MAXW];
    memset(covered, 0, sizeof(uint64_t) * W);
    memset(used_, 0, (size_t)n);
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (side_[u] != c) cand_[nc++] = u;

    int chosen[MAXD];
    int nch = 0;
    while (nch < d_) {
        int bestg = 0;
        for (int k = 0; k < nc; k++) {
            int u = cand_[k];
            if (used_[u]) { gain_[k] = 0; continue; }
            int g = 0;
            for (int w = 0; w < W; w++) g += popc64(ball_[cur][u][w] & ~covered[w]);
            gain_[k] = g;
            if (g > bestg) bestg = g;
        }
        if (bestg == 0) break;
        int thr = bestg;
        if (bestg > 1 && rnd_unit() < 0.3) thr = bestg - 1;
        int cnt = 0;
        for (int k = 0; k < nc; k++)
            if (gain_[k] >= thr && gain_[k] > 0) cnt++;
        int pick = rnd_int(cnt);
        int sel = -1;
        for (int k = 0; k < nc; k++) {
            if (gain_[k] >= thr && gain_[k] > 0) {
                if (pick == 0) { sel = cand_[k]; break; }
                pick--;
            }
        }
        if (sel < 0) break;
        used_[sel] = 1;
        chosen[nch++] = sel;
        for (int w = 0; w < W; w++) covered[w] |= ball_[cur][sel][w];
    }

    int v = n_;
    n_++;
    side_[v] = c;
    deg_[v] = 0;
    for (int i = 0; i < nch; i++) {
        int u = chosen[i];
        if (deg_[u] >= d_) {
            int x = nb_[u][rnd_int(deg_[u])];
            rem_edge(u, x);
        }
        add_edge(v, u);
    }
    return 1;
}

/* ---------- best-graph snapshot ---------- */

static void save_best(void) {
    bn_ = n_;
    bm_ = 0;
    for (int v = 0; v < n_; v++)
        for (int i = 0; i < deg_[v]; i++) {
            int u = nb_[v][i];
            if (u > v && bm_ < MAXE) {
                bu_[bm_] = v;
                bv_[bm_] = u;
                bm_++;
            }
        }
}

static void restore_best(void) {
    for (int v = 0; v < n_; v++) {
        for (int i = 0; i < deg_[v]; i++) adj_[v][nb_[v][i]] = 0;
        deg_[v] = 0;
    }
    n_ = bn_;
    for (int i = 0; i < bm_; i++) add_raw(bu_[i], bv_[i]);
}

static void print_graph(int n, int m, const int *us, const int *vs) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", us[i], vs[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs_ = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rng_next();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || n0 > MAXN) n0 = 0;
    if (m0 < 0) m0 = 0;
    int mr = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (mr < MAXE) { eu_[mr] = u; ev_[mr] = v; mr++; }
    }

    if (n0 < 2 || d_ < 1 || d_ > MAXD || D_ < 2) {
        print_graph(n0, mr, eu_, ev_);
        return 0;
    }

    n_ = n0;
    cap_ = n0 + 400;
    if (cap_ > MAXN) cap_ = MAXN;
    for (int i = 0; i < mr; i++) {
        int u = eu_[i], v = ev_[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (adj_[u][v] || deg_[u] >= d_ || deg_[v] >= d_) continue;
        add_raw(u, v);
    }

    /* Two-colour by BFS, then drop any edge joining equal colours. */
    static int queue_[MAXN];
    for (int v = 0; v < n0; v++) side_[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (side_[s] != -1) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int x = queue_[qh++];
            for (int i = 0; i < deg_[x]; i++) {
                int y = nb_[x][i];
                if (side_[y] == -1) {
                    side_[y] = 1 - side_[x];
                    queue_[qt++] = y;
                }
            }
        }
    }
    for (int v = 0; v < n0; v++)
        for (int i = deg_[v] - 1; i >= 0; i--) {
            if (i >= deg_[v]) continue;
            int u = nb_[v][i];
            if (side_[u] == side_[v]) rem_raw(v, u);
        }

    long long cost = eval_cost();
    int has_best = 0;
    if (cost == 0) { save_best(); has_best = 1; }
    long long mincost = cost, stall = 0;
    logging_ = 0;
    nlog_ = 0;

    clock_t c0 = clock();
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < tl) {
        if (cost == 0) {
            save_best();
            has_best = 1;
            logging_ = 0;
            if (!add_vertex()) break;
            cost = eval_cost();
            mincost = cost;
            stall = 0;
            continue;
        }

        logging_ = 1;
        nlog_ = 0;
        logover_ = 0;
        swap_move();
        saturate();
        if (nlog_ > 0 || logover_) {
            logging_ = 0;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || logover_ || rnd_unit() < exp(-(double)delta / TEMP)) {
                cost = nc;
            } else {
                undo_all();
            }
        }
        logging_ = 0;
        nlog_ = 0;

        if (cost < mincost) {
            mincost = cost;
            stall = 0;
        } else if (++stall > STALL_STEPS) {
            if (has_best) {
                restore_best();
                if (!add_vertex()) break;
                cost = eval_cost();
            }
            mincost = cost;
            stall = 0;
        }
    }

    if (has_best) print_graph(bn_, bm_, bu_, bv_);
    else print_graph(n0, mr, eu_, ev_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
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
    """Greedy set cover of `full` by at most d candidate vertices (optionally randomised)."""
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
    """Hill-climb dart voltages in a non-cyclic group over a random d-regular base."""
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.85 * time_limit
    end = t0 + total
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Structured base: PG(2,q) for D = 3, W(q) for D >= 4.
    base = _best_pg(d) if D == 3 else _best_gq(d)
    if base is not None:
        n0, e0 = base
        e0 = _saturate_edges(n0, e0, d, rng)
        consider(n0, e0)
        if best_n < lib.moore_bound(d, D):
            ext_end = t0 + 0.25 * total
            attempts = 0
            while time.monotonic() < ext_end and attempts < 20:
                attempts += 1
                sub = random.Random(rng.randrange(1 << 30))
                n2, e2 = _grow(n0, e0, d, D, ext_end, sub)
                consider(n2, e2)

    # Non-cyclic group lifts (parent family), a bounded share of the budget.
    if best_n < lib.moore_bound(d, D):
        group_end = t0 + 0.5 * total
        group_sizes = [1, 2, 3, 4]
        group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
        while time.monotonic() < group_end:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, group_end)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor

    # C engine: cover-based vertex insertion + annealing on degree-preserving swaps.
    budget = end - time.monotonic() - 1.0
    if budget >= 2.0 and best_n < lib.moore_bound(d, D):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
