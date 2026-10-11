import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine. Cover-guided vertex insertion with stealing, then annealing repair
# by bipartite double-edge switches. A plateau move kills vertices and re-adds
# them. Bitset balls give the exact cost (number of pairs at distance > D).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAPMAX 4096
#define WMAX 64
#define MAXD 64

typedef uint64_t u64;

typedef struct {
    int used, A;
    int side[CAPMAX];
    int alive[CAPMAX];
    int deg[CAPMAX];
    int nb[CAPMAX][MAXD];
} State;

static int d_, D_;
static int used, W, A, cap_lim;
static int side[CAPMAX], alive[CAPMAX], deg[CAPMAX];
static int nb[CAPMAX][MAXD];
static u64 BALL[CAPMAX][WMAX];
static u64 COV[CAPMAX][WMAX];
static u64 TMP[CAPMAX][WMAX];
static u64 rng_s = 88172645463325252ULL;
static clock_t t_end;
static State st_snap, st_best;

static u64 rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}

static int rndint(int n) { return (int)(rnd64() % (u64)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int time_up(void) { return clock() >= t_end; }

static void set_W(void) {
    W = (used + 63) >> 6;
    if (W < 1) W = 1;
}

static void compute_ball(int r, u64 (*dst)[WMAX]) {
    int v, s, w, k;
    for (v = 0; v < used; v++) {
        for (w = 0; w < W; w++) dst[v][w] = 0;
        dst[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (s = 0; s < r; s++) {
        for (v = 0; v < used; v++) {
            for (w = 0; w < W; w++) TMP[v][w] = dst[v][w];
            for (k = 0; k < deg[v]; k++) {
                const u64 *src = dst[nb[v][k]];
                for (w = 0; w < W; w++) TMP[v][w] |= src[w];
            }
        }
        for (v = 0; v < used; v++)
            for (w = 0; w < W; w++) dst[v][w] = TMP[v][w];
    }
}

static long long cost_full(void) {
    int v, w;
    long long tot = 0;
    compute_ball(D_, BALL);
    for (v = 0; v < used; v++) {
        int c = 0;
        if (!alive[v]) continue;
        for (w = 0; w < W; w++) c += pc64(BALL[v][w]);
        tot += A - c;
    }
    return tot / 2;
}

static int has_edge(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++)
        if (nb[a][k] == b) return 1;
    return 0;
}

static void half_del(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    half_del(a, b);
    half_del(b, a);
}

static void shuffle_ints(int *x, int n) {
    int i;
    for (i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (never increases cost). */
static void fill(void) {
    static int L[CAPMAX], R[CAPMAX];
    int nl = 0, nr = 0, v, i, j;
    for (v = 0; v < used; v++) {
        if (!alive[v] || deg[v] >= d_) continue;
        if (side[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_ints(L, nl);
    shuffle_ints(R, nr);
    for (i = 0; i < nl; i++) {
        int a = L[i];
        for (j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] >= d_ || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* Double-edge switches (degrees preserved) minimising the bad-pair count. */
static int anneal(int iters, double T0, double T1) {
    static int L0[CAPMAX];
    int n0 = 0, it, v;
    long long cur, nw, delta;
    cur = cost_full();
    if (cur == 0) return 1;
    for (it = 0; it < iters; it++) {
        if ((it & 255) == 0) {
            if (time_up()) return 0;
            fill();
            cur = cost_full();
            if (cur == 0) return 1;
            n0 = 0;
            for (v = 0; v < used; v++)
                if (alive[v] && side[v] == 0 && deg[v] > 0) L0[n0++] = v;
            if (n0 < 2) return 0;
        }
        {
            double T = T0 + (T1 - T0) * (double)it / (double)iters;
            int a = L0[rndint(n0)];
            int c = L0[rndint(n0)];
            int b, e;
            if (a == c || deg[a] == 0 || deg[c] == 0) continue;
            b = nb[a][rndint(deg[a])];
            e = nb[c][rndint(deg[c])];
            if (e == b || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            nw = cost_full();
            delta = nw - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nw;
                if (cur == 0) return 1;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        }
    }
    return cur == 0;
}

static int new_slot(void) {
    int v;
    for (v = 0; v < used; v++)
        if (!alive[v] && deg[v] == 0) return v;
    if (used >= cap_lim) return -1;
    v = used++;
    alive[v] = 0;
    deg[v] = 0;
    side[v] = 0;
    set_W();
    return v;
}

static void kill_vertex(int x) {
    while (deg[x] > 0) {
        int t = nb[x][0];
        del_edge(x, t);
    }
    alive[x] = 0;
    A--;
}

/* New vertex on a random side, joined to a greedy cover (radius D-1) of the other side. */
static int try_add_vertex(int iters) {
    static int chosen[MAXD];
    u64 covered[WMAX];
    int s, v, k, c, w, nc = 0;
    s = rndint(2);
    v = new_slot();
    if (v < 0) return 0;
    alive[v] = 1;
    side[v] = s;
    deg[v] = 0;
    A++;
    compute_ball(D_ - 1, COV);
    for (w = 0; w < W; w++) covered[w] = 0;
    for (k = 0; k < d_; k++) {
        int best = -1;
        double bs = -1.0;
        for (c = 0; c < used; c++) {
            int g = 0, dup = 0, j;
            double sc;
            if (!alive[c] || side[c] == s) continue;
            for (j = 0; j < nc; j++)
                if (chosen[j] == c) { dup = 1; break; }
            if (dup) continue;
            for (w = 0; w < W; w++) g += pc64(COV[c][w] & ~covered[w]);
            if (g == 0) continue;
            sc = g + 0.5 * rnd01();
            if (sc > bs) { bs = sc; best = c; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (w = 0; w < W; w++) covered[w] |= COV[best][w];
    }
    for (k = 0; k < nc; k++) {
        c = chosen[k];
        if (deg[c] >= d_) {
            int t = nb[c][rndint(deg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
    fill();
    return anneal(iters, 0.6, 0.05);
}

/* Kill k vertices, repair, then re-add k + extra vertices. */
static int move_kill_readd(int k, int extra, int iters) {
    int i, x;
    if (A <= k + 1) return 0;
    for (i = 0; i < k; i++) {
        do { x = rndint(used); } while (!alive[x]);
        kill_vertex(x);
    }
    fill();
    if (!anneal(iters, 0.6, 0.05)) return 0;
    for (i = 0; i < k + extra; i++)
        if (!try_add_vertex(iters)) return 0;
    return 1;
}

static void save_state(State *s) {
    s->used = used;
    s->A = A;
    memcpy(s->side, side, sizeof(int) * (size_t)used);
    memcpy(s->alive, alive, sizeof(int) * (size_t)used);
    memcpy(s->deg, deg, sizeof(int) * (size_t)used);
    memcpy(s->nb, nb, sizeof(nb[0]) * (size_t)used);
}

static void load_state(const State *s) {
    used = s->used;
    A = s->A;
    memcpy(side, s->side, sizeof(int) * (size_t)used);
    memcpy(alive, s->alive, sizeof(int) * (size_t)used);
    memcpy(deg, s->deg, sizeof(int) * (size_t)used);
    memcpy(nb, s->nb, sizeof(nb[0]) * (size_t)used);
    set_W();
}

static int load_start(void) {
    int n, m, e, i, a, b, changed;
    int *eu, *ev, *col;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n == 0) {
        int h = d_;
        used = 2 * h;
        for (i = 0; i < used; i++) {
            alive[i] = 1;
            side[i] = (i < h) ? 0 : 1;
            deg[i] = 0;
        }
        for (i = 0; i < h; i++)
            for (a = 0; a < h; a++)
                add_edge(i, h + a);
        return 1;
    }
    if (n < 0 || n > 2000 || m < 0 || m > n * d_) return 0;
    eu = malloc(sizeof(int) * (size_t)(m + 1));
    ev = malloc(sizeof(int) * (size_t)(m + 1));
    col = malloc(sizeof(int) * (size_t)n);
    if (!eu || !ev || !col) return 0;
    for (e = 0; e < m; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) return 0;
        if (eu[e] < 0 || eu[e] >= n || ev[e] < 0 || ev[e] >= n || eu[e] == ev[e]) return 0;
    }
    for (i = 0; i < n; i++) col[i] = -1;
    for (i = 0; i < n; i++) {
        if (col[i] >= 0) continue;
        col[i] = 0;
        changed = 1;
        while (changed) {
            changed = 0;
            for (e = 0; e < m; e++) {
                a = eu[e];
                b = ev[e];
                if (col[a] >= 0 && col[b] < 0) { col[b] = 1 - col[a]; changed = 1; }
                else if (col[b] >= 0 && col[a] < 0) { col[a] = 1 - col[b]; changed = 1; }
            }
        }
    }
    for (e = 0; e < m; e++)
        if (col[eu[e]] == col[ev[e]]) return 0;
    for (i = 0; i < n; i++) {
        alive[i] = 1;
        side[i] = col[i];
        deg[i] = 0;
    }
    used = n;
    for (e = 0; e < m; e++) {
        a = eu[e];
        b = ev[e];
        if (deg[a] >= d_ || deg[b] >= d_ || has_edge(a, b)) return 0;
        add_edge(a, b);
    }
    free(eu);
    free(ev);
    free(col);
    return 1;
}

int main(int argc, char **argv) {
    int i, k, cnt = 0, edges = 0, ok_in;
    static int idx[CAPMAX];
    double budget;
    State *b;
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rng_s ^= strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rng_s == 0) rng_s = 1;
    budget = atof(argv[4]);
    t_end = clock() + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    ok_in = load_start();
    if (!ok_in) {
        printf("0 0\n");
        return 0;
    }
    set_W();
    A = 0;
    for (i = 0; i < used; i++) if (alive[i]) A++;
    cap_lim = used + 1200;
    if (cap_lim > CAPMAX) cap_lim = CAPMAX;
    if (cost_full() != 0) {
        if (!anneal(300000, 0.8, 0.05)) {
            printf("0 0\n");
            return 0;
        }
    }
    save_state(&st_best);

    while (!time_up()) {
        int r = rndint(100);
        int ok;
        save_state(&st_snap);
        if (r < 55) {
            ok = try_add_vertex(1500);
        } else if (r < 85) {
            ok = move_kill_readd(1, 0, 2000);
        } else {
            ok = move_kill_readd(1 + rndint(2), 1, 3000);
        }
        if (!ok) {
            load_state(&st_snap);
        } else if (A > st_best.A) {
            save_state(&st_best);
        }
    }

    b = &st_best;
    for (i = 0; i < b->used; i++) {
        if (b->alive[i]) idx[i] = cnt++;
        else idx[i] = -1;
    }
    for (i = 0; i < b->used; i++) {
        if (!b->alive[i]) continue;
        for (k = 0; k < b->deg[i]; k++)
            if (b->nb[i][k] > i) edges++;
    }
    printf("%d %d\n", cnt, edges);
    for (i = 0; i < b->used; i++) {
        if (!b->alive[i]) continue;
        for (k = 0; k < b->deg[i]; k++) {
            int j = b->nb[i][k];
            if (j > i) printf("%d %d\n", idx[i], idx[j]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q <= 9 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python growth helpers (cheap pre-pass before the C engine).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=30):
    """Add whole vertices whose neighbourhoods cover all vertices within D-1 of the other side."""
    if D < 2:
        return n, edges
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
    """Join deficient opposite-side vertices (cross-side edges only shorten distances)."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=30):
    """Repeatedly add cover vertices, then saturate spare degree."""
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


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base plus cheap Python growth.
    try:
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
                consider(n1, e1)
    except Exception:
        pass

    # C engine: cover-guided insertion plus annealing repair, started from the best graph.
    if D >= 2 and best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - start
        budget = 0.85 * time_limit - elapsed - 1.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=max(1.0, time_limit - elapsed - 0.5))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
