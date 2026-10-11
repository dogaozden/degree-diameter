# Island g007-c12 extension: a C engine that anneals bipartite graphs with
# Python-seeded starts. New idea in the C stage: "greedy cover insertion".
# Each insertion adds a non-adjacent pair (x on side A, y on side B). Each new
# vertex is wired to the opposite side by greedily maximising newly covered
# vertices (balls of radius D-1 of the candidate neighbours). When a candidate is
# full, one of its edges is stolen (edge moved to the new vertex, which keeps
# degrees bounded). A degree-preserving simulated annealing (switches, plus
# endpoint moves into deficient vertices, plus greedy fill of deficient pairs)
# then removes the remaining bad pairs (distance > D). Cost = bad pairs, computed
# exactly by bit-parallel balls. The best valid graph is restored after failed
# attempts. The Python stage keeps the parent's GQ/PG base, cover growth, voltage
# lifts and twin trials, then hands the best graph to C.
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WMAX 16
#define DMAX 24
#define MAXE 12800
#define MAXLOG 40000

static int d_, D_;
static int N;
static int side[MAXN];
static int deg[MAXN];
static int nbr[MAXN][DMAX];
static unsigned char adjm[MAXN][MAXN];
static int slist[2][MAXN];
static int scnt[2];

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return m <= 0 ? 0 : (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double t0, t_budget;
static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int timeup(void) { return wall() - t0 >= t_budget; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---------- edge operations with an undo log ---------- */
static int logging, logn, logover;
static int loga[MAXLOG], logb[MAXLOG];
static unsigned char logop[MAXLOG];

static void push_log(int op, int a, int b) {
    if (!logging) return;
    if (logn >= MAXLOG) { logover = 1; return; }
    logop[logn] = (unsigned char)op;
    loga[logn] = a;
    logb[logn] = b;
    logn++;
}
static void remove_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nbr[a][i] == b) {
            nbr[a][i] = nbr[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void add_edge(int a, int b) {
    nbr[a][deg[a]++] = b;
    nbr[b][deg[b]++] = a;
    adjm[a][b] = 1;
    adjm[b][a] = 1;
    push_log(1, a, b);
}
static void del_edge(int a, int b) {
    remove_from(a, b);
    remove_from(b, a);
    adjm[a][b] = 0;
    adjm[b][a] = 0;
    push_log(0, a, b);
}
static void undo_log(void) {
    int saved = logging;
    logging = 0;
    for (int i = logn - 1; i >= 0; i--) {
        if (logop[i]) del_edge(loga[i], logb[i]);
        else add_edge(loga[i], logb[i]);
    }
    logn = 0;
    logging = saved;
}
static int new_vertex(int s) {
    int v = N++;
    side[v] = s;
    deg[v] = 0;
    slist[s][scnt[s]++] = v;
    return v;
}

/* ---------- bit-parallel balls and cost ---------- */
static uint64_t ballC[MAXN][WMAX], ballR[MAXN][WMAX], tmpB[MAXN][WMAX];

static void balls_into(int r, uint64_t (*out)[WMAX]) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) tmpB[v][w] = out[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nbr[v][i];
                for (int w = 0; w < W; w++) tmpB[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) out[v][w] = tmpB[v][w];
    }
}

/* number of unordered pairs at distance > D_ */
static int cost_eval(void) {
    balls_into(D_, ballC);
    int W = (N + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(ballC[v][w]);
        bad += N - c;
    }
    return (int)(bad / 2);
}

/* ---------- random helpers ---------- */
static int rand_with_deg(int s) {
    if (scnt[s] == 0) return -1;
    for (int t = 0; t < 30; t++) {
        int v = slist[s][rndint(scnt[s])];
        if (deg[v] > 0) return v;
    }
    return -1;
}
static int rand_deficient(int s) {
    if (scnt[s] == 0) return -1;
    int off = rndint(scnt[s]);
    for (int i = 0; i < scnt[s]; i++) {
        int v = slist[s][(i + off) % scnt[s]];
        if (deg[v] < d_) return v;
    }
    return -1;
}

/* add edges between deficient non-adjacent opposite-side vertices (never hurts) */
static void fill(void) {
    static int def0[MAXN], def1[MAXN];
    int c0 = 0, c1 = 0;
    for (int i = 0; i < scnt[0]; i++) { int v = slist[0][i]; if (deg[v] < d_) def0[c0++] = v; }
    for (int i = 0; i < scnt[1]; i++) { int v = slist[1][i]; if (deg[v] < d_) def1[c1++] = v; }
    if (c0 == 0 || c1 == 0) return;
    int o0 = rndint(c0), o1 = rndint(c1);
    for (int i = 0; i < c0; i++) {
        int a = def0[(i + o0) % c0];
        for (int j = 0; j < c1 && deg[a] < d_; j++) {
            int b = def1[(j + o1) % c1];
            if (deg[b] < d_ && !adjm[a][b]) add_edge(a, b);
        }
    }
}

/* ---------- moves ---------- */
/* degree-preserving double edge switch */
static int do_switch(void) {
    int s = rndint(2);
    int a = rand_with_deg(s), a2 = rand_with_deg(s);
    if (a < 0 || a2 < 0 || a == a2) return 0;
    int b = nbr[a][rndint(deg[a])];
    int b2 = nbr[a2][rndint(deg[a2])];
    if (b == b2 || adjm[a][b2] || adjm[a2][b]) return 0;
    del_edge(a, b);
    del_edge(a2, b2);
    add_edge(a, b2);
    add_edge(a2, b);
    return 1;
}

/* move an edge endpoint on side s to a deficient vertex on side s */
static int do_move(int s) {
    int x = rand_deficient(s);
    if (x < 0) return 0;
    int a = rand_with_deg(s);
    if (a < 0 || a == x) return 0;
    int b = nbr[a][rndint(deg[a])];
    if (adjm[x][b]) return 0;
    del_edge(a, b);
    add_edge(x, b);
    return 1;
}

/* simulated annealing on bad-pair count; returns final cost */
static int sa_run(int iters, double T0, double T1) {
    int cur = cost_eval();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && timeup()) break;
        double T = T0 + (T1 - T0) * ((double)it / (double)iters);
        logn = 0;
        logover = 0;
        logging = 1;
        int ok = (rnd01() < 0.4) ? do_move(rndint(2)) : do_switch();
        if (!ok) { logn = 0; logging = 0; continue; }
        fill();
        int nc = cost_eval();
        logging = 0;
        int accept = (nc <= cur) || logover ||
                     (rnd01() < exp(-(double)(nc - cur) / T));
        if (accept) cur = nc;
        else undo_log();
        logn = 0;
    }
    logging = 0;
    logn = 0;
    return cur;
}

/* ---------- NEW: greedy cover insertion ---------- */
/* Attach new vertex nv (side s, degree 0) to up to d_ vertices of side 1-s,
   each step choosing the candidate whose radius-(D-1) ball covers the most
   still-uncovered vertices. A full candidate gives up one of its edges. */
static void greedy_attach(int nv, int s) {
    balls_into(D_ - 1, ballR);
    int W = (N + 63) >> 6;
    uint64_t cov[WMAX];
    for (int w = 0; w < W; w++) cov[w] = 0;
    cov[nv >> 6] |= 1ULL << (nv & 63);
    for (int step = 0; step < d_; step++) {
        int best = -1, bestg = -1, ties = 0;
        for (int i = 0; i < scnt[1 - s]; i++) {
            int c = slist[1 - s][i];
            if (c == nv || adjm[nv][c]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(ballR[c][w] & ~cov[w]);
            if (g > bestg) { bestg = g; best = c; ties = 1; }
            else if (g == bestg) { ties++; if (rndint(ties) == 0) best = c; }
        }
        if (best < 0 || bestg <= 0) break;
        if (deg[best] < d_) {
            add_edge(nv, best);
        } else {
            int p = nbr[best][rndint(deg[best])];
            del_edge(p, best);
            add_edge(nv, best);
        }
        for (int w = 0; w < W; w++) cov[w] |= ballR[best][w];
    }
}

/* insert a non-adjacent pair (one vertex per side) with greedy cover attachment */
static void insert_pair(void) {
    if (N + 2 > MAXN) return;
    int x = new_vertex(0);
    greedy_attach(x, 0);
    int y = new_vertex(1);
    greedy_attach(y, 1);
    fill();
}

/* ---------- snapshot / restore ---------- */
static int ssN, ssM;
static int ssSide[MAXN];
static int ssA[MAXE], ssB[MAXE];

static void snapshot(void) {
    ssN = N;
    ssM = 0;
    for (int v = 0; v < N; v++) {
        ssSide[v] = side[v];
        for (int i = 0; i < deg[v]; i++) {
            int u = nbr[v][i];
            if (v < u && ssM < MAXE) { ssA[ssM] = v; ssB[ssM] = u; ssM++; }
        }
    }
}

static void restore_state(void) {
    logging = 0;
    logn = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) adjm[v][nbr[v][i]] = 0;
    N = 0;
    scnt[0] = 0;
    scnt[1] = 0;
    for (int v = 0; v < ssN; v++) new_vertex(ssSide[v]);
    for (int i = 0; i < ssM; i++) add_edge(ssA[i], ssB[i]);
}

/* ---------- main ---------- */
int main(int argc, char **argv) {
    t0 = wall();
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    t_budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 88172645463325252ULL;
    for (int i = 0; i < 4; i++) rnd64();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN || m < 0 || m > MAXE ||
        d_ < 1 || d_ > DMAX || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    int bad = 0;
    for (int i = 0; i < m && !bad; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
            deg[u] >= d_ || deg[v] >= d_) bad = 1;
        else add_edge(u, v);
    }
    static int color[MAXN], stk[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n && !bad; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && !bad) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = nbr[u][i];
                if (color[v] == -1) { color[v] = 1 - color[u]; stk[sp++] = v; }
                else if (color[v] == color[u]) { bad = 1; break; }
            }
        }
    }
    if (bad) { printf("0 0\n"); return 0; }
    scnt[0] = 0;
    scnt[1] = 0;
    for (int v = 0; v < n; v++) {
        side[v] = color[v];
        slist[side[v]][scnt[side[v]]++] = v;
    }

    logging = 0;
    fill();
    int c = cost_eval();
    if (c > 0) c = sa_run(20000, 2.0, 0.1);
    if (c > 0) { printf("0 0\n"); return 0; }
    snapshot();

    while (!timeup()) {
        if (ssN + 2 > MAXN) break;
        restore_state();
        int kicks = 1 + rndint(4);
        for (int k = 0; k < kicks; k++) do_switch();
        insert_pair();
        if (sa_run(3000, 2.0, 0.1) == 0) snapshot();
    }

    printf("%d %d\n", ssN, ssM);
    for (int i = 0; i < ssM; i++) printf("%d %d\n", ssA[i], ssB[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases (parent's constructions).
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
    """Generalized quadrangle W(q) for the largest prime power q + 1 <= d, with q <= 9 (keeps build time bounded)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared Python helpers.
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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
# Voltage lifts over small groups (parent's Python stage, kept as a seed source).
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
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane otherwise.
    base_n, base_e = best_n, list(best_e)
    base = _best_gq(d) if D >= 4 else None
    if base is None:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        if best_n >= moore:
            return best_n, list(best_e)
        n1, e1 = _grow(n0, e0, d, D, start + 0.05 * time_limit, rng)
        consider(n1, e1)

    if best_n >= moore:
        return best_n, list(best_e)

    # Short Python stages: voltage lifts, then twin trials.
    lift_end = start + 0.12 * time_limit
    if time.monotonic() < lift_end:
        _lift_stage(d, D, lambda: best_n, rng, lift_end, consider)

    trial_end = start + 0.15 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # NEW: C greedy-cover insertion + annealing, seeded with the best graph so far.
    remaining = time_limit - (time.monotonic() - start) - 3.0
    if remaining > 3.0 and best_n < moore:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.5, 2)],
                            stdin_graph=(best_n, best_e), timeout=remaining)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
