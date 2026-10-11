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

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define STALL_LIMIT 2000

static int N, W, Dd, DIAM;
static int COL[MAXN], DEG[MAXN];
static int NB[MAXN][MAXD];
static unsigned char M[MAXN][MAXN];
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];

/* best graph found so far (edge list plus colouring) */
static int BN, BM, BCOL[MAXN];
static int BU[MAXE], BV[MAXE];
static int BEST_VALID = 0;

static uint64_t RS = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    RS ^= RS << 13; RS ^= RS >> 7; RS ^= RS << 17;
    return RS;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_n(int n) { N = n; W = (N + 63) / 64; }

static void rem_from(int a, int b) {
    for (int i = 0; i < DEG[a]; i++) {
        if (NB[a][i] == b) { NB[a][i] = NB[a][--DEG[a]]; return; }
    }
}
static void add_edge(int a, int b) {
    M[a][b] = M[b][a] = 1;
    NB[a][DEG[a]++] = b;
    NB[b][DEG[b]++] = a;
}
static void del_edge(int a, int b) {
    M[a][b] = M[b][a] = 0;
    rem_from(a, b);
    rem_from(b, a);
}
static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < DEG[v]; i++) M[v][NB[v][i]] = 0;
        DEG[v] = 0;
    }
}

/* Bitset balls of radius r for all vertices; returns BA or BB. */
static uint64_t *balls_rad(int r) {
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int i = 0; i < DEG[v]; i++) {
                const uint64_t *s = cur + (size_t)NB[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long bad_pairs(void) {
    uint64_t *B = balls_rad(DIAM);
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *b = B + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(b[w]);
        bad += N - c;
    }
    return bad / 2;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add edges between non-adjacent deficient opposite-side vertices (never increases bad pairs). */
static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (DEG[v] < Dd) {
            if (COL[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && DEG[a] < Dd; j++) {
            int b = R[j];
            if (DEG[b] < Dd && !M[a][b]) add_edge(a, b);
        }
    }
}

/*
 * Cover-based vertex insertion with edge stealing.
 * The new vertex v (side s) gets up to Dd neighbours on side 1-s, chosen by greedy
 * set cover of all old vertices by the radius-(DIAM-1) balls of the candidates.
 * A saturated neighbour gives up one random edge to make room. SA repairs the rest.
 */
static int insert_vertex(void) {
    if (N + 1 >= MAXN) return 0;
    int s = rndi(2);
    uint64_t *B = balls_rad(DIAM - 1);
    static uint64_t U[MAXW];
    static int used[MAXN];
    for (int w = 0; w < W; w++) U[w] = 0;
    for (int v = 0; v < N; v++) U[v / 64] |= 1ULL << (v % 64);
    for (int v = 0; v < N; v++) used[v] = 0;

    int chosen[MAXD], nc = 0;
    for (int pick = 0; pick < Dd && nc < Dd; pick++) {
        int best = -1, bestscore = -1000000, ties = 0;
        for (int b = 0; b < N; b++) {
            if (COL[b] != 1 - s || used[b]) continue;
            const uint64_t *bb = B + (size_t)b * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(bb[w] & U[w]);
            if (g == 0) continue;
            int score = 2 * g - (DEG[b] >= Dd ? 1 : 0);
            if (score > bestscore) { bestscore = score; best = b; ties = 1; }
            else if (score == bestscore) { ties++; if (rndi(ties) == 0) best = b; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        const uint64_t *bb = B + (size_t)best * W;
        for (int w = 0; w < W; w++) U[w] &= ~bb[w];
    }
    if (nc == 0) return 0;

    int v = N;
    set_n(N + 1);
    COL[v] = s;
    DEG[v] = 0;
    for (int i = 0; i < nc; i++) {
        int b = chosen[i];
        if (DEG[b] >= Dd) {
            int x = NB[b][rndi(DEG[b])];
            del_edge(b, x);
        }
        add_edge(v, b);
    }
    return 1;
}

typedef struct { int type, a, b, c, d; } Move;

static int pick_side(int s) {
    for (int t = 0; t < 2000; t++) {
        int v = rndi(N);
        if (COL[v] == s && DEG[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving double edge swap: (a,b),(c,d) -> (a,d),(c,b), a,c on side 0. */
static int make_swap(Move *mv) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = NB[a][rndi(DEG[a])];
    int d = NB[c][rndi(DEG[c])];
    if (b == d || M[a][d] || M[c][b]) return 0;
    mv->type = 1; mv->a = a; mv->b = b; mv->c = c; mv->d = d;
    return 1;
}

/* Move one edge end from b to a vertex c with spare degree on the same side as b. */
static int make_rewire(Move *mv) {
    int s = rndi(2);
    int a = pick_side(s);
    if (a < 0) return 0;
    int b = NB[a][rndi(DEG[a])];
    for (int t = 0; t < 60; t++) {
        int c = rndi(N);
        if (COL[c] != 1 - s || DEG[c] >= Dd || c == b || M[a][c]) continue;
        mv->type = 2; mv->a = a; mv->b = b; mv->c = c; mv->d = 0;
        return 1;
    }
    return 0;
}

static void apply_move(const Move *m) {
    if (m->type == 1) {
        del_edge(m->a, m->b);
        del_edge(m->c, m->d);
        add_edge(m->a, m->d);
        add_edge(m->c, m->b);
    } else {
        del_edge(m->a, m->b);
        add_edge(m->a, m->c);
    }
}

static void undo_move(const Move *m) {
    if (m->type == 1) {
        del_edge(m->a, m->d);
        del_edge(m->c, m->b);
        add_edge(m->a, m->b);
        add_edge(m->c, m->d);
    } else {
        del_edge(m->a, m->c);
        add_edge(m->a, m->b);
    }
}

static void save_best(void) {
    BN = N;
    BM = 0;
    for (int v = 0; v < N; v++) BCOL[v] = COL[v];
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < DEG[v]; i++) {
            int u = NB[v][i];
            if (u > v && BM < MAXE) { BU[BM] = v; BV[BM] = u; BM++; }
        }
    }
}

static void load_best(void) {
    clear_graph();
    set_n(BN);
    for (int v = 0; v < N; v++) COL[v] = BCOL[v];
    for (int i = 0; i < BM; i++) add_edge(BU[i], BV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    RS ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd64();
    if (RS == 0) RS = 1;
    double t_end = now() + budget;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 1 || n0 >= MAXN - 2 || Dd < 1 || Dd >= MAXD - 1 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    set_n(n0);
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (M[u][v] || DEG[u] >= Dd || DEG[v] >= Dd) continue;
        add_edge(u, v);
    }

    /* two-colour the start graph by BFS */
    static int Q[MAXN];
    for (int v = 0; v < N; v++) COL[v] = -1;
    for (int s = 0; s < N; s++) {
        if (COL[s] != -1) continue;
        COL[s] = 0;
        int qh = 0, qt = 0;
        Q[qt++] = s;
        while (qh < qt) {
            int u = Q[qh++];
            for (int i = 0; i < DEG[u]; i++) {
                int x = NB[u][i];
                if (COL[x] == -1) { COL[x] = 1 - COL[u]; Q[qt++] = x; }
            }
        }
    }
    for (int v = 0; v < N; v++)
        for (int i = 0; i < DEG[v]; i++)
            if (COL[NB[v][i]] == COL[v]) { printf("0 0\n"); return 0; }

    long long cur_bad = bad_pairs();
    save_best();
    BEST_VALID = (cur_bad == 0);

    long long stall = 0;
    while (now() < t_end) {
        if (cur_bad == 0 || (BEST_VALID && stall > STALL_LIMIT)) {
            if (cur_bad == 0) { save_best(); BEST_VALID = 1; }
            else load_best();
            if (!insert_vertex()) break;
            saturate();
            cur_bad = bad_pairs();
            stall = 0;
            continue;
        }
        Move mv;
        int got = (rndu() < 0.7) ? make_swap(&mv) : make_rewire(&mv);
        stall++;
        if (!got) continue;
        apply_move(&mv);
        long long nb = bad_pairs();
        long long delta = nb - cur_bad;
        double T = 0.2 + 0.6 * rndu();
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur_bad = nb;
        } else {
            undo_move(&mv);
        }
    }

    printf("%d %d\n", BN, BM);
    for (int i = 0; i < BM; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (points and totally isotropic lines).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (Python version, used before the C annealer).
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
    """Greedy set cover of `full` by at most d candidate vertices. Returns the list or None."""
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
            for attempt in range(60):
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


# ----------------------------------------------------------------------------
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
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
# Haar and cyclic-lift families.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# C annealer: grows a valid graph by cover-based vertex insertion + SA repair.
# ----------------------------------------------------------------------------

def _c_refine(d, D, n, edges, budget, seed):
    """Run the C annealer from (n, edges) for about `budget` seconds. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 10.0)
    try:
        return lib.parse_graph_text(out)
    except ValueError:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.85 * time_limit - 1.0   # all work must end before this
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    cap = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    ext_deadline = start + 0.2 * time_limit

    # D >= 3: projective planes for the few largest prime powers q with q + 1 <= d.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown likewise.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    # Calibration cases already at the Moore bound: return immediately.
    if best_n >= cap:
        return best

    # Short non-cyclic / cyclic lift search for the Python side.
    py_deadline = start + (0.2 if D >= 4 else 0.3) * time_limit
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < py_deadline and best_n < cap:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, py_deadline)
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
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, py_deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, py_deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    # Main new stage: C annealer starting from the best graph found so far.
    if D >= 2 and d >= 2 and best_n < cap:
        budget = hard - time.monotonic() - 2.5
        if budget >= 1.0:
            try:
                res = _c_refine(d, D, best[0], best[1], budget, seed)
                if res is not None:
                    consider(res[0], res[1])
            except RuntimeError:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
