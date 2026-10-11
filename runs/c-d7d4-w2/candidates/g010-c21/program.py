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
#include <time.h>

#define MAXD 64
#define ANNEAL_ITERS 200

static int DEG, DIAM, N, CAP, WC;
static int *nb, *dg, *snb, *sdg, *bnb, *bdg;
static unsigned char *sd, *ssd, *bsd;
static int sN, bN;
static uint64_t *bufA, *bufB, *cov;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int m) { return m > 0 ? (int)(rnd64() % (uint64_t)m) : 0; }

static double now_s(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = nb + (size_t)a * DEG;
    for (int i = 0; i < dg[a]; i++) if (p[i] == b) return 1;
    return 0;
}
static void remove_entry(int x, int y) {
    int *p = nb + (size_t)x * DEG;
    for (int i = 0; i < dg[x]; i++) {
        if (p[i] == y) { p[i] = p[dg[x] - 1]; dg[x]--; return; }
    }
}
static void add_entry(int x, int y) { nb[(size_t)x * DEG + dg[x]] = y; dg[x]++; }
static void add_edge(int x, int y) { add_entry(x, y); add_entry(y, x); }
static void del_edge(int x, int y) { remove_entry(x, y); remove_entry(y, x); }

/* Bitset balls of radius r; returns whichever buffer holds the result. */
static uint64_t *balls(int r) {
    int Wn = (N + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * Wn);
    for (int v = 0; v < N; v++) cur[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * Wn;
            memcpy(o, cur + (size_t)v * Wn, sizeof(uint64_t) * Wn);
            for (int i = 0; i < dg[v]; i++) {
                int u = nb[(size_t)v * DEG + i];
                const uint64_t *s = cur + (size_t)u * Wn;
                for (int w = 0; w < Wn; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long long cost(void) {
    int Wn = (N + 63) >> 6;
    uint64_t *B = balls(DIAM);
    long long reach = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < Wn; w++) reach += pc64(B[(size_t)v * Wn + w]);
    return ((long long)N * N - reach) / 2;
}

/* Greedy cover of all vertices by radius DIAM-1 balls of side-s vertices. */
static int pick_cover(int s, int *ch) {
    int Wn = (N + 63) >> 6;
    uint64_t *B = balls(DIAM - 1);
    memset(cov, 0, sizeof(uint64_t) * Wn);
    int k = 0, covcnt = 0;
    while (k < DEG && covcnt < N) {
        int best = -1;
        long long bs = -1;
        for (int v = 0; v < N; v++) {
            if (sd[v] != s) continue;
            int used = 0;
            for (int j = 0; j < k; j++) if (ch[j] == v) { used = 1; break; }
            if (used) continue;
            const uint64_t *bv = B + (size_t)v * Wn;
            int g = 0;
            for (int w = 0; w < Wn; w++) g += pc64(bv[w] & ~cov[w]);
            if (g == 0) continue;
            long long sc = (long long)g * 64 + rndi(64);
            if (sc > bs) { bs = sc; best = v; }
        }
        if (best < 0) break;
        ch[k++] = best;
        const uint64_t *bv = B + (size_t)best * Wn;
        for (int w = 0; w < Wn; w++) cov[w] |= bv[w];
        covcnt = 0;
        for (int w = 0; w < Wn; w++) covcnt += pc64(cov[w]);
    }
    return k;
}

static void add_vertex_step(void) {
    if (N >= CAP) return;
    int s = rndi(2);
    int ch[MAXD];
    int k = pick_cover(s, ch);
    int v = N++;
    sd[v] = (unsigned char)(1 - s);
    dg[v] = 0;
    for (int j = 0; j < k; j++) {
        int c = ch[j];
        if (dg[c] >= DEG) {
            int t = nb[(size_t)c * DEG + rndi(dg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
}

static void remove_vertex(int x) {
    for (int i = 0; i < dg[x]; i++) {
        int u = nb[(size_t)x * DEG + i];
        remove_entry(u, x);
    }
    dg[x] = 0;
    int last = N - 1;
    if (x != last) {
        for (int i = 0; i < dg[last]; i++) {
            int u = nb[(size_t)last * DEG + i];
            int *p = nb + (size_t)u * DEG;
            for (int j = 0; j < dg[u]; j++) if (p[j] == last) { p[j] = x; break; }
        }
        memcpy(nb + (size_t)x * DEG, nb + (size_t)last * DEG, sizeof(int) * DEG);
        dg[x] = dg[last];
        sd[x] = sd[last];
    }
    N--;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Join deficient opposite-side vertices greedily in random order. */
static void fill(void) {
    int *L = malloc(sizeof(int) * (size_t)N);
    int *R = malloc(sizeof(int) * (size_t)N);
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (dg[v] >= DEG) continue;
        if (sd[v] == 0) L[nl++] = v; else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && dg[a] < DEG; j++) {
            int b = R[j];
            if (dg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
    free(L);
    free(R);
}

static int rand_side0(void) {
    for (int t = 0; t < 400; t++) {
        int v = rndi(N);
        if (sd[v] == 0 && dg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static int anneal(int iters, double deadline) {
    long long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now_s() > deadline) break;
        int a = rand_side0();
        if (a < 0) break;
        int c = rand_side0();
        if (c < 0) break;
        if (c == a) continue;
        int b = nb[(size_t)a * DEG + rndi(dg[a])];
        int e = nb[(size_t)c * DEG + rndi(dg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndi(100) < 5)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void save_snap(void) {
    sN = N;
    memcpy(snb, nb, sizeof(int) * (size_t)N * DEG);
    memcpy(sdg, dg, sizeof(int) * (size_t)N);
    memcpy(ssd, sd, (size_t)N);
}

static void restore_snap(void) {
    N = sN;
    memcpy(nb, snb, sizeof(int) * (size_t)N * DEG);
    memcpy(dg, sdg, sizeof(int) * (size_t)N);
    memcpy(sd, ssd, (size_t)N);
}

static void save_best(void) {
    bN = N;
    memcpy(bnb, nb, sizeof(int) * (size_t)N * DEG);
    memcpy(bdg, dg, sizeof(int) * (size_t)N);
    memcpy(bsd, sd, (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = now_s() + budget;
    if (DEG < 1 || DEG > MAXD || DIAM < 2) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    int *eu, *ev;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 <= 0) {
        n0 = 2; m0 = 1;
        eu = malloc(sizeof(int)); ev = malloc(sizeof(int));
        eu[0] = 0; ev[0] = 1;
    } else {
        if (m0 < 0) { printf("0 0\n"); return 0; }
        eu = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
        ev = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
        for (int i = 0; i < m0; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        }
    }

    CAP = n0 + 2048;
    WC = (CAP + 63) >> 6;
    nb = calloc((size_t)CAP * DEG, sizeof(int));
    dg = calloc((size_t)CAP, sizeof(int));
    sd = calloc((size_t)CAP, 1);
    snb = calloc((size_t)CAP * DEG, sizeof(int));
    sdg = calloc((size_t)CAP, sizeof(int));
    ssd = calloc((size_t)CAP, 1);
    bnb = calloc((size_t)CAP * DEG, sizeof(int));
    bdg = calloc((size_t)CAP, sizeof(int));
    bsd = calloc((size_t)CAP, 1);
    bufA = calloc((size_t)CAP * WC, sizeof(uint64_t));
    bufB = calloc((size_t)CAP * WC, sizeof(uint64_t));
    cov = calloc((size_t)WC, sizeof(uint64_t));

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { printf("0 0\n"); return 0; }
        if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    int *col = malloc(sizeof(int) * (size_t)N);
    int *q = malloc(sizeof(int) * (size_t)N);
    for (int i = 0; i < N; i++) col[i] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int i = 0; i < dg[x]; i++) {
                int y = nb[(size_t)x * DEG + i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[qt++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }
    for (int i = 0; i < N; i++) sd[i] = (unsigned char)col[i];

    save_best();
    while (now_s() < deadline) {
        save_snap();
        if (N < 2 || rndi(10) < 7) {
            add_vertex_step();
        } else {
            remove_vertex(rndi(N));
            add_vertex_step();
        }
        fill();
        int ok = anneal(ANNEAL_ITERS, deadline);
        if (ok && N >= bN - 1) {
            if (N > bN) save_best();
        } else {
            restore_snap();
        }
    }

    long long cnt = 0;
    for (int v = 0; v < bN; v++) cnt += bdg[v];
    cnt /= 2;
    printf("%d %lld\n", bN, cnt);
    for (int v = 0; v < bN; v++) {
        for (int i = 0; i < bdg[v]; i++) {
            int u = bnb[(size_t)v * DEG + i];
            if (u > v) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
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
    """Greedily add twins in random order while neighbours have spare degree."""
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Groups and bi-Cayley graphs.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k, r) with m*k = G giving a semidirect product Z_m x| Z_k."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _bicayley_adj(N, table, S):
    """Adjacency lists of the bi-Cayley graph: a_g = g, b_x = N + x, a_g ~ b_{g*s}."""
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        row = table[g]
        ag = adj[g]
        for s in S:
            b = N + row[s]
            ag.append(b)
            adj[b].append(g)
    return adj


def _cayley_cost(adj, D):
    """Vertices farther than D from a_e or from b_e (both sources)."""
    total = 0
    N2 = len(adj)
    N = N2 // 2
    for src in (0, N):
        dist = [-1] * N2
        dist[src] = 0
        frontier = [src]
        cnt = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _climb(N, table, d, D, rng, iters, deadline):
    """Hill-climb a d-element generating set S minimising the Cayley cost. Returns S or None."""
    S = rng.sample(range(N), d)
    cur = _cayley_cost(_bicayley_adj(N, table, S), D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in S:
            continue
        newS = list(S)
        newS[i] = cand
        c2 = _cayley_cost(_bicayley_adj(N, table, newS), D)
        if c2 <= cur or (c2 == cur + 1 and rng.random() < 0.05):
            S, cur = newS, c2
    return S if cur == 0 else None


def _bicayley_search(d, D, rng, deadline, consider, lo_n):
    """Search bi-Cayley graphs of increasing order N (n = 2N) that beat lo_n vertices."""
    lo = max(d, lo_n // 2 + 1)
    hi = lib.moore_bound(d, D) // 2
    N = lo
    while N <= hi and time.monotonic() < deadline:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:4]:
            if time.monotonic() >= deadline:
                break
            order, mul, _ = lib.semidirect_group(m, k, r)
            table = [[mul(x, y) for y in range(order)] for x in range(order)]
            S = _climb(N, table, d, D, rng, 200, deadline)
            if S is not None:
                edges = [(g, N + table[g][s]) for g in range(N) for s in S]
                consider(2 * N, edges)
                break
        N += 1


# ----------------------------------------------------------------------------
# Group-lift search.
# ----------------------------------------------------------------------------

def _lift_cost(kb, G, T, d, D, tgt, lab):
    """Sum over base vertices of unreached lifted vertices within distance D of (u, identity)."""
    n = 2 * kb * G
    nbr = [[] for _ in range(n)]
    for t in range(d):
        tt = tgt[t]
        lt = lab[t]
        for i in range(kb):
            j = kb + tt[i]
            g = lt[i]
            for x in range(G):
                a = i * G + x
                b = j * G + T[x][g]
                nbr[a].append(b)
                nbr[b].append(a)
    total = 0
    for u in range(2 * kb):
        s = u * G
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for w in nbr[v]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _lift_search(kb, G, T, d, D, deadline, rng):
    """Anneal dart labels and slot permutations until the lift has diameter <= D."""
    n = 2 * kb * G
    tgt = []
    lab = []
    for _ in range(d):
        p = list(range(kb))
        rng.shuffle(p)
        tgt.append(p)
        lab.append([rng.randrange(G) for _ in range(kb)])
    cur = _lift_cost(kb, G, T, d, D, tgt, lab)
    temp = 2.0
    while cur > 0 and time.monotonic() < deadline:
        if kb >= 2 and rng.random() < 0.3:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(kb), 2)
            tt = tgt[t]
            tt[i1], tt[i2] = tt[i2], tt[i1]
            c = _lift_cost(kb, G, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                tt[i1], tt[i2] = tt[i2], tt[i1]
        else:
            t = rng.randrange(d)
            i = rng.randrange(kb)
            old = lab[t][i]
            new = rng.randrange(G)
            if new == old:
                continue
            lab[t][i] = new
            c = _lift_cost(kb, G, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                lab[t][i] = old
    if cur != 0:
        return None
    edges = set()
    for t in range(d):
        for i in range(kb):
            j = kb + tgt[t][i]
            g = lab[t][i]
            for x in range(G):
                edges.add((i * G + x, j * G + T[x][g]))
    return n, sorted(edges)


def _lift_stage(d, D, rng, deadline, floor_n, limit_n):
    """Ladder over lift sizes above floor_n. Returns the largest valid lift found, or None."""
    cands = []
    for kb in range(1, 7):
        lo = floor_n // (2 * kb) + 1
        hi = limit_n // (2 * kb)
        for G in range(lo, hi + 1):
            n = 2 * kb * G
            if floor_n < n <= limit_n:
                cands.append((n, kb, G))
    cands.sort()
    best = None
    best_n = floor_n
    for n, kb, G in cands:
        if n <= best_n:
            continue
        if time.monotonic() >= deadline:
            break
        groups = _groups_of_order(G)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _lift_search(kb, G, T, d, D, slice_end, rng)
        if res is not None:
            cn, ce = res
            if cn > best_n and lib.is_valid(cn, ce, d, D):
                best_n = cn
                best = (cn, ce)
    return best


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    def at(frac):
        return t0 + frac * time_limit

    # Stage 1: structured base (generalized quadrangle or projective plane) plus growth.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        try:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.12), rng)
                consider(n1, e1)
        except Exception:
            pass

    if best_n >= moore:
        return best_n, list(best_e)

    # Stage 2: twin and growth pipelines.
    if D >= 2:
        try:
            trial_end = at(0.22)
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)
        except Exception:
            pass

    # Stage 3: bi-Cayley search over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.36):
        try:
            _bicayley_search(d, D, rng, at(0.36), consider, best_n)
        except Exception:
            pass

    # Stage 4: group-lift search for larger diameters.
    if D >= 4 and d >= 3 and time.monotonic() < at(0.5):
        try:
            limit_n = min(moore, 1200)
            res = _lift_stage(d, D, rng, at(0.5), best_n, limit_n)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    # Stage 5: C engine polishes the best graph by adding vertices with annealing repair.
    if best_n < moore and D >= 2 and 2 <= d <= 64 and time_limit >= 8:
        try:
            budget = at(0.85) - time.monotonic() - 0.5
            if budget > 1.0:
                hard_end = at(0.93)
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=max(1.0, hard_end - time.monotonic()))
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
