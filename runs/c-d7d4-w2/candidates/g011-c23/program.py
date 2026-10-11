import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Native annealing vertex insertion (C engine).
#
# The engine keeps a valid bipartite graph and repeatedly (1) attaches a new
# vertex to a greedy cover of the opposite side, (2) fills spare degree between
# deficient opposite-side vertices, and (3) anneals degree-preserving double-edge
# switches to drive the bad-pair count back to zero. Bad pairs are counted with
# bitset balls of radius D. A successful repair is kept and followed by a short
# zero-cost plateau walk; a failed repair restores the last valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int Dd, DIST, N, NCAP, WCAP;
static int *adjv, *degv, *colr;
static u64 *bufA, *bufB, *covb;
static int *snapAdj, *snapDeg, *snapCol, snapN;
static u64 rs = 88172645463325252ULL;
static double tlimit = 0.0;

static u64 rnext(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rnd(int k) {
    return (int)(rnext() % (u64)k);
}

static double rndu(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int timeup(void) {
    return elapsed() >= tlimit;
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    int base = a * Dd, dg = degv[a], k;
    for (k = 0; k < dg; k++)
        if (adjv[base + k] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    int base = a * Dd, dg = degv[a], k;
    for (k = 0; k < dg; k++) {
        if (adjv[base + k] == b) {
            adjv[base + k] = adjv[base + dg - 1];
            degv[a] = dg - 1;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

static void add_edge(int a, int b) {
    adjv[a * Dd + degv[a]] = b;
    degv[a]++;
    adjv[b * Dd + degv[b]] = a;
    degv[b]++;
}

/* Bitset balls of radius r. Row v has stride w = ceil(N/64). Returns bufA or bufB. */
static u64 *compute_ball(int r) {
    int n = N, w = (n + 63) >> 6, s, v, k, j;
    u64 *cur = bufA, *nxt = bufB, *t;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)w);
    for (v = 0; v < n; v++)
        cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (s = 0; s < r; s++) {
        for (v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * w;
            u64 *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(u64) * (size_t)w);
            for (k = 0; k < degv[v]; k++) {
                int u = adjv[v * Dd + k];
                u64 *ur = cur + (size_t)u * w;
                for (j = 0; j < w; j++) dst[j] |= ur[j];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered vertex pairs at distance more than DIST. */
static long long cost_full(void) {
    u64 *b = compute_ball(DIST);
    int n = N, w = (n + 63) >> 6, v, j;
    long long bad = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (j = 0; j < w; j++) c += pc64(b[(size_t)v * w + j]);
        bad += n - c;
    }
    return bad / 2;
}

static int pick_side(int side) {
    int t;
    for (t = 0; t < 1000; t++) {
        int v = rnd(N);
        if (colr[v] == side) return v;
    }
    return -1;
}

/* Propose a switch a-b, c-e -> a-e, c-b with a, c on side 0. Degrees are preserved. */
static int propose_switch(int *pa, int *pb, int *pc, int *pe) {
    int a = pick_side(0), c, b, e;
    if (a < 0 || degv[a] == 0) return 0;
    c = pick_side(0);
    if (c < 0 || c == a || degv[c] == 0) return 0;
    b = adjv[a * Dd + rnd(degv[a])];
    e = adjv[c * Dd + rnd(degv[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    *pa = a;
    *pb = b;
    *pc = c;
    *pe = e;
    return 1;
}

static void apply_switch(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_switch(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Metropolis annealing on switches. Returns 1 when the bad-pair count reaches 0. */
static int anneal(int maxit, int stale_lim, double T) {
    long long cur = cost_full(), best = cur;
    int it, stale = 0;
    for (it = 0; it < maxit && cur > 0; it++) {
        int a, b, c, e;
        long long nc, delta;
        if ((it & 15) == 0 && timeup()) break;
        if (!propose_switch(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        nc = cost_full();
        delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_switch(a, b, c, e);
        }
        if (cur < best) {
            best = cur;
            stale = 0;
        } else if (++stale > stale_lim) {
            break;
        }
    }
    return cur == 0;
}

/* Zero-cost plateau walk: keep only switches that leave the graph valid. */
static void walk(int iters) {
    int i;
    for (i = 0; i < iters; i++) {
        int a, b, c, e;
        if (!propose_switch(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        if (cost_full() != 0) undo_switch(a, b, c, e);
    }
}

/* Add cross-side edges between deficient vertices in random order (never hurts distances). */
static void fill(void) {
    int n = N, i, j, k, nl = 0, nr = 0, cnt = 0;
    int *L = malloc(sizeof(int) * (size_t)(n + 1));
    int *R = malloc(sizeof(int) * (size_t)(n + 1));
    int *P = malloc(sizeof(int) * 2 * (size_t)(n * n / 4 + 2));
    if (!L || !R || !P) {
        free(L);
        free(R);
        free(P);
        return;
    }
    for (i = 0; i < n; i++) {
        if (degv[i] >= Dd) continue;
        if (colr[i] == 0) L[nl++] = i;
        else R[nr++] = i;
    }
    for (i = 0; i < nl; i++)
        for (j = 0; j < nr; j++)
            if (!has_edge(L[i], R[j])) {
                P[2 * cnt] = L[i];
                P[2 * cnt + 1] = R[j];
                cnt++;
            }
    for (i = cnt - 1; i > 0; i--) {
        int r = rnd(i + 1), ta, tb;
        ta = P[2 * i];
        tb = P[2 * i + 1];
        P[2 * i] = P[2 * r];
        P[2 * i + 1] = P[2 * r + 1];
        P[2 * r] = ta;
        P[2 * r + 1] = tb;
    }
    for (k = 0; k < cnt; k++) {
        int a = P[2 * k], b = P[2 * k + 1];
        if (degv[a] < Dd && degv[b] < Dd && !has_edge(a, b)) add_edge(a, b);
    }
    free(L);
    free(R);
    free(P);
}

/* Attach a new vertex (colour 1 - side) to a greedy cover of side-colour vertices. */
static int add_vertex(int side) {
    int n = N, w = (n + 63) >> 6, k, j, v;
    u64 *ball;
    int chosen[64], nch = 0;
    if (n + 1 >= NCAP || DIST < 2) return -1;
    ball = compute_ball(DIST - 1);
    memset(covb, 0, sizeof(u64) * (size_t)w);
    for (k = 0; k < Dd && k < 64; k++) {
        int best = -1, s, t;
        double bs = -1.0;
        for (s = 0; s < n; s++) {
            int dup = 0, g = 0;
            double sc;
            if (colr[s] != side) continue;
            for (t = 0; t < nch; t++)
                if (chosen[t] == s) {
                    dup = 1;
                    break;
                }
            if (dup) continue;
            for (j = 0; j < w; j++)
                g += pc64(ball[(size_t)s * w + j] & ~covb[j]);
            sc = (double)g + 0.5 * rndu();
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (j = 0; j < w; j++) covb[j] |= ball[(size_t)best * w + j];
    }
    if (nch == 0) return -1;
    v = N++;
    colr[v] = 1 - side;
    degv[v] = 0;
    for (k = 0; k < nch; k++) {
        int s = chosen[k];
        if (degv[s] >= Dd) {
            int t = adjv[s * Dd + rnd(degv[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return v;
}

static void save_state(void) {
    snapN = N;
    memcpy(snapAdj, adjv, sizeof(int) * (size_t)N * Dd);
    memcpy(snapDeg, degv, sizeof(int) * (size_t)N);
    memcpy(snapCol, colr, sizeof(int) * (size_t)N);
}

static void restore_state(void) {
    N = snapN;
    memcpy(adjv, snapAdj, sizeof(int) * (size_t)N * Dd);
    memcpy(degv, snapDeg, sizeof(int) * (size_t)N);
    memcpy(colr, snapCol, sizeof(int) * (size_t)N);
}

static int load_graph(int n, int m, const int *eu, const int *ev) {
    int i, s, head, tail;
    int *q;
    N = n;
    memset(degv, 0, sizeof(int) * (size_t)NCAP);
    for (i = 0; i < n; i++) colr[i] = -1;
    for (i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (degv[u] >= Dd || degv[v] >= Dd) return 0;
        if (has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    q = malloc(sizeof(int) * (size_t)(n + 1));
    if (!q) return 0;
    for (s = 0; s < n; s++) {
        if (colr[s] != -1) continue;
        colr[s] = 0;
        head = tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++], k;
            for (k = 0; k < degv[x]; k++) {
                int y = adjv[x * Dd + k];
                if (colr[y] == -1) {
                    colr[y] = 1 - colr[x];
                    q[tail++] = y;
                } else if (colr[y] == colr[x]) {
                    free(q);
                    return 0;
                }
            }
        }
    }
    free(q);
    return 1;
}

/* Complete bipartite K_{d,d}: valid for D >= 2. */
static void set_fallback(int d) {
    int i, j;
    N = 2 * d;
    memset(degv, 0, sizeof(int) * (size_t)NCAP);
    for (i = 0; i < N; i++) colr[i] = (i < d) ? 0 : 1;
    for (i = 0; i < d; i++)
        for (j = 0; j < d; j++)
            add_edge(i, d + j);
}

static void print_state(void) {
    long long M = 0;
    int v, k;
    for (v = 0; v < N; v++) M += degv[v];
    M /= 2;
    printf("%d %lld\n", N, M);
    for (v = 0; v < N; v++)
        for (k = 0; k < degv[v]; k++)
            if (v < adjv[v * Dd + k]) printf("%d %d\n", v, adjv[v * Dd + k]);
}

int main(int argc, char **argv) {
    int d, D, n0 = 0, m0 = 0, i, ok;
    unsigned long long seed;
    int *eu, *ev;
    int base;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    tlimit = atof(argv[4]);
    if (d < 1 || d > 64 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 20; i++) rnext();
    Dd = d;
    DIST = D;

    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || m0 < 0) {
        n0 = 0;
        m0 = 0;
    }
    eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) return 1;
    for (i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            m0 = i;
            break;
        }
    }

    base = n0 > 2 * d ? n0 : 2 * d;
    NCAP = 2 * base + 200;
    WCAP = (NCAP + 63) >> 6;
    adjv = malloc(sizeof(int) * (size_t)NCAP * Dd);
    degv = calloc((size_t)NCAP, sizeof(int));
    colr = calloc((size_t)NCAP, sizeof(int));
    bufA = malloc(sizeof(u64) * (size_t)NCAP * WCAP);
    bufB = malloc(sizeof(u64) * (size_t)NCAP * WCAP);
    covb = malloc(sizeof(u64) * (size_t)WCAP);
    snapAdj = malloc(sizeof(int) * (size_t)NCAP * Dd);
    snapDeg = malloc(sizeof(int) * (size_t)NCAP);
    snapCol = malloc(sizeof(int) * (size_t)NCAP);
    if (!adjv || !degv || !colr || !bufA || !bufB || !covb ||
        !snapAdj || !snapDeg || !snapCol)
        return 1;

    ok = (n0 > 0 && load_graph(n0, m0, eu, ev));
    if (!ok) set_fallback(d);
    if (cost_full() != 0) {
        anneal(20000, 4000, 0.8);
        if (cost_full() != 0) set_fallback(d);
    }

    save_state();
    while (!timeup()) {
        int side = rnd(2);
        double T;
        if (N + 1 >= NCAP) break;
        if (add_vertex(side) < 0) continue;
        T = 0.4 + 0.8 * rndu();
        fill();
        if (anneal(3000, 900, T)) {
            walk(60);
            save_state();
        } else {
            restore_state();
        }
    }
    restore_state();
    print_state();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python growth helpers (cover extension, saturation, twin duplication).
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Greedily add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
    """One randomized pipeline mixing twin duplication with cover growth and saturation."""
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

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Calibration-type cases already at the Moore bound: return at once.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.18 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Native annealing vertex insertion from the best valid graph found so far.
    if D >= 2 and d >= 3 and best_n < lib.moore_bound(d, D):
        c_deadline = start + 0.90 * time_limit
        budget = c_deadline - time.monotonic() - 4.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError, OSError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
