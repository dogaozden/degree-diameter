import itertools
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

/* Slot-based annealing engine.
 * Keeps a valid bipartite graph (max degree DEGMAX, diameter <= DIAM) and repeatedly
 * replaces a vertex or adds one, repairs the result with degree-preserving bipartite
 * double-edge switches driven by an exact bitset count of bad pairs, and keeps the
 * new state only if it is valid again. */

static int DEGMAX, DIAM, CAP, W;
static int *adj, *deg, *col, *alive, *freest, nfree, nslots, L;
static uint64_t *rA, *rB;
static uint64_t rs;
static int *ordL, *ordR, *stk;
static double T_END;
static int bestN = 0, bestM = 0, bestL = -1;
static int *bestE = NULL;

typedef struct {
    int *adj, *deg, *col, *alive, *freest;
    int nslots, nfree, L;
} Snap;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEGMAX;
    for (int i = 0; i < deg[a]; i++)
        if (p[i] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    int *p = adj + (size_t)a * DEGMAX;
    for (int i = 0; i < deg[a]; i++) {
        if (p[i] == b) {
            p[i] = p[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_arc(int a, int b) {
    adj[(size_t)a * DEGMAX + deg[a]] = b;
    deg[a]++;
}

static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

static int alloc_slot(void) {
    int v;
    if (nfree > 0) {
        v = freest[--nfree];
    } else {
        if (nslots >= CAP) return -1;
        v = nslots++;
    }
    alive[v] = 1;
    deg[v] = 0;
    L++;
    return v;
}

static void free_slot(int v) {
    alive[v] = 0;
    deg[v] = 0;
    freest[nfree++] = v;
    L--;
}

/* Number of pairs of live vertices at distance > DIAM (unreachable pairs included). */
static long long cost_eval(void) {
    uint64_t *cur = rA, *nxt = rB;
    int i, j, w, step;
    for (i = 0; i < nslots; i++) {
        if (!alive[i]) continue;
        uint64_t *row = cur + (size_t)i * W;
        for (w = 0; w < W; w++) row[w] = 0;
        row[i >> 6] |= 1ULL << (i & 63);
    }
    for (step = 0; step < DIAM; step++) {
        for (i = 0; i < nslots; i++) {
            if (!alive[i]) continue;
            uint64_t *dst = nxt + (size_t)i * W;
            const uint64_t *src = cur + (size_t)i * W;
            for (w = 0; w < W; w++) dst[w] = src[w];
            const int *p = adj + (size_t)i * DEGMAX;
            for (j = 0; j < deg[i]; j++) {
                const uint64_t *s2 = cur + (size_t)p[j] * W;
                for (w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (i = 0; i < nslots; i++) {
        if (!alive[i]) continue;
        const uint64_t *row = cur + (size_t)i * W;
        int c = 0;
        for (w = 0; w < W; w++) c += popc(row[w]);
        tot += L - c;
    }
    return tot / 2;
}

static int pick_live(void) {
    for (int t = 0; t < 2000; t++) {
        int x = rndint(nslots);
        if (alive[x] && deg[x] > 0) return x;
    }
    return -1;
}

static void shuffle_arr(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Join deficient opposite-colour vertices (non-adjacent), in random order. */
static void fill_deficient(void) {
    int nl = 0, nr = 0;
    for (int i = 0; i < nslots; i++) {
        if (!alive[i] || deg[i] >= DEGMAX) continue;
        if (col[i] == 0) ordL[nl++] = i;
        else ordR[nr++] = i;
    }
    shuffle_arr(ordL, nl);
    shuffle_arr(ordR, nr);
    for (int i = 0; i < nl; i++) {
        int a = ordL[i];
        for (int j = 0; j < nr && deg[a] < DEGMAX; j++) {
            int b = ordR[j];
            if (deg[b] < DEGMAX && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add a vertex of colour c attached to up to DEGMAX opposite-colour vertices.
 * Saturated neighbours give up a random edge (repaired later by annealing). */
static int add_vertex(int c) {
    int v = alloc_slot();
    if (v < 0) return -1;
    col[v] = c;
    for (int t = 0; t < DEGMAX; t++) {
        int w = -1;
        for (int tries = 0; tries < 60; tries++) {
            int x = rndint(nslots);
            if (alive[x] && x != v && col[x] != c && deg[x] < DEGMAX && !has_edge(x, v)) {
                w = x;
                break;
            }
        }
        if (w < 0) {
            for (int tries = 0; tries < 300; tries++) {
                int x = rndint(nslots);
                if (alive[x] && x != v && col[x] != c && deg[x] > 0 && !has_edge(x, v)) {
                    w = x;
                    break;
                }
            }
            if (w < 0) break;
            if (deg[w] >= DEGMAX) {
                int t2 = adj[(size_t)w * DEGMAX + rndint(deg[w])];
                del_edge(w, t2);
            }
        }
        add_edge(v, w);
    }
    return v;
}

static void remove_vertex(int r) {
    while (deg[r] > 0) del_edge(r, adj[(size_t)r * DEGMAX + deg[r] - 1]);
    free_slot(r);
}

/* Degree-preserving bipartite switches a-b, c-e  ->  a-e, c-b  (a, c same colour).
 * Keeps the cheapest states; returns 1 when the state has no bad pairs. */
static int anneal(int iters, double T0, double T1) {
    long long cur = cost_eval();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now_s() > T_END) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a = pick_live();
        if (a < 0) break;
        int b = adj[(size_t)a * DEGMAX + rndint(deg[a])];
        int c = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_live();
            if (x >= 0 && x != a && col[x] == col[a]) {
                c = x;
                break;
            }
        }
        if (c < 0) continue;
        int e = adj[(size_t)c * DEGMAX + rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost_eval();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
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

static void snap_alloc(Snap *s) {
    s->adj = malloc(sizeof(int) * (size_t)CAP * DEGMAX);
    s->deg = malloc(sizeof(int) * CAP);
    s->col = malloc(sizeof(int) * CAP);
    s->alive = malloc(sizeof(int) * CAP);
    s->freest = malloc(sizeof(int) * CAP);
}

static void snap_save(Snap *s) {
    memcpy(s->adj, adj, sizeof(int) * (size_t)CAP * DEGMAX);
    memcpy(s->deg, deg, sizeof(int) * CAP);
    memcpy(s->col, col, sizeof(int) * CAP);
    memcpy(s->alive, alive, sizeof(int) * CAP);
    memcpy(s->freest, freest, sizeof(int) * (size_t)nfree);
    s->nslots = nslots;
    s->nfree = nfree;
    s->L = L;
}

static void snap_restore(const Snap *s) {
    memcpy(adj, s->adj, sizeof(int) * (size_t)CAP * DEGMAX);
    memcpy(deg, s->deg, sizeof(int) * CAP);
    memcpy(col, s->col, sizeof(int) * CAP);
    memcpy(alive, s->alive, sizeof(int) * CAP);
    memcpy(freest, s->freest, sizeof(int) * (size_t)s->nfree);
    nslots = s->nslots;
    nfree = s->nfree;
    L = s->L;
}

/* Store the current live graph, compacted to 0..L-1, as the best result. */
static void store_best(void) {
    int *mp = malloc(sizeof(int) * (size_t)nslots);
    int k = 0;
    for (int i = 0; i < nslots; i++) mp[i] = alive[i] ? k++ : -1;
    long long cnt = 0;
    for (int i = 0; i < nslots; i++)
        if (alive[i]) cnt += deg[i];
    int mm = (int)(cnt / 2);
    int *E = malloc(sizeof(int) * 2 * (size_t)(mm > 0 ? mm : 1));
    int q = 0;
    for (int i = 0; i < nslots; i++) {
        if (!alive[i]) continue;
        for (int j = 0; j < deg[i]; j++) {
            int b = adj[(size_t)i * DEGMAX + j];
            if (i < b) {
                E[2 * q] = mp[i];
                E[2 * q + 1] = mp[b];
                q++;
            }
        }
    }
    free(mp);
    free(bestE);
    bestE = E;
    bestN = k;
    bestM = q;
    bestL = L;
}

static void echo_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    T_END = now_s() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int mr = 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        mr++;
    }
    m = mr;
    if (DEGMAX < 1 || DIAM < 1) {
        echo_input(n, m, eu, ev);
        return 0;
    }

    CAP = n + n / 3 + 300;
    W = (CAP + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)CAP * DEGMAX);
    deg = calloc(CAP, sizeof(int));
    col = malloc(sizeof(int) * CAP);
    alive = calloc(CAP, sizeof(int));
    freest = malloc(sizeof(int) * CAP);
    rA = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    rB = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    ordL = malloc(sizeof(int) * CAP);
    ordR = malloc(sizeof(int) * CAP);
    stk = malloc(sizeof(int) * CAP);
    for (int i = 0; i < CAP; i++) col[i] = -1;
    for (int i = 0; i < n; i++) alive[i] = 1;
    nslots = n;
    L = n;
    nfree = 0;

    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) ok = 0;
        else if (deg[u] >= DEGMAX || deg[v] >= DEGMAX || has_edge(u, v)) ok = 0;
        else add_edge(u, v);
    }
    if (ok) {
        int bad = 0;
        for (int s = 0; s < n && !bad; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0 && !bad) {
                int u = stk[--sp];
                for (int j = 0; j < deg[u]; j++) {
                    int v = adj[(size_t)u * DEGMAX + j];
                    if (col[v] < 0) {
                        col[v] = 1 - col[u];
                        stk[sp++] = v;
                    } else if (col[v] == col[u]) {
                        bad = 1;
                        break;
                    }
                }
            }
        }
        if (bad) ok = 0;
    }
    if (!ok) {
        echo_input(n, m, eu, ev);
        return 0;
    }
    if (cost_eval() > 0) anneal(20000, 1.0, 0.05);
    if (cost_eval() > 0) {
        echo_input(n, m, eu, ev);
        return 0;
    }

    store_best();
    Snap sv;
    snap_alloc(&sv);
    while (now_s() < T_END) {
        snap_save(&sv);
        int good = 1;
        if (L < 3 || rnd01() < 0.5) {
            if (add_vertex(rndint(2)) < 0) good = 0;
        } else {
            int x = -1;
            for (int t = 0; t < 200 && x < 0; t++) {
                int y = rndint(nslots);
                if (alive[y]) x = y;
            }
            if (x < 0) {
                good = 0;
            } else {
                int c = col[x];
                remove_vertex(x);
                if (add_vertex(c) < 0) good = 0;
            }
        }
        if (good) {
            fill_deficient();
            good = anneal(3000, 1.0, 0.05);
        }
        if (good) {
            if (L > bestL) store_best();
        } else {
            snap_restore(&sv);
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    return 0;
}
'''


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
# Shared graph helpers.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Adding cross-side edges keeps the graph bipartite and degrees <= d, and can only
    shorten distances, so a valid graph stays valid.
    """
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
# Twin duplication.
# ----------------------------------------------------------------------------

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
# Python kill-repair-regrow search (early stage; the C engine does the bulk).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _local_kill(n, adj, k, rng):
    """Pick k vertices forming a connected cluster (BFS-like from a random seed vertex)."""
    v = rng.randrange(n)
    kill = {v}
    frontier = [v]
    while len(kill) < k and frontier:
        x = frontier.pop(rng.randrange(len(frontier)))
        nb = list(adj[x])
        rng.shuffle(nb)
        for u in nb:
            if len(kill) >= k:
                break
            if u not in kill:
                kill.add(u)
                frontier.append(u)
    while len(kill) < k:
        kill.add(rng.randrange(n))
    return kill


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        if rng.random() < 0.6:
            full_adj = _to_sets(cur_n, cur_e)
            kill = _local_kill(cur_n, full_adj, k, rng)
        else:
            kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


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
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines (short).
    if D >= 2:
        trial_end = start + 0.22 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Python kill-repair-regrow (short warm-up).
    if D >= 2 and time.monotonic() < start + 0.35 * time_limit:
        _lns(best_n, best_e, d, D, start + 0.35 * time_limit, rng, consider)

    # C annealing engine: replace/grow moves with exact bitset cost, from the best graph.
    if D >= 2 and d >= 2:
        c_end = start + 0.80 * time_limit
        budget = c_end - time.monotonic()
        if budget > 1.0:
            try:
                txt = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                n, e = lib.parse_graph_text(txt)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
