import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: valid-graph local search in C. Bitset-based bad-pair cost,
# degree-preserving bipartite switch annealing, vertex addition by greedy
# cover, and kill-repair-regrow. Only ever outputs a graph it has checked.
# Python re-checks everything with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define ITER 800

static int N, S, DM;
static int *ADJ, *DEG, *COL;
static int *SADJ, *SDEG, *SCOL, SN;
static int *BADJ, *BDEG, *BCOL, BN;
static int *S0;
static uint64_t *BUFA, *BUFB;
static uint64_t rs = 88172645463325252ULL;
static double DEADLINE = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static int timeup(void) { return (double)clock() / CLOCKS_PER_SEC > DEADLINE; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void del_half(int a, int b) {
    int *row = ADJ + (size_t)a * S;
    for (int i = 0; i < DEG[a]; i++) {
        if (row[i] == b) {
            row[i] = row[DEG[a] - 1];
            DEG[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static void add_edge(int a, int b) {
    ADJ[(size_t)a * S + DEG[a]] = b;
    DEG[a]++;
    ADJ[(size_t)b * S + DEG[b]] = a;
    DEG[b]++;
}

static int has_edge(int a, int b) {
    int x = a, y = b;
    if (DEG[x] > DEG[y]) { x = b; y = a; }
    const int *row = ADJ + (size_t)x * S;
    for (int i = 0; i < DEG[x]; i++) if (row[i] == y) return 1;
    return 0;
}

/* Reach sets within radius r, as bitsets. Returns a pointer to one of BUFA/BUFB. */
static uint64_t *reach_calc(int r) {
    int W = (N + 63) >> 6;
    uint64_t *cur = BUFA, *nxt = BUFB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < DEG[v]; i++) {
                const uint64_t *src = cur + (size_t)ADJ[(size_t)v * S + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DM (unreachable counts). */
static long cost(void) {
    int W = (N + 63) >> 6;
    uint64_t *b = reach_calc(DM);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(b[(size_t)v * W + w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Degree-preserving bipartite switches minimising bad pairs. True if cost reaches 0. */
static int anneal(int iters) {
    long cur = cost();
    int n0 = 0;
    for (int v = 0; v < N; v++) if (COL[v] == 0) S0[n0++] = v;
    if (n0 < 2) return cur == 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        int a = S0[rndint(n0)];
        if (DEG[a] == 0) continue;
        int b = ADJ[(size_t)a * S + rndint(DEG[a])];
        int c = S0[rndint(n0)];
        if (c == a || DEG[c] == 0) continue;
        int e = ADJ[(size_t)c * S + rndint(DEG[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd() % 10 == 0)) {
            cur = nw;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void shuffle_ints(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Join deficient opposite-colour vertices in random order. */
static void fill(void) {
    int *L = malloc(sizeof(int) * (N + 1));
    int *R = malloc(sizeof(int) * (N + 1));
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (DEG[v] < S) {
            if (COL[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_ints(L, nl);
    shuffle_ints(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (DEG[a] >= S) break;
            int b = R[j];
            if (DEG[b] < S && !has_edge(a, b)) add_edge(a, b);
        }
    }
    free(L);
    free(R);
}

/* Add a vertex on the side opposite to a greedy cover of the other side. */
static int add_vertex(void) {
    if (N >= MAXN - 2) return -1;
    int side = rndint(2);
    int W = (N + 63) >> 6;
    uint64_t *ball = reach_calc(DM - 1);
    uint64_t *cov = calloc((size_t)W + 1, sizeof(uint64_t));
    int *cand = malloc(sizeof(int) * (N + 1));
    char *used = calloc((size_t)N + 1, 1);
    int *chosen = malloc(sizeof(int) * (S + 1));
    int nc = 0, nch = 0;
    for (int v = 0; v < N; v++) if (COL[v] == side) cand[nc++] = v;
    for (int k = 0; k < S; k++) {
        int best = -1;
        long bs = -1;
        for (int i = 0; i < nc; i++) {
            int s = cand[i];
            if (used[s]) continue;
            long g = 0;
            for (int w = 0; w < W; w++) g += pc64(ball[(size_t)s * W + w] & ~cov[w]);
            long sc = g * 16 + (long)(rnd() % 16);
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= ball[(size_t)best * W + w];
    }
    int v = N;
    N++;
    COL[v] = 1 - side;
    DEG[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (DEG[s] >= S) {
            int t = ADJ[(size_t)s * S + rndint(DEG[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
    free(cov);
    free(cand);
    free(used);
    free(chosen);
    return v;
}

/* Delete vertex x, moving the last vertex into its slot. */
static void remove_vertex(int x) {
    while (DEG[x] > 0) remove_edge(x, ADJ[(size_t)x * S]);
    int last = N - 1;
    if (x != last) {
        for (int i = 0; i < DEG[last]; i++) {
            int u = ADJ[(size_t)last * S + i];
            int *row = ADJ + (size_t)u * S;
            for (int j = 0; j < DEG[u]; j++) {
                if (row[j] == last) {
                    row[j] = x;
                    break;
                }
            }
        }
        memcpy(ADJ + (size_t)x * S, ADJ + (size_t)last * S, sizeof(int) * S);
        DEG[x] = DEG[last];
        COL[x] = COL[last];
    }
    N--;
    DEG[N] = 0;
}

static void snap(void) {
    SN = N;
    memcpy(SADJ, ADJ, sizeof(int) * (size_t)N * S);
    memcpy(SDEG, DEG, sizeof(int) * (size_t)N);
    memcpy(SCOL, COL, sizeof(int) * (size_t)N);
}

static void restore(void) {
    N = SN;
    memcpy(ADJ, SADJ, sizeof(int) * (size_t)N * S);
    memcpy(DEG, SDEG, sizeof(int) * (size_t)N);
    memcpy(COL, SCOL, sizeof(int) * (size_t)N);
}

static void save_best(void) {
    BN = N;
    memcpy(BADJ, ADJ, sizeof(int) * (size_t)N * S);
    memcpy(BDEG, DEG, sizeof(int) * (size_t)N);
    memcpy(BCOL, COL, sizeof(int) * (size_t)N);
}

static void load_best(void) {
    N = BN;
    memcpy(ADJ, BADJ, sizeof(int) * (size_t)N * S);
    memcpy(DEG, BDEG, sizeof(int) * (size_t)N);
    memcpy(COL, BCOL, sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    S = d;
    if (S < 1 || DM < 2) {
        printf("0 0\n");
        return 0;
    }
    size_t cap = (size_t)MAXN * S;
    ADJ = malloc(sizeof(int) * cap);
    SADJ = malloc(sizeof(int) * cap);
    BADJ = malloc(sizeof(int) * cap);
    DEG = malloc(sizeof(int) * MAXN);
    COL = malloc(sizeof(int) * MAXN);
    SDEG = malloc(sizeof(int) * MAXN);
    SCOL = malloc(sizeof(int) * MAXN);
    BDEG = malloc(sizeof(int) * MAXN);
    BCOL = malloc(sizeof(int) * MAXN);
    S0 = malloc(sizeof(int) * MAXN);
    BUFA = malloc(sizeof(uint64_t) * MAXN * MAXW);
    BUFB = malloc(sizeof(uint64_t) * MAXN * MAXW);
    if (!ADJ || !SADJ || !BADJ || !DEG || !COL || !SDEG || !SCOL || !BDEG ||
        !BCOL || !S0 || !BUFA || !BUFB) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 1 || n >= MAXN - 64 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    memset(DEG, 0, sizeof(int) * MAXN);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (DEG[u] >= S || DEG[v] >= S) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < N; v++) COL[v] = -1;
    int *q = malloc(sizeof(int) * (N + 1));
    for (int s = 0; s < N; s++) {
        if (COL[s] >= 0) continue;
        COL[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int i = 0; i < DEG[x]; i++) {
                int y = ADJ[(size_t)x * S + i];
                if (COL[y] < 0) {
                    COL[y] = 1 - COL[x];
                    q[tail++] = y;
                }
            }
        }
    }
    free(q);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < DEG[v]; i++)
            if (COL[ADJ[(size_t)v * S + i]] == COL[v]) {
                printf("0 0\n");
                return 0;
            }

    DEADLINE = (double)clock() / CLOCKS_PER_SEC + budget;
    if (cost() != 0) {
        anneal(5000);
        if (cost() != 0) {
            printf("0 0\n");
            return 0;
        }
    }
    save_best();

    while (!timeup()) {
        if (rndint(10) < 7) {
            /* Grow: add a cover vertex, saturate, repair. */
            if (N >= MAXN - 2) break;
            snap();
            if (add_vertex() < 0) { restore(); break; }
            fill();
            if (anneal(ITER)) {
                if (N > BN) save_best();
            } else {
                restore();
            }
        } else {
            /* Kill some vertices, repair, then regrow a few times. */
            int k = 1 + rndint(3);
            if (N - k < 8) continue;
            snap();
            for (int i = 0; i < k; i++) remove_vertex(rndint(N));
            fill();
            if (!anneal(ITER)) {
                restore();
                continue;
            }
            for (int t = 0; t < 3 && !timeup(); t++) {
                if (N >= MAXN - 2) break;
                snap();
                if (add_vertex() < 0) { restore(); break; }
                fill();
                if (!anneal(ITER)) {
                    restore();
                    break;
                }
            }
            if (N > BN) save_best();
            else if (N < BN - 3) load_best();
        }
    }

    long em = 0;
    for (int v = 0; v < BN; v++)
        for (int i = 0; i < BDEG[v]; i++)
            if (BADJ[(size_t)v * S + i] > v) em++;
    printf("%d %ld\n", BN, em);
    for (int v = 0; v < BN; v++)
        for (int i = 0; i < BDEG[v]; i++) {
            int u = BADJ[(size_t)v * S + i];
            if (u > v) printf("%d %d\n", v, u);
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """Dense structured graph with degree at least d, to be thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within radius D-1."""
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
    """Join deficient opposite-side vertices in random order. Keeps validity."""
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
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
    """One randomized pipeline: twin duplication mixed with cover growth and saturation."""
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
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver.
#   1. Structured base (W(q) for D >= 4, PG(2,q) for D = 3), grown.
#   2. Short randomized twin/cover trials.
#   3. One thinning trial from a dense graph.
#   4. C local search (kill, repair, regrow, switch annealing) from the best graph.
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    def at(f):
        return start + f * T

    # Phase 1: structured base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            consider(*_grow(n0, e0, d, D, at(0.08), rng))

    # Phase 2: randomized trials.
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            consider(*_trial(base_n, base_e, d, D, rng, trial_end))

    # Phase 3: thinning a dense structured graph.
    if D >= 2 and time.monotonic() < at(0.25):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            r = _deletion_trial(d, D, rn, re, rng, at(0.25))
            if r is not None:
                consider(*r)

    # Phase 4: C local search from the best valid graph.
    c_budget = at(0.85) - time.monotonic()
    if D >= 2 and c_budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget - 0.3, 2)],
                            stdin_graph=(best_n, best_e), timeout=c_budget + 2.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
