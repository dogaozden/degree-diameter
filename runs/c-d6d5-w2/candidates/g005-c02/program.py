import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction family: bi-Cayley graphs over arbitrary finite groups.
#
# For a group G of order N and a connection set S = {s_1..s_d} (distinct),
# the graph has vertices A_g and B_h (g, h in G), with A_g ~ B_{g s} for s in S.
# Left multiplication is an automorphism, so the diameter is <= D iff BFS of
# depth D from A_e and from B_e reaches everything. Each BFS is O(N d).
#
# Groups are NOT restricted to metacyclic ones. The candidates include
# F_q x| H with non-prime q (non-cyclic translation subgroup), PSL(2,q) for
# q = 7, 8, 9, 11 (acting on the projective line), and direct products of
# A4, S4, A5, S5, PSL(2,7) with cyclic groups. Each group arrives as a full
# multiplication table. The C engine searches S by simulated annealing with
# restarts and warm restarts from the best state for each group. Groups are
# visited round-robin, and only groups larger than the best valid order found
# so far are searched.
#
# Fallbacks: K_{d,d} (diameter 2) and the projective-plane incidence graph
# PG(2, q) (diameter 3). Every output is checked with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CHUNK 20000
#define T_HOT 10.0
#define T_COLD 0.5

static uint64_t rs[2];
static struct timespec T0TS;
static double DEADLINE;
static int DEG, DIAM;

typedef struct {
    int N;
    const int *mul;   /* N*N table, mul[x*N+y] = x*y, identity index 0 */
    int *inv;
    int *mark;        /* size 2N */
    int *queue;       /* size 2N */
    int stamp;
    int *S;           /* current connection set, DEG entries */
    int *invS;        /* inverses of S */
    int *bestS;       /* best connection set seen */
    int bestC;        /* -1 = none yet */
} Grp;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0TS.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0TS.tv_nsec);
}

static int in_set(const int *S, int n, int x) {
    for (int k = 0; k < n; k++) if (S[k] == x) return 1;
    return 0;
}

/* Number of vertices within distance DIAM of src in the bi-Cayley graph. */
static int bfs_reach(Grp *g, int src) {
    int N = g->N;
    const int *S = g->S, *invS = g->invS;
    if (++g->stamp == 0x7fffffff) {
        memset(g->mark, 0, sizeof(int) * (size_t)(2 * N));
        g->stamp = 1;
    }
    int st = g->stamp;
    int head = 0, tail = 0;
    g->queue[tail++] = src;
    g->mark[src] = st;
    for (int depth = 0; depth < DIAM && head < tail; depth++) {
        int lend = tail;
        while (head < lend) {
            int v = g->queue[head++];
            if (v < N) {
                const int *row = g->mul + (size_t)v * N;
                for (int k = 0; k < DEG; k++) {
                    int w = N + row[S[k]];
                    if (g->mark[w] != st) { g->mark[w] = st; g->queue[tail++] = w; }
                }
            } else {
                const int *row = g->mul + (size_t)(v - N) * N;
                for (int k = 0; k < DEG; k++) {
                    int u = row[invS[k]];
                    if (g->mark[u] != st) { g->mark[u] = st; g->queue[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Cost = number of (source, vertex) pairs not covered, over the two block representatives. */
static int eval_cost(Grp *g) {
    int N = g->N;
    for (int k = 0; k < DEG; k++) g->invS[k] = g->inv[g->S[k]];
    int r0 = bfs_reach(g, 0);
    int r1 = bfs_reach(g, N);
    return (2 * N - r0) + (2 * N - r1);
}

static void random_set(Grp *g) {
    for (int k = 0; k < DEG; k++) {
        int x;
        do { x = rnd_int(g->N); } while (in_set(g->S, k, x));
        g->S[k] = x;
    }
}

/* One annealing chunk on group g. Returns the best cost reached in this chunk. */
static int sa_chunk(Grp *g, int iters) {
    int N = g->N;
    int warm = (g->bestC >= 0) && (rnd_unit() < 0.5);
    if (warm) {
        memcpy(g->S, g->bestS, sizeof(int) * (size_t)DEG);
        for (int p = 0; p < 2; p++) {
            int k = rnd_int(DEG), x;
            do { x = rnd_int(N); } while (in_set(g->S, DEG, x));
            g->S[k] = x;
        }
    } else {
        random_set(g);
    }
    int cur = eval_cost(g);
    int chunkbest = cur;
    if (g->bestC < 0 || cur < g->bestC) {
        g->bestC = cur;
        memcpy(g->bestS, g->S, sizeof(int) * (size_t)DEG);
    }
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = T_HOT * pow(T_COLD / T_HOT, frac);
        int k = rnd_int(DEG);
        int x = rnd_int(N);
        if (in_set(g->S, DEG, x)) continue;
        int old = g->S[k];
        g->S[k] = x;
        int c2 = eval_cost(g);
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur < chunkbest) chunkbest = cur;
            if (g->bestC < 0 || cur < g->bestC) {
                g->bestC = cur;
                memcpy(g->bestS, g->S, sizeof(int) * (size_t)DEG);
            }
        } else {
            g->S[k] = old;
        }
    }
    return chunkbest;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0TS, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int hdr_n, hdr_m;
    if (scanf("%d %d", &hdr_n, &hdr_m) != 2) {
        printf("0 0\n");
        return 0;
    }
    int cap = 1 << 16, len = 0;
    int *vec = malloc(sizeof(int) * (size_t)cap);
    int x;
    while (scanf("%d", &x) == 1) {
        if (len == cap) {
            cap *= 2;
            vec = realloc(vec, sizeof(int) * (size_t)cap);
        }
        vec[len++] = x;
    }

    if (DEG < 1 || DIAM < 1 || len == 0) {
        printf("0 0\n");
        return 0;
    }

    int total = vec[0];
    int pos = 1;
    int ngmax = 64;
    Grp *grps = calloc((size_t)ngmax, sizeof(Grp));
    int ng = 0;
    for (int gi = 0; gi < total && gi < ngmax && pos < len; gi++) {
        int N = vec[pos++];
        if (N < 2 || N < DEG || (long long)pos + (long long)N * N > (long long)len) break;
        Grp *g = &grps[ng];
        g->N = N;
        g->mul = vec + pos;
        pos += N * N;
        g->inv = malloc(sizeof(int) * (size_t)N);
        int ok = 1;
        for (int a = 0; a < N && ok; a++) {
            g->inv[a] = -1;
            for (int b = 0; b < N; b++)
                if (g->mul[a * N + b] == 0) { g->inv[a] = b; break; }
            if (g->inv[a] < 0) ok = 0;
        }
        if (!ok) { free(g->inv); continue; }
        g->mark = calloc((size_t)(2 * N), sizeof(int));
        g->queue = malloc(sizeof(int) * (size_t)(2 * N));
        g->stamp = 0;
        g->S = malloc(sizeof(int) * (size_t)DEG);
        g->invS = malloc(sizeof(int) * (size_t)DEG);
        g->bestS = malloc(sizeof(int) * (size_t)DEG);
        g->bestC = -1;
        ng++;
    }

    int bestN = 0, bestG = -1;
    while (elapsed() < DEADLINE) {
        int any = 0;
        for (int gi = 0; gi < ng && elapsed() < DEADLINE; gi++) {
            Grp *g = &grps[gi];
            if (g->N <= bestN) continue;
            any = 1;
            (void)sa_chunk(g, CHUNK);
            if (g->bestC == 0 && g->N > bestN) {
                bestN = g->N;
                bestG = gi;
            }
        }
        if (!any) break;
    }

    if (bestG < 0) {
        printf("0 0\n");
        return 0;
    }
    Grp *g = &grps[bestG];
    int N = g->N;
    printf("%d %d\n", 2 * N, N * DEG);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", v, N + g->mul[v * N + g->bestS[k]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group construction in Python. Each group is a permutation group; its
# multiplication table is built with numpy hashing.
# ----------------------------------------------------------------------------

def _closure(gens, limit):
    """Elements of the permutation group generated by gens, identity first. None if more than limit."""
    P = len(gens[0])
    ident = tuple(range(P))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(g[t] for t in x)  # apply x, then g
            if y not in index:
                if len(elems) == limit:
                    return None
                index[y] = len(elems)
                elems.append(y)
    return elems


def _mult_table(elems):
    """N x N table with table[a][b] = index of a*b, where (a*b)[t] = b[a[t]]. None on failure."""
    E = np.array(elems, dtype=np.int64)
    N, P = E.shape
    rng = np.random.default_rng(12345)
    w = rng.integers(1, 2 ** 62, size=P, dtype=np.int64).astype(np.uint64)
    H = (E.astype(np.uint64) * w).sum(axis=1, dtype=np.uint64)
    order = np.argsort(H)
    Hs = H[order]
    table = np.empty((N, N), dtype=np.int64)
    for a in range(N):
        Z = E[:, E[a]]  # Z[b, t] = b[a[t]], so row b is a*b
        hz = (Z.astype(np.uint64) * w).sum(axis=1, dtype=np.uint64)
        pos = np.minimum(np.searchsorted(Hs, hz), N - 1)
        idx = order[pos]
        if not np.array_equal(H[idx], hz):
            return None
        table[a] = idx
    return table


def _affine_gens(q, h):
    """Generators of F_q x| H, with H the subgroup of order h in F_q^*; acts on the q field elements."""
    F = lib.GF(q)
    p, k = F.p, F.k
    gens = []
    for i in range(k):
        t = p ** i
        gens.append(tuple(F.add(x, t) for x in range(q)))
    if h > 1:
        g = F.primitive_element()
        m = F.pow(g, (q - 1) // h)
        gens.append(tuple(F.mul(m, x) for x in range(q)))
    return gens


def _psl2_gens(q):
    """Generators of PSL(2,q) on the projective line (q points plus infinity, index q)."""
    F = lib.GF(q)
    inf = q
    t = tuple([F.add(x, 1) for x in range(q)] + [inf])
    s = [inf if x == 0 else F.neg(F.inv(x)) for x in range(q)] + [0]
    return [t, tuple(s)]


def _cycle_gens(k):
    return [tuple((i + 1) % k for i in range(k))]


def _product(g1, P1, g2, P2):
    """Generators of G1 x G2 acting on the disjoint union of P1 and P2 points."""
    gens = []
    for a in g1:
        gens.append(tuple(a) + tuple(range(P1, P1 + P2)))
    for b in g2:
        gens.append(tuple(range(P1)) + tuple(x + P1 for x in b))
    return gens


_BASES = [
    (12, lambda: [(1, 2, 0, 3), (1, 0, 3, 2)], 4),                 # A4
    (24, lambda: [(1, 0, 2, 3), (1, 2, 3, 0)], 4),                 # S4
    (60, lambda: [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)], 5),           # A5
    (120, lambda: [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 5),          # S5
    (168, lambda: _psl2_gens(7), 8),                               # PSL(2,7)
]


def _group_specs(lo, hi):
    """List of (order, builder) for candidate groups with lo <= order <= hi."""
    specs = []
    # Affine-type groups F_q x| H with q a prime power (non-prime q are non-metacyclic).
    for q in range(3, hi + 1):
        if not lib.is_prime_power(q):
            continue
        for h in range(1, q):
            if (q - 1) % h:
                continue
            order = q * h
            if lo <= order <= hi:
                specs.append((order, lambda q=q, h=h: _affine_gens(q, h)))
    # Projective linear groups PSL(2,q).
    for q in (7, 8, 9, 11):
        order = q * (q * q - 1) // 2
        if lo <= order <= hi:
            specs.append((order, lambda q=q: _psl2_gens(q)))
    # Direct products of small non-abelian groups with cyclic groups.
    for bo, bg, bp in _BASES:
        for k in range(2, hi // bo + 1):
            order = bo * k
            if lo <= order <= hi:
                specs.append((order, lambda bg=bg, bp=bp, k=k: _product(bg(), bp, _cycle_gens(k), k)))
    return specs


def _materialize(builder, lo, hi):
    """Return (N, flat table list) for a group spec, or None if it fails or is out of range."""
    gens = builder()
    elems = _closure(gens, hi)
    if elems is None or not (lo <= len(elems) <= hi):
        return None
    table = _mult_table(elems)
    if table is None:
        return None
    return len(elems), table.ravel().tolist()


def _select_groups(d, D, moore):
    """Pick up to 6 candidate groups, spread over the order range, largest first."""
    hi = moore // 2
    lo = max(d + 1, int(0.4 * hi))
    if hi < lo:
        return []
    specs = sorted(_group_specs(lo, hi), key=lambda s: -s[0])
    gap = max(1, (hi - lo) // 8)
    out = []
    last = None
    for order, builder in specs:
        if len(out) >= 6:
            break
        if last is not None and order > last - gap:
            continue
        mat = _materialize(builder, lo, hi)
        if mat is None:
            continue
        out.append(mat)
        last = mat[0]
    return out


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    if d >= 3:
        try:
            groups = _select_groups(d, D, moore)
            if groups:
                remaining = 0.85 * time_limit - (time.monotonic() - start) - 3.0
                if remaining >= 2.0:
                    flat = [len(groups)]
                    for N, table in groups:
                        flat.append(N)
                        flat.extend(table)
                    if len(flat) % 2:
                        flat.append(0)
                    stdin = (len(flat), list(zip(flat[0::2], flat[1::2])))
                    out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                                    stdin_graph=stdin, timeout=remaining + 8.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
