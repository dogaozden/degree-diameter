import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: the Python side builds arc-extended projective-plane starts
# (diameter 3, from the parent), and a new C engine then grows the graph by
# vertex insertion plus simulated annealing over degree-preserving 2-switches,
# endpoint moves and fills. Distances are checked exactly with bitset BFS in C.
# The annealer minimises the number of vertex pairs at distance > D.
# Every returned graph is re-checked with lib.is_valid, and K_{d,d} is the
# fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXW 19
#define MAXM 40000
#define MAXD 40
#define STALL 30000

static int d_, D_, n, M, W;
static int col[MAXN], deg[MAXN];
static int eu[MAXM], ev[MAXM];
static unsigned char amat[MAXN][MAXN];
static int adjc[MAXN], adjl[MAXN][MAXD];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int bestN = -1, bestM = 0;
static int bestEU[MAXM], bestEV[MAXM], bestCol[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* number of unordered pairs at distance > D_ */
static long long cost(void) {
    for (int v = 0; v < n; v++) adjc[v] = 0;
    for (int i = 0; i < M; i++) {
        int a = eu[i], b = ev[i];
        adjl[a][adjc[a]++] = b;
        adjl[b][adjc[b]++] = a;
    }
    W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < adjc[v]; k++) {
                int u = adjl[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void add_e(int a, int b) {
    int x, y;
    if (col[a] == 0) { x = a; y = b; } else { x = b; y = a; }
    eu[M] = x; ev[M] = y; M++;
    amat[x][y] = 1; amat[y][x] = 1;
    deg[x]++; deg[y]++;
}

static int del_e(int a, int b) {
    int x, y;
    if (col[a] == 0) { x = a; y = b; } else { x = b; y = a; }
    for (int i = 0; i < M; i++) {
        if (eu[i] == x && ev[i] == y) {
            eu[i] = eu[M - 1]; ev[i] = ev[M - 1]; M--;
            amat[x][y] = 0; amat[y][x] = 0;
            deg[x]--; deg[y]--;
            return 1;
        }
    }
    return 0;
}

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

static void apply_move(Move *m) {
    for (int i = 0; i < m->nr; i++) del_e(m->ra[i], m->rb[i]);
    for (int i = 0; i < m->na; i++) add_e(m->aa[i], m->ab[i]);
}

static void undo_move(Move *m) {
    for (int i = 0; i < m->na; i++) del_e(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nr; i++) add_e(m->ra[i], m->rb[i]);
}

static int propose(Move *mv) {
    mv->nr = 0; mv->na = 0;
    if (M == 0) return 0;
    double u = urand();
    if (u < 0.5) {
        if (M < 2) return 0;
        int i = rint_(M), j = rint_(M);
        if (i == j) return 0;
        int a = eu[i], b = ev[i], a2 = eu[j], b2 = ev[j];
        if (a == a2 || b == b2) return 0;
        if (amat[a][b2] || amat[a2][b]) return 0;
        mv->nr = 2;
        mv->ra[0] = a; mv->rb[0] = b; mv->ra[1] = a2; mv->rb[1] = b2;
        mv->na = 2;
        mv->aa[0] = a; mv->ab[0] = b2; mv->aa[1] = a2; mv->ab[1] = b;
        return 1;
    } else if (u < 0.8) {
        int i = rint_(M);
        int a = eu[i], b = ev[i];
        if (rnd64() & 1ULL) {
            int y = rint_(n);
            if (y == b || col[y] != col[b] || deg[y] >= d_ || amat[a][y]) return 0;
            mv->nr = 1; mv->ra[0] = a; mv->rb[0] = b;
            mv->na = 1; mv->aa[0] = a; mv->ab[0] = y;
        } else {
            int x = rint_(n);
            if (x == a || col[x] != col[a] || deg[x] >= d_ || amat[x][b]) return 0;
            mv->nr = 1; mv->ra[0] = a; mv->rb[0] = b;
            mv->na = 1; mv->aa[0] = x; mv->ab[0] = b;
        }
        return 1;
    } else {
        int x = rint_(n), y = rint_(n);
        if (x == y || col[x] == col[y] || deg[x] >= d_ || deg[y] >= d_ || amat[x][y]) return 0;
        mv->na = 1; mv->aa[0] = x; mv->ab[0] = y;
        return 1;
    }
}

static void grow(void) {
    int c = (int)(rnd64() & 1ULL);
    int v = n;
    n++;
    col[v] = c;
    deg[v] = 0;
    for (int t = 0; t < 2000 && deg[v] < d_ && v > 0; t++) {
        int y = rint_(v);
        if (col[y] == c || deg[y] >= d_ || amat[v][y]) continue;
        add_e(v, y);
    }
}

static void save_best(void) {
    bestN = n;
    bestM = M;
    memcpy(bestEU, eu, sizeof(int) * (size_t)M);
    memcpy(bestEV, ev, sizeof(int) * (size_t)M);
    memcpy(bestCol, col, sizeof(int) * (size_t)n);
}

static void load_state(int N, int MM, const int *EU, const int *EV, const int *C) {
    n = N; M = MM;
    memcpy(eu, EU, sizeof(int) * (size_t)M);
    memcpy(ev, EV, sizeof(int) * (size_t)M);
    memcpy(col, C, sizeof(int) * (size_t)n);
    memset(amat, 0, sizeof amat);
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M; i++) {
        deg[eu[i]]++; deg[ev[i]]++;
        amat[eu[i]][ev[i]] = 1; amat[ev[i]][eu[i]] = 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long sd = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (sd + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd64();
    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 100 || M0 < 0 || M0 > MAXM) {
        printf("0 0\n"); return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(M0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(M0 + 1));
    int *dg = calloc((size_t)N0, sizeof(int));
    int *colr = malloc(sizeof(int) * (size_t)N0);
    int *q = malloc(sizeof(int) * (size_t)N0);
    int ok = 1;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) { ok = 0; break; }
        iu[i] = u; iv[i] = v;
        dg[u]++; dg[v]++;
        if (dg[u] > d_ || dg[v] > d_) { ok = 0; break; }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    for (int v = 0; v < N0; v++) { adjc[v] = 0; colr[v] = -1; }
    for (int i = 0; i < M0; i++) {
        int u = iu[i], v = iv[i];
        adjl[u][adjc[u]++] = v;
        adjl[v][adjc[v]++] = u;
    }
    for (int s = 0; s < N0 && ok; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < adjc[u]; k++) {
                int w = adjl[u][k];
                if (colr[w] < 0) { colr[w] = 1 - colr[u]; q[t++] = w; }
                else if (colr[w] == colr[u]) { ok = 0; }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    n = N0; M = 0;
    for (int v = 0; v < n; v++) { col[v] = colr[v]; deg[v] = 0; }
    for (int i = 0; i < M0; i++) {
        int u = iu[i], v = iv[i];
        if (amat[u][v]) { ok = 0; break; }
        add_e(u, v);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    long long cur = cost();
    if (cur == 0) save_best();

    double deadline = now_s() + budget;
    double T = 2.0;
    int stall = 0;
    long long iter = 0;
    for (;;) {
        if ((iter & 31) == 0 && now_s() > deadline) break;
        iter++;
        if (cur == 0) {
            save_best();
            if (n + 2 >= MAXN - 1) break;
            grow();
            cur = cost();
            stall = 0;
            T = 2.0;
            continue;
        }
        if (stall > STALL && bestN >= 0) {
            load_state(bestN, bestM, bestEU, bestEV, bestCol);
            cur = cost();
            stall = 0;
            T = 2.0;
            continue;
        }
        Move mv;
        stall++;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            if (nc < cur) stall = 0;
            cur = nc;
        } else {
            undo_move(&mv);
        }
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEU[i], bestEV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), from the parent.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets so every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Build: best arc-extension (or K_{d,d}) start, then C vertex-growth annealing.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0]:
                consider(n_c, e_c)

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=best, timeout=budget + 10.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
