import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving bipartite annealing with vertex insertion and
# removal. The energy is (bad pairs at distance > D) - BETA * (vertex count).
# The engine keeps the largest valid graph it sees. Every graph it works on
# has max degree <= d and is bipartite; the Python side re-checks the output.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXW (MAXN / 64)
#define BETA 1.0
#define T0 2.0
#define T1 0.05
#define CYCLES 4.0
#define RESTART 30000LL

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static State S1, S2, SB;
static int best_n = 0;
static int dd, DD;
static uint64_t rs;
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static int queue_buf[MAXN];

static uint64_t rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++)
        if (s->adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(State *s, int a, int b) {
    s->adj[a][s->deg[a]++] = b;
    s->adj[b][s->deg[b]++] = a;
}

static void del_one(State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++) {
        if (s->adj[a][k] == b) {
            s->adj[a][k] = s->adj[a][--s->deg[a]];
            return;
        }
    }
}

static void remove_edge(State *s, int a, int b) {
    del_one(s, a, b);
    del_one(s, b, a);
}

static void remove_vertex(State *s, int v) {
    for (int k = 0; k < s->deg[v]; k++) del_one(s, s->adj[v][k], v);
    int last = s->n - 1;
    if (v != last) {
        for (int k = 0; k < s->deg[last]; k++) {
            int u = s->adj[last][k];
            for (int j = 0; j < s->deg[u]; j++) {
                if (s->adj[u][j] == last) { s->adj[u][j] = v; break; }
            }
        }
        s->deg[v] = s->deg[last];
        memcpy(s->adj[v], s->adj[last], sizeof(int) * MAXD);
        s->col[v] = s->col[last];
    }
    s->deg[last] = 0;
    s->n = last;
}

static void copy_state(State *dst, const State *src) {
    int n = src->n;
    dst->n = n;
    memcpy(dst->deg, src->deg, sizeof(int) * n);
    memcpy(dst->col, src->col, sizeof(int) * n);
    memcpy(dst->adj, src->adj, sizeof(int) * MAXD * n);
}

static void make_kdd(State *s) {
    s->n = 2 * dd;
    for (int v = 0; v < s->n; v++) {
        s->deg[v] = 0;
        s->col[v] = (v < dd) ? 0 : 1;
    }
    for (int i = 0; i < dd; i++)
        for (int j = dd; j < 2 * dd; j++)
            add_edge(s, i, j);
}

static int read_start(State *s) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0) return 0;
    s->n = n;
    for (int v = 0; v < n; v++) { s->deg[v] = 0; s->col[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (s->deg[u] >= dd || s->deg[v] >= dd) return 0;
        if (has_edge(s, u, v)) return 0;
        add_edge(s, u, v);
    }
    for (int r = 0; r < n; r++) {
        if (s->col[r] != -1) continue;
        s->col[r] = 0;
        int qh = 0, qt = 0;
        queue_buf[qt++] = r;
        while (qh < qt) {
            int x = queue_buf[qh++];
            for (int k = 0; k < s->deg[x]; k++) {
                int y = s->adj[x][k];
                if (s->col[y] == -1) {
                    s->col[y] = 1 - s->col[x];
                    queue_buf[qt++] = y;
                } else if (s->col[y] == s->col[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Number of unordered pairs at distance > DD (unreachable pairs included). */
static long long bad_count(const State *s) {
    int n = s->n;
    if (n <= 1) return 0;
    int W = (n + 63) >> 6;
    uint64_t (*A)[MAXW] = bufA, (*B)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        memset(A[v], 0, sizeof(uint64_t) * W);
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(B[v], A[v], sizeof(uint64_t) * W);
            for (int k = 0; k < s->deg[v]; k++) {
                const uint64_t *src = A[s->adj[v][k]];
                for (int w = 0; w < W; w++) B[v][w] |= src[w];
            }
        }
        uint64_t (*Tm)[MAXW] = A;
        A = B;
        B = Tm;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(A[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void save_best(const State *s) {
    copy_state(&SB, s);
    best_n = s->n;
}

/* Degree-preserving bipartite double-edge switch. */
static int move_switch(State *t) {
    int n = t->n;
    for (int tries = 0; tries < 50; tries++) {
        int a = rint_(n);
        if (t->col[a] != 0 || t->deg[a] == 0) continue;
        int c = rint_(n);
        if (c == a || t->col[c] != 0 || t->deg[c] == 0) continue;
        int b = t->adj[a][rint_(t->deg[a])];
        int e = t->adj[c][rint_(t->deg[c])];
        if (b == e) continue;
        if (has_edge(t, a, e) || has_edge(t, c, b)) continue;
        remove_edge(t, a, b);
        remove_edge(t, c, e);
        add_edge(t, a, e);
        add_edge(t, c, b);
        return 1;
    }
    return 0;
}

static int move_addedge(State *t) {
    int n = t->n;
    for (int tries = 0; tries < 60; tries++) {
        int a = rint_(n);
        int b = rint_(n);
        if (t->col[a] != 0 || t->col[b] != 1) continue;
        if (t->deg[a] >= dd || t->deg[b] >= dd) continue;
        if (has_edge(t, a, b)) continue;
        add_edge(t, a, b);
        return 1;
    }
    return 0;
}

static int move_remove_edge(State *t) {
    int n = t->n;
    for (int tries = 0; tries < 50; tries++) {
        int a = rint_(n);
        if (t->deg[a] == 0) continue;
        int b = t->adj[a][rint_(t->deg[a])];
        remove_edge(t, a, b);
        return 1;
    }
    return 0;
}

/* Insert a vertex on a random side; take up to dd opposite-side neighbours,
   removing one edge at each neighbour that is already saturated. */
static int move_addvertex(State *t) {
    if (t->n >= MAXN - 1) return 0;
    int c = rint_(2);
    int v = t->n;
    t->n = v + 1;
    t->deg[v] = 0;
    t->col[v] = c;
    int opp = 1 - c;
    int got = 0;
    for (int tries = 0; tries < 400 && got < dd; tries++) {
        int u = rint_(v);
        if (t->col[u] != opp) continue;
        if (has_edge(t, v, u)) continue;
        if (t->deg[u] >= dd) {
            int w = t->adj[u][rint_(t->deg[u])];
            remove_edge(t, u, w);
        }
        add_edge(t, v, u);
        got++;
    }
    return got > 0;
}

static int move_removevertex(State *t) {
    if (t->n <= dd + 1) return 0;
    int v = rint_(t->n);
    remove_vertex(t, v);
    return 1;
}

static int propose(State *t) {
    if (t->n < 2) return 0;
    int r = rint_(100);
    if (r < 55) return move_switch(t);
    if (r < 75) return move_addedge(t);
    if (r < 80) return move_remove_edge(t);
    if (r < 93) return move_addvertex(t);
    return move_removevertex(t);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (dd < 1 || dd > MAXD || DD < 2) {
        printf("0 0\n");
        return 0;
    }

    State *cp = &S1, *tp = &S2;
    if (!read_start(cp)) make_kdd(cp);
    long long bad_cur = bad_count(cp);
    if (bad_cur == 0) {
        save_best(cp);
    } else {
        make_kdd(tp);
        save_best(tp);
    }

    double Ecur = (double)bad_cur - BETA * cp->n;
    long long since = 0;
    clock_t t0 = clock();
    for (;;) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        double x = CYCLES * el / budget;
        x -= floor(x);
        double T = T0 * pow(T1 / T0, x);

        copy_state(tp, cp);
        since++;
        if (!propose(tp)) continue;
        long long bt = bad_count(tp);
        double Et = (double)bt - BETA * tp->n;
        double dE = Et - Ecur;
        if (dE <= 0.0 || rdbl() < exp(-dE / T)) {
            State *sw = cp;
            cp = tp;
            tp = sw;
            bad_cur = bt;
            Ecur = Et;
            if (bt == 0 && cp->n > best_n) {
                save_best(cp);
                since = 0;
            }
        }
        if (since > RESTART && best_n > 0) {
            copy_state(cp, &SB);
            bad_cur = 0;
            Ecur = -BETA * cp->n;
            since = 0;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = 0;
    for (int v = 0; v < SB.n; v++)
        for (int k = 0; k < SB.deg[v]; k++)
            if (v < SB.adj[v][k]) m++;
    printf("%d %d\n", SB.n, m);
    for (int v = 0; v < SB.n; v++)
        for (int k = 0; k < SB.deg[v]; k++)
            if (v < SB.adj[v][k]) printf("%d %d\n", v, SB.adj[v][k]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q). Order 2(q+1)(q^2+1), degree q+1."""
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


def _largest_pp_le(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _smallest_pp_ge(x, hi):
    """Smallest prime power q with max(2, x) <= q <= hi, or None."""
    for q in range(max(2, x), hi + 1):
        if lib.is_prime_power(q):
            return q
    return None


def _candidates(d, D):
    """Structured bipartite graphs with max degree d (or slightly more, to be thinned)."""
    out = []
    if D >= 3:
        q = _largest_pp_le(d - 1)
        if q is not None and q <= 13:
            out.append(lib.projective_plane_incidence(q))
        q = _smallest_pp_ge(d - 1, 13)
        if q is not None:
            out.append(lib.projective_plane_incidence(q))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_pp_le(d - 1)
        if q is not None and q <= 9:
            out.append(_gq_w(q))
        q = _smallest_pp_ge(d - 1, 9)
        if q is not None:
            out.append(_gq_w(q))
    return out


def _reduce(n, edges, d, rng):
    """Remove edges so every vertex has degree <= d. Bipartiteness is preserved."""
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
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2 and is always valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Structured starts. Each is thinned to max degree d; valid ones are kept as fallbacks.
    starts = []
    for g in _candidates(d, D):
        consider(*g)
        starts.append(_reduce(g[0], g[1], d, rng))
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    starts.append(lib.haar_graph(d, range(d)))
    starts.sort(key=lambda g: -g[0])
    runs = starts[:2]

    # Annealing runs in C, one per start, sharing the usable budget.
    for i, (n, e) in enumerate(runs):
        remaining = deadline - time.monotonic()
        left = len(runs) - i
        budget = remaining / left - 1.0
        if budget < 2.0:
            break
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 7 + i + 1, round(budget, 2)],
                            stdin_graph=(n, e), timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            continue

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
