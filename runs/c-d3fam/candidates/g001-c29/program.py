import itertools
import time

import lib

# C search engine: degree-capped bipartite graph annealing with vertex insertion.
# It keeps the largest valid graph it has seen and never outputs an invalid one.
C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define WMAX 64
#define MAXDEG 60
#define MAXE (MAXN * 32)
#define STAG 50000

static int dd, DD;
static int n;
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];

static uint64_t P1[MAXN][WMAX];
static uint64_t P2[MAXN][WMAX];
static uint64_t RB[MAXN][WMAX];
static uint64_t RS[MAXN][WMAX];
static uint64_t covered[WMAX];
static int used[MAXN];

static int best_n = 0, best_m = 0;
static int best_col[MAXN];
static int best_u[MAXE], best_v[MAXE];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; return; }
    }
}

static void remove_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* res[v] = bitset of vertices within distance r of v. */
static void ball(int r, uint64_t (*res)[WMAX]) {
    int W = (n + 63) >> 6;
    uint64_t (*src)[WMAX] = P1, (*dst)[WMAX] = P2, (*tmp)[WMAX];
    for (int v = 0; v < n; v++) {
        memset(src[v], 0, sizeof(uint64_t) * W);
        src[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            memcpy(dst[v], src[v], sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) dst[v][w] |= src[u][w];
            }
        }
        tmp = src; src = dst; dst = tmp;
    }
    for (int v = 0; v < n; v++) memcpy(res[v], src[v], sizeof(uint64_t) * W);
}

/* Number of unordered vertex pairs at distance > DD. Zero iff valid. */
static long cost_now(void) {
    int W = (n + 63) >> 6;
    ball(DD, RS);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(RS[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Insert a new vertex, greedily covering the old vertices by radius DD-1 balls. */
static void insert_vertex(void) {
    int c = rndi(2);
    int x = n;
    n++;
    col[x] = c;
    deg[x] = 0;
    int W = (n + 63) >> 6;
    ball(DD - 1, RB);
    for (int w = 0; w < W; w++) covered[w] = 0;
    covered[x >> 6] |= 1ULL << (x & 63);
    for (int u = 0; u < n; u++) used[u] = 0;
    int picks = 0;
    while (picks < dd) {
        int best = -1, bestg = 0;
        for (int u = 0; u < x; u++) {
            if (col[u] == c || used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(RB[u][w] & ~covered[w]);
            if (g > bestg) { bestg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        if (deg[best] >= dd) {
            int w2 = adj[best][rndi(deg[best])];
            remove_edge(best, w2);
        }
        add_edge(x, best);
        picks++;
        for (int w = 0; w < W; w++) covered[w] |= RB[best][w];
    }
    for (int t = 0; t < 1000 && picks == 0; t++) {
        int u = rndi(x);
        if (col[u] == c) continue;
        if (deg[u] >= dd) {
            int w2 = adj[u][rndi(deg[u])];
            remove_edge(u, w2);
        }
        add_edge(x, u);
        picks = 1;
    }
}

static int pick_vertex(int c, int need) {
    for (int t = 0; t < 200; t++) {
        int v = rndi(n);
        if (col[v] != c) continue;
        if (need == 1 && deg[v] == 0) continue;
        if (need == 2 && deg[v] >= dd) continue;
        return v;
    }
    return -1;
}

typedef struct { int nr, na; int ru[2], rv[2], au[2], av[2]; } Move;

/* type 0: add edge; type 1: rewire one endpoint; type 2: degree-preserving swap. */
static int make_move(Move *m, int type) {
    m->nr = 0;
    m->na = 0;
    if (type == 0) {
        int u = pick_vertex(0, 2), w = pick_vertex(1, 2);
        if (u < 0 || w < 0 || has_edge(u, w)) return 0;
        m->na = 1; m->au[0] = u; m->av[0] = w;
        return 1;
    }
    if (type == 1) {
        int u = rndi(n);
        if (deg[u] == 0) return 0;
        int v = adj[u][rndi(deg[u])];
        int w = -1;
        for (int t = 0; t < 20; t++) {
            int x = rndi(n);
            if (col[x] == col[u] || x == v || deg[x] >= dd || has_edge(u, x)) continue;
            w = x;
            break;
        }
        if (w < 0) return 0;
        m->nr = 1; m->ru[0] = u; m->rv[0] = v;
        m->na = 1; m->au[0] = u; m->av[0] = w;
        return 1;
    }
    int a = pick_vertex(0, 1);
    if (a < 0) return 0;
    int b = adj[a][rndi(deg[a])];
    int c = pick_vertex(0, 1);
    if (c < 0 || c == a) return 0;
    int e = adj[c][rndi(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    m->nr = 2; m->ru[0] = a; m->rv[0] = b; m->ru[1] = c; m->rv[1] = e;
    m->na = 2; m->au[0] = a; m->av[0] = e; m->au[1] = c; m->av[1] = b;
    return 1;
}

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) remove_edge(m->ru[i], m->rv[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->au[i], m->av[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) remove_edge(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ru[i], m->rv[i]);
}

static void save_snapshot(void) {
    best_n = n;
    best_m = 0;
    for (int v = 0; v < n; v++) {
        best_col[v] = col[v];
        if (col[v] == 0) {
            for (int k = 0; k < deg[v]; k++) {
                best_u[best_m] = v;
                best_v[best_m] = adj[v][k];
                best_m++;
            }
        }
    }
}

static void load_snapshot(void) {
    n = best_n;
    for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = best_col[v]; }
    for (int i = 0; i < best_m; i++) add_edge(best_u[i], best_v[i]);
}

/* Returns 1 on success (graph loaded), 0 if empty input, -1 on invalid input. */
static int read_input(void) {
    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2) return 0;
    if (nn == 0) return 0;
    if (nn < 0 || nn >= MAXN || mm < 0) return -1;
    n = nn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < mm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return -1;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return -1;
        if (has_edge(u, v)) return -1;
        if (deg[u] >= dd || deg[v] >= dd) return -1;
        add_edge(u, v);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stack[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] == -1) { col[v] = 1 - col[u]; stack[sp++] = v; }
                else if (col[v] == col[u]) return -1;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    if (dd < 2 || dd > MAXDEG || DD < 2 || DD > 40) { printf("0 0\n"); return 0; }

    int rc = read_input();
    if (rc < 0) { printf("0 0\n"); return 0; }
    if (rc == 0) {
        n = 2 * dd;
        for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = (v >= dd); }
        for (int i = 0; i < dd; i++)
            for (int j = 0; j < dd; j++) add_edge(i, dd + j);
    }

    double moore = 0.0, pw = 1.0;
    for (int i = 0; i < DD; i++) { moore += pw; pw *= (dd - 1); }
    moore *= 2.0;

    long cur = cost_now();
    long lvl_best = cur;
    long since = 0, lit = 0;

    while (elapsed() < tl) {
        if (cur == 0) {
            if (n > best_n) save_snapshot();
            if ((double)(n + 1) > moore || n + 1 >= MAXN) break;
            insert_vertex();
            cur = cost_now();
            lvl_best = cur;
            since = 0;
            lit = 0;
            continue;
        }
        lit++;
        since++;
        double T = 0.2 + 1.0 / (1.0 + (double)lit / 2000.0);
        double r = rndd();
        int type = r < 0.2 ? 0 : (r < 0.55 ? 1 : 2);
        Move m;
        if (make_move(&m, type)) {
            apply_move(&m);
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rndd() < exp(-(double)delta / T)) cur = nc;
            else undo_move(&m);
        }
        if (cur < lvl_best) { lvl_best = cur; since = 0; }
        if (since > STAG) {
            if (best_n > 0) {
                load_snapshot();
                if ((double)(n + 1) > moore) break;
                insert_vertex();
            }
            cur = cost_now();
            lvl_best = cur;
            since = 0;
            lit = 0;
        }
    }
    if (cur == 0 && n > best_n) save_snapshot();

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_u[i], best_v[i]);
    return 0;
}
'''

GQ_Q_MAX = 9        # largest q for which W(q) is built (pair loop is O(P^2))
C_FRAC = 0.75       # wall-clock fraction of time_limit by which the C search must finish
C_RESERVE = 3.0     # seconds reserved for compile, parsing and Python overhead


# ---------------------------------------------------------------- constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


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
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _valid_best(cands, d, D):
    """Largest candidate that passes lib.is_valid, or None."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    kdd = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2, always valid
    if D == 2:
        return kdd

    cands = [kdd]

    # D >= 3: projective plane (diameter 3). Moore-extremal when d-1 is a prime power.
    pg = _pg_base(d) if d >= 3 else None
    if pg is not None:
        if D == 3 and lib.is_prime_power(d - 1):
            return _valid_best(cands + [pg], d, D) or kdd
        cands.append(pg)

    # Araujo-Pardo & Lopez record graph for d = q+2, q a prime power (diameter 3).
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass

    # D >= 4: generalized quadrangle (diameter 4).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
                return _valid_best(cands + [gq], d, D) or kdd
            cands.append(gq)

    best = _valid_best(cands, d, D) or kdd

    # Search: start from the largest valid construction and let C insert vertices.
    elapsed = time.monotonic() - start
    budget = time_limit * C_FRAC - elapsed - C_RESERVE
    if budget < 1.0:
        return best
    n0, e0 = best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(n0, e0), timeout=budget + 10.0)
        n1, e1 = lib.parse_graph_text(text)
        if n1 > n0 and lib.is_valid(n1, e1, d, D):
            return n1, e1
    except Exception:
        pass
    return best
