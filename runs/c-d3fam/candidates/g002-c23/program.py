import itertools
import random
import time

import lib

# C search engine: vertex-pair insertion followed by simulated annealing on 2-switches.
# Each epoch starts from the best valid graph, inserts two vertices x, y (x adjacent to
# d chosen vertices of the other side, y adjacent to their partners), keeps all degrees
# unchanged, and anneals the number of vertex pairs at distance > D to zero.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1536
#define MAXW ((MAXN + 63) / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define ITER 30000
#define T_HOT 1.2
#define T_COLD 0.15
#define MAXFAIL 200

static int d_, D_, cap_;
static int n, m;
static int col[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char M[MAXN][MAXN];
static int ea[MAXE], eb[MAXE];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int bN, bM;
static int bA[MAXE], bB[MAXE], bC[MAXN];
static uint64_t rs = 88172645463325252ULL;
static time_t t0;
static double Lsec;

static uint64_t rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static double u01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int out_of_time(void) {
    return difftime(time(NULL), t0) >= Lsec;
}

static void build_nb(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int a = ea[i], b = eb[i];
        nb[a][deg[a]++] = b;
        nb[b][deg[b]++] = a;
    }
}

/* Number of unordered vertex pairs at distance > D_ (0 iff valid). */
static long long cost_eval(void) {
    int W = (n + 63) >> 6;
    build_nb();
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[nb[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int p = 0;
        for (int w = 0; w < W; w++) p += __builtin_popcountll(cur[v][w]);
        bad += n - p;
    }
    return bad / 2;
}

static void add_edge_raw(int u, int v) {
    int a = u, b = v;
    if (col[a] != 0) { a = v; b = u; }
    ea[m] = a;
    eb[m] = b;
    m++;
    M[u][v] = 1;
    M[v][u] = 1;
}

static void remove_edge_uv(int u, int v) {
    for (int i = 0; i < m; i++) {
        if ((ea[i] == u && eb[i] == v) || (ea[i] == v && eb[i] == u)) {
            ea[i] = ea[m - 1];
            eb[i] = eb[m - 1];
            m--;
            M[u][v] = 0;
            M[v][u] = 0;
            return;
        }
    }
}

static void load_base(void) {
    n = bN;
    m = bM;
    memcpy(col, bC, sizeof(int) * n);
    memcpy(ea, bA, sizeof(int) * m);
    memcpy(eb, bB, sizeof(int) * m);
    memset(M, 0, sizeof M);
    for (int i = 0; i < m; i++) {
        M[ea[i]][eb[i]] = 1;
        M[eb[i]][ea[i]] = 1;
    }
}

static void save_base(void) {
    bN = n;
    bM = m;
    memcpy(bC, col, sizeof(int) * n);
    memcpy(bA, ea, sizeof(int) * m);
    memcpy(bB, eb, sizeof(int) * m);
}

/* Insert two vertices x (side c) and y (side 1-c) keeping every degree unchanged.
   Greedily picks d edges (a_i, b_i) with distinct endpoints; b_i covers N(b_i) so that
   x (adjacent to all b_i) is at distance <= 2 from as many same-side vertices as possible. */
static int insert_pair(void) {
    static unsigned char cov[MAXN], usedA[MAXN], usedB[MAXN];
    int c = (int)(rnd() & 1ULL);
    build_nb();
    memset(cov, 0, n);
    memset(usedA, 0, n);
    memset(usedB, 0, n);
    int ca[MAXD], cb[MAXD];
    int k = 0;
    while (k < d_) {
        int best = -1, bestA = -1, bestG = -1;
        int off = (int)(rnd() % (uint64_t)n);
        for (int t = 0; t < n; t++) {
            int b = (off + t) % n;
            if (col[b] == c || usedB[b]) continue;
            int dg = deg[b];
            if (dg == 0) continue;
            int st = (int)(rnd() % (uint64_t)dg);
            int aa = -1;
            for (int q = 0; q < dg && aa < 0; q++) {
                int w = nb[b][(st + q) % dg];
                if (!usedA[w]) aa = w;
            }
            if (aa < 0) continue;
            int g = 0;
            for (int q = 0; q < dg; q++) {
                int w = nb[b][q];
                if (w != aa && !cov[w]) g++;
            }
            if (g > bestG) {
                bestG = g;
                best = b;
                bestA = aa;
            }
        }
        if (best < 0) return 0;
        ca[k] = bestA;
        cb[k] = best;
        k++;
        usedA[bestA] = 1;
        usedB[best] = 1;
        for (int q = 0; q < deg[best]; q++) {
            int w = nb[best][q];
            if (w != bestA) cov[w] = 1;
        }
    }
    int x = n, y = n + 1;
    col[x] = c;
    col[y] = 1 - c;
    n += 2;
    for (int i = 0; i < k; i++) remove_edge_uv(ca[i], cb[i]);
    for (int i = 0; i < k; i++) {
        add_edge_raw(x, cb[i]);
        add_edge_raw(y, ca[i]);
    }
    return 1;
}

/* Greedily add edges between spare-degree vertices of opposite sides (never hurts). */
static void fill_spare(void) {
    build_nb();
    for (int u = 0; u < n; u++) {
        if (col[u] != 0 || deg[u] >= d_) continue;
        for (int v = 0; v < n && deg[u] < d_; v++) {
            if (col[v] != 1 || deg[v] >= d_ || M[u][v]) continue;
            add_edge_raw(u, v);
            deg[u]++;
            deg[v]++;
        }
    }
}

/* 2-switch annealing: (a,b),(c,e) -> (a,e),(c,b). Degrees are preserved. */
static long long anneal(long long cur, int iters) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if (out_of_time()) break;
        if (m < 2) break;
        double T = T_HOT + (T_COLD - T_HOT) * ((double)it / (double)iters);
        int i = (int)(rnd() % (uint64_t)m);
        int j = (int)(rnd() % (uint64_t)m);
        if (i == j) continue;
        int a = ea[i], b = eb[i], c2 = ea[j], e = eb[j];
        if (a == c2 || b == e) continue;
        if (M[a][e] || M[c2][b]) continue;
        M[a][b] = 0; M[b][a] = 0;
        M[c2][e] = 0; M[e][c2] = 0;
        M[a][e] = 1; M[e][a] = 1;
        M[c2][b] = 1; M[b][c2] = 1;
        ea[i] = a; eb[i] = e;
        ea[j] = c2; eb[j] = b;
        long long nc = cost_eval();
        if (nc <= cur || u01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            M[a][e] = 0; M[e][a] = 0;
            M[c2][b] = 0; M[b][c2] = 0;
            M[a][b] = 1; M[b][a] = 1;
            M[c2][e] = 1; M[e][c2] = 1;
            ea[i] = a; eb[i] = b;
            ea[j] = c2; eb[j] = e;
        }
    }
    return cur;
}

/* Reads mm edges for a graph on nn vertices; returns 1 iff it is simple, degree <= d_, bipartite. */
static int read_graph(int nn, int mm) {
    for (int i = 0; i < mm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= nn || v >= nn || u == v) return 0;
        ea[i] = u;
        eb[i] = v;
    }
    n = nn;
    m = mm;
    memset(M, 0, sizeof M);
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = ea[i], v = eb[i];
        if (M[u][v]) return 0;
        M[u][v] = 1;
        M[v][u] = 1;
        if (++deg[u] > d_) return 0;
        if (++deg[v] > d_) return 0;
    }
    build_nb();
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < m; i++) {
        if (col[ea[i]] != 0) {
            int t = ea[i];
            ea[i] = eb[i];
            eb[i] = t;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (d_ < 3 || d_ > 60 || D_ < 3) {
        printf("0 0\n");
        return 0;
    }
    Lsec = budget - 1.0;
    if (Lsec < 0) Lsec = 0;
    t0 = time(NULL);

    double bound = 0.0, pw = 1.0;
    for (int i = 0; i < D_; i++) {
        bound += pw;
        pw *= (d_ - 1);
    }
    double cap = 2.0 * bound;
    if (cap > MAXN) cap = MAXN;
    cap_ = (int)cap;

    int n0 = 0, m0 = 0, ok = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && n0 <= MAXN && m0 >= 0 && m0 <= MAXE)
        ok = read_graph(n0, m0);
    if (ok) ok = (cost_eval() == 0);
    if (!ok) {
        n = 2 * d_;
        m = 0;
        memset(M, 0, sizeof M);
        for (int v = 0; v < n; v++) col[v] = (v < d_) ? 0 : 1;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++)
                add_edge_raw(i, d_ + j);
    }

    save_base();
    int fails = 0;
    while (!out_of_time() && bN + 2 <= cap_) {
        load_base();
        if (!insert_pair()) {
            if (++fails > MAXFAIL) break;
            continue;
        }
        fails = 0;
        fill_spare();
        long long cur = cost_eval();
        cur = anneal(cur, ITER);
        if (cur == 0) save_base();
    }

    printf("%d %d\n", bN, bM);
    for (int i = 0; i < bM; i++) printf("%d %d\n", bA[i], bB[i]);
    return 0;
}
"""

GQ_Q_MAX = 9        # largest q for which W(q) is built
C_FRAC = 0.92       # fraction of time_limit covered by the C run plus Python overhead


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite and diameter)."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _best_valid(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))   # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]    # K_{d,d}: diameter 2, always valid

    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal, nothing to improve
                return _best_valid(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                ext_end = min(start + 0.15 * time_limit, time.monotonic() + 0.7)
                cands.append(_extend(g[0], g[1], d, D, rng, ext_end))

    # Araujo-Pardo & Lopez record for D = 3, d = q + 2 with q a prime power >= 3.
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _best_valid(cands + [gq], d, D)   # Moore-extremal for D = 4
            cands.append(gq)

    best = _best_valid(cands, d, D)

    # C engine: grow the best valid start by vertex-pair insertion plus annealing.
    elapsed = time.monotonic() - start
    budget = C_FRAC * time_limit - elapsed - 1.5
    if budget >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, int(budget)], stdin_graph=best,
                             timeout=max(1.0, 0.97 * time_limit - elapsed))
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
    return best
