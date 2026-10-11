import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count for lifts
MAX_C_N = 4000                # vertex cap handed to the C search (engine arrays hold 4096)
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                   # annealing attempts per candidate lift size
POST_EXTEND_SLICE = 1.5       # seconds given to greedy extension of the best lift
PY_FRAC_GENERIC = 0.3         # Python construction share of time_limit when no Araujo-Lopez start exists
PY_SECONDS_ARAUJO = 2.0       # Python construction seconds when the Araujo-Lopez start is available
END_FRAC = 0.96              # the whole program aims to finish by this fraction of time_limit


# ---------------------------------------------------------------- C iterated local search

C_SOURCE = r"""
/* Iterated local search for bipartite graphs with max degree d and diameter <= D.
 *
 * Moves (all keep the graph valid, so output is valid by construction):
 *  - insertion: a new vertex on one side is joined to at most d opposite-side vertices with
 *    spare degree whose radius-(D-1) balls cover every vertex. Such a vertex is at distance
 *    <= D from everything, and old distances only shrink. Found by randomized greedy set cover.
 *  - augmentation: add edges between opposite sides with spare degree (only shortens paths).
 *  - kick: delete 1 or 2 random vertices, keep the result only if it is still valid
 *    (diameter <= D), otherwise roll back.
 * The largest valid graph seen is printed as "n m" followed by m edge lines.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define DMAX 64
#define WMAX (MAXN / 64)
#define ATT 40
#define SLACK 2

typedef uint64_t u64;

static int d_, D_, cap_;
static int n_, W_;
static int deg_[MAXN];
static int nb_[MAXN][DMAX];
static int col_[MAXN];
static u64 ball_[MAXN][WMAX];
static u64 tmpb_[MAXN][WMAX];

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int nb[MAXN][DMAX];
} Snap;

static Snap best_s, roll_s;

static u64 rng_s = 1;

static u64 rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static int rndi(int k) { return (int)(rnd64() % (u64)k); }

static double rndf(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg_[u]; i++)
        if (nb_[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nb_[u][deg_[u]++] = v;
    nb_[v][deg_[v]++] = u;
}

static void remove_vertex(int x) {
    for (int i = 0; i < deg_[x]; i++) {
        int y = nb_[x][i];
        for (int j = 0; j < deg_[y]; j++) {
            if (nb_[y][j] == x) {
                nb_[y][j] = nb_[y][--deg_[y]];
                break;
            }
        }
    }
    int L = n_ - 1;
    if (x != L) {
        col_[x] = col_[L];
        deg_[x] = deg_[L];
        memcpy(nb_[x], nb_[L], sizeof(int) * (size_t)deg_[L]);
        for (int i = 0; i < deg_[x]; i++) {
            int y = nb_[x][i];
            for (int j = 0; j < deg_[y]; j++) {
                if (nb_[y][j] == L) {
                    nb_[y][j] = x;
                    break;
                }
            }
        }
    }
    deg_[L] = 0;
    n_--;
}

/* ball_[v] = bitset of vertices within distance R of v. */
static void compute_balls(int R) {
    int n = n_;
    if (R > n) R = n;
    if (R < 0) R = 0;
    W_ = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W_; w++) ball_[v][w] = 0;
        ball_[v][v >> 6] |= (u64)1 << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W_; w++) tmpb_[v][w] = ball_[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                int u = nb_[v][i];
                for (int w = 0; w < W_; w++) tmpb_[v][w] |= ball_[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W_; w++) ball_[v][w] = tmpb_[v][w];
    }
}

/* True iff every pair of vertices is at distance <= D_. */
static int valid_full(void) {
    compute_balls(D_);
    for (int v = 0; v < n_; v++) {
        int c = 0;
        for (int w = 0; w < W_; w++) c += pc64(ball_[v][w]);
        if (c != n_) return 0;
    }
    return 1;
}

/* Randomized greedy set cover: try to insert one new vertex. Uses ball_ at radius D_-1,
 * which must be current. Returns 1 if a vertex was added. */
static int try_grow(int attempts) {
    int n = n_, W = W_;
    int order = rndi(2);
    for (int oc = 0; oc < 2; oc++) {
        int c = order ^ oc;                 /* colour of the new vertex */
        static int cand[MAXN];
        int nc = 0;
        for (int u = 0; u < n; u++)
            if (col_[u] == 1 - c && deg_[u] < d_) cand[nc++] = u;
        if (nc == 0) continue;
        for (int a = 0; a < attempts; a++) {
            u64 cov[WMAX];
            memset(cov, 0, sizeof(cov));
            static int avail[MAXN], gains[MAXN];
            memcpy(avail, cand, sizeof(int) * (size_t)nc);
            int na = nc;
            int chosen[DMAX];
            int nch = 0;
            int uncov = n;
            int noisy = a & 1;
            while (uncov > 0 && nch < d_ && na > 0) {
                int bg = 0, bi = -1, ties = 0;
                for (int i = 0; i < na; i++) {
                    const u64 *b = ball_[avail[i]];
                    int g = 0;
                    for (int w = 0; w < W; w++) g += pc64(b[w] & ~cov[w]);
                    gains[i] = g;
                    if (g > bg) {
                        bg = g;
                        bi = i;
                        ties = 1;
                    } else if (g == bg && g > 0) {
                        ties++;
                        if (rndi(ties) == 0) bi = i;
                    }
                }
                if (bg == 0) break;
                int pick = bi;
                if (noisy && rndf() < 0.25) {
                    int cntp = 0;
                    for (int i = 0; i < na; i++) if (gains[i] > 0) cntp++;
                    int r = rndi(cntp);
                    for (int i = 0; i < na; i++) {
                        if (gains[i] > 0) {
                            if (r == 0) { pick = i; break; }
                            r--;
                        }
                    }
                }
                int u = avail[pick];
                chosen[nch++] = u;
                const u64 *b = ball_[u];
                for (int w = 0; w < W; w++) {
                    uncov -= pc64(b[w] & ~cov[w]);
                    cov[w] |= b[w];
                }
                avail[pick] = avail[--na];
            }
            if (uncov == 0 && nch > 0 && n_ < MAXN) {
                int x = n_;
                col_[x] = c;
                deg_[x] = 0;
                for (int i = 0; i < nch; i++) add_edge(chosen[i], x);
                n_++;
                return 1;
            }
        }
    }
    return 0;
}

/* Add edges between opposite colour classes using spare degree (keeps validity). */
static void augment(void) {
    static int us[MAXN], cv[MAXN];
    int nu = 0;
    for (int u = 0; u < n_; u++)
        if (deg_[u] < d_) us[nu++] = u;
    if (nu == 0) return;
    for (int i = nu - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = us[i];
        us[i] = us[j];
        us[j] = t;
    }
    for (int k = 0; k < nu; k++) {
        int u = us[k];
        if (deg_[u] >= d_) continue;
        int nv = 0;
        for (int v = 0; v < n_; v++)
            if (col_[v] != col_[u] && deg_[v] < d_ && !has_edge(u, v)) cv[nv++] = v;
        if (nv > 0) add_edge(u, cv[rndi(nv)]);
    }
}

static void save_snap(Snap *s) {
    s->n = n_;
    memcpy(s->deg, deg_, sizeof(int) * (size_t)n_);
    memcpy(s->col, col_, sizeof(int) * (size_t)n_);
    memcpy(s->nb, nb_, sizeof(int) * (size_t)DMAX * (size_t)n_);
}

static void load_snap(const Snap *s) {
    n_ = s->n;
    memcpy(deg_, s->deg, sizeof(int) * (size_t)n_);
    memcpy(col_, s->col, sizeof(int) * (size_t)n_);
    memcpy(nb_, s->nb, sizeof(int) * (size_t)DMAX * (size_t)n_);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    cap_ = (argc > 5) ? atoi(argv[5]) : MAXN;
    if (d_ > DMAX) d_ = DMAX;
    if (cap_ > MAXN || cap_ <= 0) cap_ = MAXN;
    rng_s = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_s == 0) rng_s = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > MAXN) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    for (int v = 0; v < n; v++) { deg_[v] = 0; col_[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colour the start graph component by component. */
    static int stack[MAXN];
    for (int s = 0; s < n_; s++) {
        if (col_[s] >= 0) continue;
        col_[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < deg_[u]; i++) {
                int w = nb_[u][i];
                if (col_[w] < 0) {
                    col_[w] = 1 - col_[u];
                    stack[sp++] = w;
                }
            }
        }
    }

    double t0 = now_s();
    double deadline = t0 + budget;
    save_snap(&best_s);
    int bestn = n_;

    while (now_s() < deadline) {
        augment();
        compute_balls(D_ - 1);
        if (n_ < cap_ && try_grow(ATT)) {
            if (n_ > bestn) {
                bestn = n_;
                save_snap(&best_s);
            }
            continue;
        }
        /* stalled: first return to the best graph if we drifted too far below it */
        if (n_ < bestn - SLACK) {
            load_snap(&best_s);
            continue;
        }
        /* kick: delete one or two random vertices, keep only if still valid */
        save_snap(&roll_s);
        int k = 1 + (rndf() < 0.3 ? 1 : 0);
        for (int i = 0; i < k && n_ > 2; i++) remove_vertex(rndi(n_));
        if (!valid_full()) load_snap(&roll_s);
    }

    load_snap(&best_s);
    int m2 = 0;
    for (int u = 0; u < n_; u++)
        for (int i = 0; i < deg_[u]; i++)
            if (nb_[u][i] > u) m2++;
    printf("%d %d\n", n_, m2);
    for (int u = 0; u < n_; u++)
        for (int i = 0; i < deg_[u]; i++)
            if (nb_[u][i] > u) printf("%d %d\n", u, nb_[u][i]);
    return 0;
}
"""


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
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
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
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
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


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : projective plane / Araujo-Lopez

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _araujo(d, D):
    """Araujo-Pardo & Lopez record graph for d = q+2 with q a prime power (D = 3), or None."""
    if D != 3:
        return None
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        g = lib.araujo_lopez_graph(q)
    except Exception:
        return None
    return g if lib.is_valid(g[0], g[1], d, D) else None


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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


# ---------------------------------------------------------------- Haar graphs (hill-climb)

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


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices."""
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _try_size(s, m, d, D, rng, deadline):
    """Attempt to anneal a valid lift of size m, with a few independent restarts."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- C search driver

def _c_improve(graph, d, D, seed, hard_end, cap):
    """Run the C iterated local search from `graph`; return (n, edges) or None on any failure."""
    now = time.monotonic()
    budget = hard_end - now - 1.5
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed) % (2 ** 31), round(budget, 2), int(cap)],
                        stdin_graph=graph, timeout=max(2.0, hard_end - now + 1.0))
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + END_FRAC * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # Record constructions for D = 3 start the search; Python search is kept short for them.
    ara = _araujo(d, D)
    if ara is not None:
        cands.append(ara)
        py_end = start + PY_SECONDS_ARAUJO
    else:
        py_end = start + PY_FRAC_GENERIC * time_limit
    deadline = py_end

    # D >= 3: projective plane (diameter 3), extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:   # Moore-extremal, nothing to improve
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Haar graphs with growing modulus (small slice of the remaining Python time).
    now = time.monotonic()
    haar_frac = 0.2 if D <= 4 else 0.1
    haar_end = now + haar_frac * max(0.0, deadline - now)
    haar_best, haar_m, haar_miss = None, d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    # Voltage-lift annealing, one slice per base size s.
    lift_best = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            cands.append(g)
            if lift_best is None or g[0] > lift_best[0]:
                lift_best = g

    # Post-process the largest lift: fill spare degree by augmentation, then extend.
    if lift_best is not None and time.monotonic() < deadline:
        aug = _augment(lift_best[0], lift_best[1], d, seed)
        cands.append(aug)
        ext_end = min(deadline + 1.0, time.monotonic() + POST_EXTEND_SLICE)
        cands.append(_extend(aug[0], aug[1], d, D, rng, ext_end))

    best = _finish(cands, d, D)

    # C iterated local search from the best valid graph; keep it only if valid and larger.
    if d >= 3 and D >= 3 and time.monotonic() < hard_end - 3.0:
        improved = _c_improve(best, d, D, seed, hard_end, min(MAX_C_N, lib.moore_bound(d, D)))
        if improved is not None and improved[0] > best[0] and lib.is_valid(improved[0], improved[1], d, D):
            best = improved

    return best
