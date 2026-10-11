import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count for the algebraic/lift phase
ITERS_G = 1200                # annealing moves per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing attempts per lift order
EXTEND_SLICE = 0.5            # seconds per greedy extension run
EXTEND_TRIES = 6              # randomized greedy restarts per base graph
POOL_KEEP = 8                 # candidates kept in the pool
BC_N_MAX = 1600               # largest group order searched for bi-Cayley graphs
BC_GROUPS_PER_ORDER = 3       # semidirect presentations tried per group order
BC_FRAC = 0.3                 # share of remaining time for bi-Cayley search (D >= 4, d >= 4)
HAAR_FRAC = 0.1               # share of remaining time for Haar search
POST_FRAC = 0.1               # share of construction time reserved for final extension
C_SPLIT = 0.45                # constructive phase ends at this fraction of time_limit
C_END = 0.88                  # C refinement ends at this fraction of time_limit
C_MAX_N = 636                 # largest start graph handed to the C engine


# ---------------------------------------------------------------- C engine
#
# Deficit-penalised vertex-insertion annealing (new idea).
# State: a bipartite graph with max degree d, kept on n vertices with a side label each.
# Cost = (number of vertex pairs at distance > D) + (total degree deficit sum(d - deg)).
# Moves: edge addition, rewiring one endpoint of a full vertex, and degree-preserving
# double edge swaps between two left vertices. Whenever the cost reaches zero the graph is
# valid, so it is recorded and grown by one vertex per side (both new vertices start with
# no edges and are pulled in by the annealing). Epochs that fail restart from the best
# valid graph, so the search keeps probing one size above the best one found.

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 640
#define WMAX 10
#define MAXD 16
#define EPOCH 60000L

typedef struct { int kind; int p[4]; } Move;

static int d_, D_;
static int n;
static int side[MAXN];
static unsigned char adj[MAXN][MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static int Lv[MAXN], Rv[MAXN], nL, nR;
static uint64_t bs[MAXN][WMAX], bn[MAXN][WMAX];
static int W;

static int IEU[MAXN * MAXD], IEV[MAXN * MAXD], ISIDE[MAXN];
static int initN, initM;
static int BEU[MAXN * MAXD], BEV[MAXN * MAXD], BSIDE[MAXN];
static int bestN, bestM, hasValid;
static int g_bad, g_cur;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(rnext() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    adj[u][v] = 1;
    adj[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void rem_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    adj[u][v] = 0;
    adj[v][u] = 0;
    rem_nb(u, v);
    rem_nb(v, u);
}

static void rebuild(void) {
    nL = 0;
    nR = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) Lv[nL++] = v;
        else Rv[nR++] = v;
    }
}

static void clear_graph(void) {
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            adj[v][u] = 0;
        }
        deg[v] = 0;
    }
}

static void load_state(int nn, int m, const int *eu, const int *ev, const int *sd) {
    clear_graph();
    n = nn;
    for (int v = 0; v < n; v++) {
        side[v] = sd[v];
        deg[v] = 0;
    }
    for (int i = 0; i < m; i++) add_edge(eu[i], ev[i]);
    rebuild();
}

static int bad_pairs(void) {
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) bs[v][w] = 0;
        bs[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) bn[v][w] = bs[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) bn[v][w] |= bs[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) bs[v][w] = bn[v][w];
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(bs[v][w]);
        tot += n - c;
    }
    return (int)(tot / 2);
}

static int deficit(void) {
    int s = 0;
    for (int v = 0; v < n; v++) s += d_ - deg[v];
    return s;
}

static void evaluate(void) {
    g_bad = bad_pairs();
    g_cur = g_bad + deficit();
}

static void record_best(void) {
    bestN = n;
    bestM = 0;
    for (int v = 0; v < n; v++) {
        BSIDE[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u > v) {
                BEU[bestM] = v;
                BEV[bestM] = u;
                bestM++;
            }
        }
    }
    hasValid = 1;
}

static void restore_best(void) {
    if (hasValid) load_state(bestN, bestM, BEU, BEV, BSIDE);
    else load_state(initN, initM, IEU, IEV, ISIDE);
}

/* Add one vertex on each side; both start with no edges. */
static void grow(void) {
    if (n + 2 > MAXN - 2) return;
    side[n] = 0;
    deg[n] = 0;
    side[n + 1] = 1;
    deg[n + 1] = 0;
    n += 2;
    rebuild();
}

static int propose(Move *m) {
    if (nL == 0 || nR == 0) return 0;
    if (rnd01() < 0.5) {
        if (nL < 2) return 0;
        int a = Lv[rnd(nL)];
        int c = Lv[rnd(nL)];
        if (a == c || deg[a] == 0 || deg[c] == 0) return 0;
        int b = nb[a][rnd(deg[a])];
        int e = nb[c][rnd(deg[c])];
        if (b == e || adj[a][e] || adj[c][b]) return 0;
        m->kind = 4;
        m->p[0] = a;
        m->p[1] = b;
        m->p[2] = c;
        m->p[3] = e;
        return 1;
    }
    int u = Lv[rnd(nL)];
    int v = Rv[rnd(nR)];
    if (adj[u][v]) return 0;
    if (deg[u] < d_ && deg[v] < d_) {
        m->kind = 1;
        m->p[0] = u;
        m->p[1] = v;
        return 1;
    }
    if (deg[u] == d_ && deg[v] < d_ && deg[u] > 0) {
        int w = nb[u][rnd(deg[u])];
        m->kind = 2;
        m->p[0] = u;
        m->p[1] = v;
        m->p[2] = w;
        return 1;
    }
    if (deg[v] == d_ && deg[u] < d_ && deg[v] > 0) {
        int x = nb[v][rnd(deg[v])];
        m->kind = 3;
        m->p[0] = u;
        m->p[1] = v;
        m->p[2] = x;
        return 1;
    }
    return 0;
}

static void apply_move(const Move *m) {
    switch (m->kind) {
    case 1:
        add_edge(m->p[0], m->p[1]);
        break;
    case 2:
        del_edge(m->p[0], m->p[2]);
        add_edge(m->p[0], m->p[1]);
        break;
    case 3:
        del_edge(m->p[2], m->p[1]);
        add_edge(m->p[0], m->p[1]);
        break;
    case 4:
        del_edge(m->p[0], m->p[1]);
        del_edge(m->p[2], m->p[3]);
        add_edge(m->p[0], m->p[3]);
        add_edge(m->p[2], m->p[1]);
        break;
    default:
        break;
    }
}

static void undo_move(const Move *m) {
    switch (m->kind) {
    case 1:
        del_edge(m->p[0], m->p[1]);
        break;
    case 2:
        del_edge(m->p[0], m->p[1]);
        add_edge(m->p[0], m->p[2]);
        break;
    case 3:
        del_edge(m->p[0], m->p[1]);
        add_edge(m->p[2], m->p[1]);
        break;
    case 4:
        del_edge(m->p[0], m->p[3]);
        del_edge(m->p[2], m->p[1]);
        add_edge(m->p[0], m->p[1]);
        add_edge(m->p[2], m->p[3]);
        break;
    default:
        break;
    }
}

static void print_graph(int nn, int mm, const int *eu, const int *ev) {
    printf("%d %d\n", nn, mm);
    for (int i = 0; i < mm; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = (uint64_t)atol(argv[3]) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 <= 0) {
        /* No start graph: K_{d,d}, which is valid for D >= 2. */
        n0 = 2 * d_;
        m0 = 0;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++) {
                IEU[m0] = i;
                IEV[m0] = d_ + j;
                m0++;
            }
        for (int i = 0; i < n0; i++) ISIDE[i] = (i >= d_) ? 1 : 0;
    } else {
        if (n0 > MAXN - 4 || m0 < 0 || m0 > MAXN * MAXD / 2) {
            printf("0 0\n");
            return 0;
        }
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                printf("0 0\n");
                return 0;
            }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
                printf("0 0\n");
                return 0;
            }
            IEU[i] = u;
            IEV[i] = v;
        }
        static int dg[MAXN];
        for (int i = 0; i < n0; i++) dg[i] = 0;
        for (int i = 0; i < m0; i++) {
            dg[IEU[i]]++;
            dg[IEV[i]]++;
        }
        for (int i = 0; i < n0; i++)
            if (dg[i] > d_) {
                printf("0 0\n");
                return 0;
            }
        for (int i = 0; i < m0; i++)
            for (int j = 0; j < i; j++) {
                int a = IEU[i], b = IEV[i], c = IEU[j], e = IEV[j];
                if ((a == c && b == e) || (a == e && b == c)) {
                    printf("0 0\n");
                    return 0;
                }
            }
        /* Two-colouring by relaxation. */
        for (int i = 0; i < n0; i++) ISIDE[i] = -1;
        for (int s = 0; s < n0; s++) {
            if (ISIDE[s] != -1) continue;
            ISIDE[s] = 0;
            int changed = 1;
            while (changed) {
                changed = 0;
                for (int i = 0; i < m0; i++) {
                    int a = IEU[i], b = IEV[i];
                    if (ISIDE[a] != -1 && ISIDE[b] == -1) {
                        ISIDE[b] = 1 - ISIDE[a];
                        changed = 1;
                    } else if (ISIDE[b] != -1 && ISIDE[a] == -1) {
                        ISIDE[a] = 1 - ISIDE[b];
                        changed = 1;
                    }
                }
            }
        }
        for (int i = 0; i < m0; i++)
            if (ISIDE[IEU[i]] == ISIDE[IEV[i]]) {
                printf("0 0\n");
                return 0;
            }
    }

    initN = n0;
    initM = m0;
    hasValid = 0;
    load_state(n0, m0, IEU, IEV, ISIDE);
    evaluate();
    if (g_bad == 0) record_best();

    double tlim = tl * 0.9 - 0.3;
    if (tlim < 0.2) tlim = 0.2;
    clock_t c0 = clock();

    if (g_bad == 0) {
        grow();
        evaluate();
    }

    long it = 0, ep = 0;
    for (;;) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > tlim) break;
        }
        it++;
        if (it - ep >= EPOCH) {
            int base = hasValid ? bestN : initN;
            if (base + 2 > MAXN - 2) break;
            restore_best();
            grow();
            evaluate();
            ep = it;
            continue;
        }
        double frac = (double)(it - ep) / (double)EPOCH;
        double T = 1.5 * (1.0 - frac) + 0.08;
        Move mv;
        if (!propose(&mv)) continue;
        int old = g_cur;
        apply_move(&mv);
        int nbad = bad_pairs();
        int nc = nbad + deficit();
        if (nc <= old || rnd01() < exp(-(double)(nc - old) / T)) {
            g_cur = nc;
            g_bad = nbad;
            if (g_bad == 0) {
                record_best();
                if (n + 2 > MAXN - 2) break;
                grow();
                evaluate();
                ep = it;
            }
        } else {
            undo_move(&mv);
        }
    }

    if (hasValid) print_graph(bestN, bestM, BEU, BEV);
    else print_graph(initN, initM, IEU, IEV);
    return 0;
}
"""


# ---------------------------------------------------------------- algebraic bases

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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- extension helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
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
    """Greedily add vertices, each attached to a set cover of the current graph.

    A new vertex whose neighbours' radius-(D-1) balls cover everything is within D of all
    old vertices. Old distances only shrink, so the diameter bound is preserved.
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


def _extend_best(n, edges, d, D, rng, deadline, tries=EXTEND_TRIES):
    """Several randomized greedy extensions, keeping the largest result."""
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        cand = _extend(n, edges, d, D, rng, per)
        if cand[0] > best[0]:
            best = cand
    return best


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps distances and bipartiteness)."""
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


def _grow_alt(n, edges, d, D, rng, deadline):
    """Alternate spare-degree edge augmentation and greedy cover extension."""
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        _, e2 = _augment(n, edges, d, rng.randrange(1 << 30))
        n2, e3 = _extend(n, e2, d, D, rng, deadline)
        if n2 == n and len(e2) == len(edges):
            break
        n, edges = n2, e3
    return n, edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- Haar graphs

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


# ---------------------------------------------------------------- semidirect groups
#
# Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).
# Cyclic: k = 1. Dihedral-type: k = 2, r = m - 1.

def _presentations(M, rng, limit):
    """Random semidirect presentations (m, k, r) of groups of order M (k <= 8)."""
    out = []
    ks = [k for k in range(1, 9) if M % k == 0]
    rng.shuffle(ks)
    for k in ks:
        m = M // k
        if m == 1:
            out.append((1, k, 0))
        elif k == 1:
            out.append((m, 1, 1))
        else:
            cands = [m - 1] if k == 2 else []
            for _ in range(40):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append(r)
            if cands:
                out.append((m, k, rng.choice(cands)))
        if len(out) >= limit:
            break
    return out


class _Grp:
    """Semidirect group Z_m x|_r Z_k of order M = m*k with vectorised right multiplication."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.M = m * k
        self.powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        X = np.arange(self.M, dtype=np.int64)
        a, b = X // k, X % k
        nb = (-b) % k
        c = (-self.powers[nb] * a) % m
        self.inv = c * k + nb

    def mul(self, X, g):
        """Return X * g elementwise (X an array, g a scalar element)."""
        a1, b1 = X // self.k, X % self.k
        a2, b2 = g // self.k, g % self.k
        a = (a1 + self.powers[b1] * a2) % self.m
        b = (b1 + b2) % self.k
        return a * self.k + b


# ---------------------------------------------------------------- group lifts (annealing)

def _gcol(nbr, kk, sig, sinv, G, s, M, grp):
    """Fill neighbour column kk for every lift vertex.

    Left vertex (i, x) joins right (sig[kk,i], x*g); right (j, y) joins left (sinv[kk,j], y*g^-1).
    """
    Y = np.arange(M, dtype=np.int64)
    for i in range(s):
        j = int(sig[kk, i])
        nbr[i * M:(i + 1) * M, kk] = s * M + j * M + grp.mul(Y, int(G[kk, i]))
    for j in range(s):
        i = int(sinv[kk, j])
        gi = int(grp.inv[int(G[kk, i])])
        nbr[s * M + j * M: s * M + (j + 1) * M, kk] = i * M + grp.mul(Y, gi)


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff valid (fiber-transitive lifts)."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        Mx = R.copy()
        for k in range(nbr.shape[1]):
            Mx |= R[:, nbr[:, k]]
        if np.array_equal(Mx, R):
            break
        R = Mx
    return int(S * n - np.count_nonzero(R))


def _lift_anneal(s, M, grp, d, D, rng, deadline, iters):
    """Anneal darts of a group lift until diameter <= D. Returns neighbour table or None."""
    n = 2 * s * M
    sig = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    sinv = np.zeros_like(sig)
    for kk in range(d):
        for i in range(s):
            sinv[kk, sig[kk, i]] = i
    G = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    nbr = np.empty((n, d), dtype=np.int64)
    for kk in range(d):
        _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    sources = [i * M for i in range(s)] + [s * M + j * M for j in range(s)]
    cur = _cost(nbr, sources, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        if s == 1 or rng.random() < 0.6:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(G[kk, i])
            new = rng.randrange(M)
            if new == old:
                continue
            G[kk, i] = new
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                G[kk, i] = old
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(sig, sinv, kk, a, b)
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                _swap(sig, sinv, kk, a, b)
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    return nbr if cur == 0 else None


def _nbr_edges(nbr):
    """Deduplicated edge list from a neighbour table."""
    n, d = nbr.shape
    xs = np.repeat(np.arange(n, dtype=np.int64), d)
    ys = nbr.reshape(-1)
    lo = np.minimum(xs, ys)
    hi = np.maximum(xs, ys)
    keys = np.unique(lo * n + hi)
    return [(int(x // n), int(x % n)) for x in keys.tolist()]


def _lift_try(s, M, d, D, rng, deadline):
    """Try a few random presentations of order M. Returns edge list or None."""
    pres = _presentations(M, rng, 4)
    for _ in range(RETRIES):
        if time.monotonic() >= deadline:
            break
        m, k, r = rng.choice(pres)
        grp = _Grp(m, k, r)
        nbr = _lift_anneal(s, M, grp, d, D, rng, deadline, ITERS_G)
        if nbr is not None:
            return _nbr_edges(nbr)
    return None


def _lift_search(s, d, D, rng, deadline, cap):
    """Doubling then bisection over group order M for a fixed base size s. Returns (n, edges) or None."""
    best = None
    lo, hi = 0, None
    M = max(2, d)
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            if lo == 0:
                break
            hi = M
        else:
            edges = _lift_try(s, M, d, D, rng, deadline)
            if edges is not None:
                lo = M
                best = (2 * s * M, edges)
            elif lo == 0:
                M *= 2
                continue
            else:
                hi = M
        if hi is None:
            M = 2 * M
        else:
            if hi - lo <= max(1, lo // 16):
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- bi-Cayley graphs

def _group_tables(m, k, r):
    """Return (N, tab, invs): tab[s, x] = x * s, invs[s] = s^{-1}, for G = Z_m x|_r Z_k."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    pw_arr = np.array(pw, dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    A, B = X // k, X % k
    tab = np.empty((N, N), dtype=np.int32)
    invs = np.empty(N, dtype=np.int64)
    for s in range(N):
        c, dd = divmod(s, k)
        tab[s] = ((A + pw_arr[B] * c) % m) * k + (B + dd) % k
        nb = (-dd) % k
        na = (-pw[nb] * c) % m
        invs[s] = na * k + nb
    return N, tab, invs


def _uncovered(tab, invs, S, N, D):
    """Number of (source, vertex) pairs not within distance D, over sources (e, L) and (e, R)."""
    fwd = [tab[s] for s in S]
    bwd = [tab[invs[s]] for s in S]
    total = 0
    for src_side in (0, 1):
        visL = np.zeros(N, dtype=bool)
        visR = np.zeros(N, dtype=bool)
        if src_side == 0:
            visL[0] = True
            fL = np.array([0], dtype=np.int64)
            fR = np.empty(0, dtype=np.int64)
        else:
            visR[0] = True
            fR = np.array([0], dtype=np.int64)
            fL = np.empty(0, dtype=np.int64)
        for _ in range(D):
            nR = np.zeros(N, dtype=bool)
            for row in fwd:
                nR[row[fL]] = True
            nL = np.zeros(N, dtype=bool)
            for row in bwd:
                nL[row[fR]] = True
            nR &= ~visR
            nL &= ~visL
            visR |= nR
            visL |= nL
            fL = np.flatnonzero(nL)
            fR = np.flatnonzero(nR)
            if fL.size == 0 and fR.size == 0:
                break
        total += 2 * N - int(visL.sum()) - int(visR.sum())
    return total


def _anneal_bc(N, tab, invs, d, D, rng, budget_end):
    """Search a connection set S of size d with zero uncovered pairs. Returns S or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cur = _uncovered(tab, invs, S, N, D)
    start = time.monotonic()
    span = max(1e-3, budget_end - start)
    while cur > 0:
        now = time.monotonic()
        if now >= budget_end:
            break
        frac = (now - start) / span
        temp = 1.0 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        c = _uncovered(tab, invs, T, N, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = T, c
    return S if cur == 0 else None


def _bc_graph(N, tab, S):
    """Bi-Cayley graph: left x joined to right N + x*s for s in S."""
    edges = []
    for s in S:
        row = tab[s].tolist()
        for x in range(N):
            edges.append((x, N + row[x]))
    return 2 * N, edges


def _try_order(N, d, D, rng, end):
    """Try to realise a valid bi-Cayley graph of group order N over a few presentations."""
    pres = _presentations(N, rng, BC_GROUPS_PER_ORDER)
    for idx, (m, k, r) in enumerate(pres):
        now = time.monotonic()
        if now >= end:
            break
        per_end = now + (end - now) / (len(pres) - idx)
        _, tab, invs = _group_tables(m, k, r)
        S = _anneal_bc(N, tab, invs, d, D, rng, per_end)
        if S is not None:
            return _bc_graph(N, tab, S)
    return None


def _bicayley_best(d, D, seed, deadline):
    """Binary search over group orders for the largest order with a valid bi-Cayley graph."""
    moore = lib._moore_bound(d, D)
    N_hi = min(N_CAP // 2, moore // 2, BC_N_MAX)
    N_lo = max(d, N_hi // 3)
    if N_hi < N_lo or N_hi < d:
        return None
    rng = random.Random(seed * 1000003 + 17 * d + D)
    orders = list(range(N_lo, N_hi + 1))
    best = None
    lo, hi = 0, len(orders) - 1
    while lo <= hi and time.monotonic() < deadline - 0.2:
        mid = (lo + hi) // 2
        N = orders[mid]
        now = time.monotonic()
        budget_end = min(deadline, now + max(0.5, 0.25 * (deadline - now)))
        g = _try_order(N, d, D, rng, budget_end)
        if g is not None:
            if best is None or g[0] > best[0]:
                best = g
            lo = mid + 1
        else:
            hi = mid - 1
    return best


# ---------------------------------------------------------------- C refinement

def _c_refine(n, edges, d, D, seed, budget):
    """Run the C annealing engine from a valid start graph; return a strictly larger valid graph or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 20.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D, Moore-extremal
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    deadline = start + max(0.5, C_SPLIT * time_limit)
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    pool = [lib.haar_graph(d, range(d))]    # K_{d,d} fallback, always valid

    def add(c):
        if c is None:
            return
        pool.append(c)
        pool.sort(key=lambda item: -item[0])
        del pool[POOL_KEEP:]

    # Algebraic base: PG(2,q) for D = 3, W(q) for D >= 4 (both Moore-extremal shortcuts).
    pg = _pg_base(d) if D == 3 else None
    gq = _best_gq(d) if D >= 4 else None
    if D == 3 and pg is not None and lib.is_prime_power(d - 1):
        return _finish([pg], d, D)
    if D == 4 and gq is not None and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
        return _finish([gq], d, D)

    base = pg if D == 3 else gq
    if base is not None:
        add(base)
        alg_end = min(deadline, time.monotonic() + 0.15 * (deadline - start))
        aug = _augment(base[0], base[1], d, seed)
        add(aug)
        for h in (base, aug):
            now = time.monotonic()
            if now >= alg_end:
                break
            add(_extend_best(h[0], h[1], d, D, rng, min(alg_end, now + EXTEND_SLICE)))
        now = time.monotonic()
        if now < alg_end:
            add(_grow_alt(aug[0], aug[1], d, D, rng, min(alg_end, now + EXTEND_SLICE)))

    # Haar graphs with growing modulus.
    now = time.monotonic()
    haar_end = now + HAAR_FRAC * max(0.0, deadline - now)
    haar_m, haar_miss, haar_best = d + 1, 0, None
    while time.monotonic() < haar_end and haar_miss < 4 and 2 * haar_m <= cap:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    add(haar_best)

    # Bi-Cayley graphs over semidirect groups (weak regime D >= 4, d >= 4).
    if d >= 4 and D >= 4:
        now = time.monotonic()
        bc_end = now + BC_FRAC * max(0.0, deadline - now)
        try:
            add(_bicayley_best(d, D, seed, bc_end))
        except Exception:
            pass

    # Cyclic, dihedral and semidirect group lifts, one slice per base size.
    post_reserve = POST_FRAC * max(0.0, deadline - start)
    lift_end = deadline - post_reserve
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= lift_end:
            break
        slice_end = now + (lift_end - now) / (len(S_LIST) - idx)
        try:
            add(_lift_search(s, d, D, rng, slice_end, cap))
        except Exception:
            pass

    # Post-processing: fill spare degree of the best candidate.
    if pool:
        top = pool[0]
        try:
            add(_extend_best(top[0], top[1], d, D, rng, deadline, tries=2))
        except Exception:
            pass

    try:
        base_best = _finish(pool, d, D)
    except Exception:
        base_best = lib.haar_graph(d, range(d))

    # Deficit-penalised vertex-insertion annealing in C, started from the best valid graph.
    if base_best[0] >= lib._moore_bound(d, D) or base_best[0] > C_MAX_N:
        return base_best
    left = start + C_END * time_limit - time.monotonic() - 2.0
    if left >= 2.0:
        res = _c_refine(base_best[0], base_best[1], d, D, seed, left)
        if res is not None:
            return res
    return base_best
