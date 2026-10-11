import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS_G = 1200                # annealing moves per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing attempts per lift order
TIME_FRAC = 0.8               # fraction of time_limit used overall
EXTEND_SLICE = 0.5            # seconds per greedy extension run
EXTEND_TRIES = 6              # randomized greedy restarts per base graph
POOL_KEEP = 8                 # candidates kept in the pool
BC_N_MAX = 1600               # largest group order searched for bi-Cayley graphs
BC_GROUPS_PER_ORDER = 3       # semidirect presentations tried per group order
BC_FRAC = 0.3                 # share of remaining time for bi-Cayley search (D >= 4, d >= 4)
HAAR_FRAC = 0.1               # share of remaining time for Haar search
POST_FRAC = 0.1               # share of total working time reserved for final extension

BASE_SHARE = 0.5              # share of time_limit given to the algebraic/lift pipeline
C_MARGIN = 2.5                # seconds reserved for compiling and wrap-up
C_INNER = 0.9                 # the C engine stops at this fraction of its budget
MULTI_K = 3                   # NEW: insertion-annealing runs on the top-K distinct candidates
MULTI_MIN_RUN = 3.0           # NEW: minimum seconds per C run


# ---------------------------------------------------------------- C local search engine
#
# Starts from a valid graph, inserts a pair of vertices (w in side 0, z in side 1) by
# splicing them into d-1 disjoint edges (degrees are preserved), then anneals with
# degree-preserving 2-switches on the number of pairs at distance > D. Every stored
# snapshot is valid, so the output is always valid when non-empty.

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1216
#define WORDS 19
#define MAXD 32

typedef uint64_t u64;

static int d, D, n;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static int SADJ[MAXN][MAXD];
static int SDEG[MAXN];
static int SN = 0;
static int have_snap = 0;
static u64 RA[MAXN][WORDS];
static u64 RB[MAXN][WORDS];
static u64 rng_state = 88172645463325252ULL;
static unsigned used[MAXN];
static unsigned stamp_ctr = 1;
static double t_budget = 1.0;
static clock_t t_begin;
static long cur = 0;
static int Q[MAXN];

static double elapsed(void) {
    return (double)(clock() - t_begin) / (double)CLOCKS_PER_SEC;
}

static u64 rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static unsigned rnd(unsigned m) {
    return (unsigned)(rnd64() % (u64)m);
}

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(u64 x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int slot(int v, int u) {
    int k;
    for (k = 0; k < deg[v]; k++) if (adj[v][k] == u) return k;
    return -1;
}

/* Edges (a,b),(c,e) become (a,e),(c,b). Calling it again with (a,e,c,b) undoes it. */
static void do_switch(int a, int b, int c, int e) {
    adj[a][slot(a, b)] = e;
    adj[c][slot(c, e)] = b;
    adj[e][slot(e, c)] = a;
    adj[b][slot(b, a)] = c;
}

/* Number of ordered pairs (v,u) with dist(v,u) > D. Zero iff valid. */
static long cost_fn(void) {
    int W = (n + 63) / 64;
    int v, r, w, k, changed;
    long bad = 0;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < D; r++) {
        changed = 0;
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) {
                u64 x = RA[v][w];
                for (k = 0; k < deg[v]; k++) x |= RA[adj[v][k]][w];
                RB[v][w] = x;
                if (x != RA[v][w]) changed = 1;
            }
        }
        if (!changed) break;
        for (v = 0; v < n; v++)
            for (w = 0; w < W; w++) RA[v][w] = RB[v][w];
    }
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc(RA[v][w]);
        bad += n - c;
    }
    return bad;
}

static void anneal(long steps_max, double T0) {
    long s;
    for (s = 0; s < steps_max && cur > 0; s++) {
        int a = -1, c = -1, t, b, e;
        double frac, T;
        long nc;
        if ((s & 127) == 0 && elapsed() > t_budget) break;
        frac = (double)s / (double)steps_max;
        T = T0 * (1.0 - frac) + 0.05;
        for (t = 0; t < 1000; t++) {
            int x = (int)rnd((unsigned)n);
            if (col[x] == 0 && deg[x] > 0) { a = x; break; }
        }
        if (a < 0) break;
        for (t = 0; t < 1000; t++) {
            int x = (int)rnd((unsigned)n);
            if (col[x] == 0 && deg[x] > 0 && x != a) { c = x; break; }
        }
        if (c < 0) break;
        b = adj[a][rnd((unsigned)deg[a])];
        e = adj[c][rnd((unsigned)deg[c])];
        if (b == e) continue;
        if (slot(a, e) >= 0 || slot(c, b) >= 0) continue;
        do_switch(a, b, c, e);
        nc = cost_fn();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            do_switch(a, e, c, b);
        }
    }
}

/* Replace d-1 disjoint edges (a_i,b_i) by a_i-z, b_i-w, and add w-z. Degrees are kept. */
static int insert_pair(void) {
    int A[MAXD], B[MAXD];
    int cnt = 0, tries = 0, i;
    int w, z;
    if (n + 2 > MAXN || d < 2) return 0;
    stamp_ctr++;
    while (cnt < d - 1 && tries < 5000) {
        int a, b;
        tries++;
        a = (int)rnd((unsigned)n);
        if (col[a] != 0 || deg[a] == 0) continue;
        b = adj[a][rnd((unsigned)deg[a])];
        if (used[a] == stamp_ctr || used[b] == stamp_ctr) continue;
        used[a] = stamp_ctr;
        used[b] = stamp_ctr;
        A[cnt] = a;
        B[cnt] = b;
        cnt++;
    }
    if (cnt < d - 1) return 0;
    w = n;
    z = n + 1;
    col[w] = 0;
    col[z] = 1;
    for (i = 0; i < cnt; i++) {
        adj[A[i]][slot(A[i], B[i])] = z;
        adj[B[i]][slot(B[i], A[i])] = w;
        adj[z][i] = A[i];
        adj[w][i] = B[i];
    }
    adj[w][d - 1] = z;
    adj[z][d - 1] = w;
    deg[w] = d;
    deg[z] = d;
    n += 2;
    return 1;
}

static void greedy_fill(void) {
    int a, b;
    for (a = 0; a < n; a++) {
        if (col[a] != 0) continue;
        for (b = 0; b < n; b++) {
            if (col[b] != 1) continue;
            if (deg[a] < d && deg[b] < d && slot(a, b) < 0) {
                adj[a][deg[a]++] = b;
                adj[b][deg[b]++] = a;
            }
        }
    }
}

static void save_snap(void) {
    int v, k;
    SN = n;
    for (v = 0; v < n; v++) {
        SDEG[v] = deg[v];
        for (k = 0; k < deg[v]; k++) SADJ[v][k] = adj[v][k];
    }
    have_snap = 1;
}

static void restore_snap(void) {
    int v, k;
    n = SN;
    for (v = 0; v < n; v++) {
        deg[v] = SDEG[v];
        for (k = 0; k < deg[v]; k++) adj[v][k] = SADJ[v][k];
    }
}

static void print_state(int nn, int ad[][MAXD], const int *dg) {
    long m = 0;
    int v, k;
    for (v = 0; v < nn; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", nn, m);
    for (v = 0; v < nn; v++)
        for (k = 0; k < dg[v]; k++)
            if (ad[v][k] > v) printf("%d %d\n", v, ad[v][k]);
}

int main(int argc, char **argv) {
    int m, i, u, v, s;
    double budget;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rng_state ^= (u64)strtoull(argv[3], NULL, 10) * 2654435761ULL + 12345ULL;
    if (rng_state == 0) rng_state = 1;
    budget = atof(argv[4]);
    t_budget = budget * C_INNER_SCALE_PLACEHOLDER;
    t_begin = clock();

    if (d < 2 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        if (deg[u] >= d || deg[v] >= d || slot(u, v) >= 0) { printf("0 0\n"); return 0; }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (i = 0; i < n; i++) col[i] = -1;
    for (s = 0; s < n; s++) {
        int qh = 0, qt = 0, k;
        if (col[s] >= 0) continue;
        col[s] = 0;
        Q[qt++] = s;
        while (qh < qt) {
            int x = Q[qh++];
            for (k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    Q[qt++] = y;
                }
            }
        }
    }
    for (v = 0; v < n; v++)
        for (i = 0; i < deg[v]; i++)
            if (col[adj[v][i]] == col[v]) { printf("0 0\n"); return 0; }

    greedy_fill();
    cur = cost_fn();
    if (cur == 0) save_snap();

    {
        long fails = 0;
        const long K0 = 6000;
        while (elapsed() < t_budget) {
            long K;
            if (have_snap) {
                if (!insert_pair()) break;
                cur = cost_fn();
            }
            K = K0 + 200 * fails;
            if (K > 60000) K = 60000;
            anneal(K, 2.0);
            if (cur == 0) {
                save_snap();
                fails = 0;
            } else if (have_snap) {
                restore_snap();
                cur = 0;
                fails++;
            }
        }
    }
    if (have_snap) print_state(SN, SADJ, SDEG);
    else printf("0 0\n");
    return 0;
}
'''.replace("C_INNER_SCALE_PLACEHOLDER", "0.9")


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


def _finish_list(cands, d, D, k=MULTI_K):
    """NEW: return up to k largest candidates that pass lib.is_valid (K_{d,d} if none)."""
    out = []
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            out.append((n, e))
            if len(out) >= k:
                break
    if not out:
        out.append(lib.haar_graph(d, range(d)))
    return out


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


# ---------------------------------------------------------------- algebraic / lift pipeline
#
# _base_build returns a LIST of up to MULTI_K valid candidates (largest first), so the
# C insertion search can be run from several distinct starting graphs.

def _base_build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return [(1, [])]
    if d == 1 or D == 1:
        return [(2, [(0, 1)])]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D, Moore-extremal
        return [(L, [(i, (i + 1) % L) for i in range(L)])]
    if D == 2:
        return [lib.haar_graph(d, range(d))]  # K_{d,d} is extremal for D = 2

    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
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
        return _finish_list([pg], d, D)
    if D == 4 and gq is not None and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
        return _finish_list([gq], d, D)

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
        return _finish_list(pool, d, D)
    except Exception:
        return [lib.haar_graph(d, range(d))]


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    safe = lib.haar_graph(d, range(d)) if d >= 1 else (1, [])

    try:
        cands = _base_build(d, D, seed, BASE_SHARE * time_limit)
    except Exception:
        cands = [safe]
    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    if not valid:
        valid = [safe]
    valid.sort(key=lambda c: -c[0])
    best = valid[0]

    # NEW: multi-start insertion annealing. The C engine runs from the top distinct
    # candidates in turn, with the remaining time split evenly among the runs.
    if d >= 3 and D >= 4 and best[0] > 0:
        elapsed = time.monotonic() - t0
        total = C_INNER * (0.9 * time_limit - elapsed - C_MARGIN)
        runs = min(MULTI_K, len(valid), int(total // MULTI_MIN_RUN))
        if runs >= 1 and total >= 2.0:
            per = total / runs
            for i in range(runs):
                cand = valid[i]
                if cand[0] <= 0:
                    continue
                try:
                    text = lib.run_c(C_SOURCE, [d, D, seed + i, round(per, 2)],
                                     stdin_graph=cand, timeout=per + 4.0)
                    n2, e2 = lib.parse_graph_text(text)
                    if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                        best = (n2, e2)
                except Exception:
                    pass

    return best
