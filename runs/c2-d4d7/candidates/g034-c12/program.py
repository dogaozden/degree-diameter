"""Bold variant for the weakest target (d=4, D=7): bi-Cayley and voltage lifts over explicit groups.

Change from the parent: the C engine no longer searches only metacyclic groups Z_m x| Z_k. Python builds
multiplication tables for non-metacyclic groups (PSL(2,q), PGL(2,q) for q in {5,7,8,9,11}, S4, A5, S5, S6,
direct products of these with Z_k, and random semidirect products). Each table is sent to C as a compact
generator description: a BFS tree over right multiplications, with one row per generator. The C engine
rebuilds the full table, then runs a simulated-annealing search over base multigraphs on p <= 4 fibres per
side and voltage assignments in that group. The diameter test is orbit-reduced (BFS from the 2p fibre
identities), and every accepted lift is re-checked by a full all-sources BFS in C. Python checks each result
again with lib.is_valid. Each group gets a short time slice, and the best valid graph seen so far is returned.
Fallbacks: the start graph (the best known construction, including the H(3) hexagon graph for d=4, D>=6) is
returned whenever no lift beats it. The calibration case returns immediately when it already meets the Moore bound.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

_MAXP = 4
_MAXGEN = 16

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXG 1200
#define MAXGEN 16
#define MAXP 4
#define STEPS 25000
#define KICK 2500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

typedef struct { int i, j, g; } Dart;

static int d, D, GN;
static int best_n;
static int found;
static double t_end;
static int GT[MAXG * MAXG];
static Graph bestg, work;
static int dist_buf[MAXN], queue_buf[MAXN];
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void add_edge(Graph *g, int u, int v) {
    if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return;
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* A-fibre i, element x -> i*N + x.  B-fibre j, element y -> (p+j)*N + y.
 * Dart (i, j, g) joins A(i,x) to B(j, x*g) for every x. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

/* Random d-regular bipartite multigraph on p + p fibres, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) {
                    seen[u] = 1;
                    nseen++;
                    stack[top++] = u;
                }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* A voltage distinct from the other darts on the same fibre pair (i, j). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

/* BFS from src up to depth D; returns the number of vertices reached (including src). */
static int bfs_reach(const Graph *g, int src) {
    int nv = g->n, head = 0, tail = 0;
    for (int v = 0; v < nv; v++) dist_buf[v] = -1;
    dist_buf[src] = 0;
    queue_buf[tail++] = src;
    while (head < tail) {
        int v = queue_buf[head++];
        if (dist_buf[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (dist_buf[u] < 0) {
                dist_buf[u] = dist_buf[v] + 1;
                queue_buf[tail++] = u;
            }
        }
    }
    return tail;
}

/* Orbit-reduced objective: the left action of GN on each fibre is an automorphism group acting
 * regularly, so the fibre identities are enough sources. Returns the number of unreached pairs. */
static long orbit_bad(const Graph *g, int p) {
    long total = 0;
    for (int s = 0; s < 2 * p; s++)
        total += g->n - bfs_reach(g, s * GN);
    return total;
}

static int full_ok(const Graph *g) {
    for (int v = 0; v < g->n; v++)
        if (bfs_reach(g, v) != g->n) return 0;
    return 1;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* Input: "N M" then M pairs. The first N-1 pairs are (parent, generator) for elements 1..N-1
 * in BFS order, where element g = parent * gen[k]. Then for each generator k, N pairs (k, x*gen_k).
 * Builds GT[x*N+g] = x*g. */
static int read_group(void) {
    int m;
    if (scanf("%d %d", &GN, &m) != 2) return 0;
    if (GN < 2 || GN > MAXG) return 0;
    int rest = m - (GN - 1);
    if (rest <= 0 || rest % GN) return 0;
    int G = rest / GN;
    if (G < 1 || G > MAXGEN) return 0;
    static int par[MAXG], gk[MAXG];
    static int R[MAXGEN][MAXG];
    for (int g = 1; g < GN; g++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= g || v < 0 || v >= G) return 0;
        par[g] = u;
        gk[g] = v;
    }
    for (int k = 0; k < G; k++)
        for (int x = 0; x < GN; x++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) return 0;
            if (u != k || v < 0 || v >= GN) return 0;
            R[k][x] = v;
        }
    for (int x = 0; x < GN; x++) GT[x * GN] = x;
    for (int g = 1; g < GN; g++)
        for (int x = 0; x < GN; x++)
            GT[x * GN + g] = R[gk[g]][GT[x * GN + par[g]]];
    return 1;
}

static void make_fibre_darts(int p, Dart *dt, int *ndp) {
    int M[MAXP][MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j);
                nd++;
            }
    *ndp = nd;
}

/* One annealing attempt on a random base multigraph over the current group. */
static void attempt(int p, double until) {
    Dart dt[MAXD * MAXP], bestdt[MAXD * MAXP];
    int nd = 0;
    make_fibre_darts(p, dt, &nd);
    double T = 1.0 + 2.0 * rnd01();
    build_lift(&work, p, dt, nd);
    long bad = orbit_bad(&work, p);
    long bestbad = bad;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    int stall = 0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j);
        build_lift(&work, p, dt, nd);
        long nb = orbit_bad(&work, p);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T))
            bad = nb;
        else
            dt[t].g = old;
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(bestdt, dt, sizeof(Dart) * nd);
            stall = 0;
        } else if (++stall > KICK) {
            memcpy(dt, bestdt, sizeof(Dart) * nd);
            for (int k = 0; k < 2; k++) {
                int u = rndint(nd);
                dt[u].g = fresh_voltage(dt, nd, u, dt[u].i, dt[u].j);
            }
            build_lift(&work, p, dt, nd);
            bad = orbit_bad(&work, p);
            stall = 0;
        }
    }
    if (bestbad == 0) {
        memcpy(dt, bestdt, sizeof(Dart) * nd);
        build_lift(&work, p, dt, nd);
        if (work.n > best_n && full_ok(&work)) {
            bestg = work;
            best_n = work.n;
            found = 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit best_n < group\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    best_n = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    found = 0;
    if (d < 2 || d > MAXD || D < 2 || !read_group() || GN <= d) {
        printf("0 0\n");
        return 0;
    }
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    while (now() < t_end) {
        int feas[MAXP], nf = 0;
        for (int p = 1; p <= MAXP; p++) {
            long v = 2L * p * GN;
            if (v > best_n && v <= cap) feas[nf++] = p;
        }
        if (nf == 0) break;
        int p = feas[rndint(nf)];
        double until = now() + 1.5;
        if (until > t_end) until = t_end;
        attempt(p, until);
    }
    if (found)
        print_graph(&bestg);
    else
        printf("0 0\n");
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6."""
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


# ------------------------------------------------------------ group construction

def _closure(gens, cap):
    """Elements of the permutation group generated by gens (tuples), identity first; None if above cap."""
    deg = len(gens[0])
    ident = tuple(range(deg))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        e = elems[i]
        i += 1
        for s in gens:
            h = tuple(e[x] for x in s)  # e o s
            if h not in index:
                if len(elems) >= cap:
                    return None
                index[h] = len(elems)
                elems.append(h)
    return elems


def _table_from_perms(elems):
    """Multiplication table T[i, j] = index of elems[i] o elems[j]."""
    N = len(elems)
    E = np.array(elems, dtype=np.int64)
    w = 16 ** np.arange(E.shape[1], dtype=np.int64)
    keys = E @ w
    order = np.argsort(keys)
    sk = keys[order]
    T = np.empty((N, N), dtype=np.int64)
    for j in range(N):
        ck = E[:, E[j]] @ w
        pos = np.minimum(np.searchsorted(sk, ck), N - 1)
        if not np.array_equal(sk[pos], ck):
            raise ValueError("closure is not closed")
        T[:, j] = order[pos]
    return T


def _pgl_gens(q, pgl):
    """Generators of PSL(2,q) (pgl False) or PGL(2,q) acting on the projective line {0..q-1, inf=q}."""
    F = lib.GF(q)
    inf = q

    def t(x):
        return inf if x == inf else F.add(x, 1)

    def s(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return F.neg(F.inv(x))

    gens = [tuple(t(x) for x in range(q + 1)), tuple(s(x) for x in range(q + 1))]
    if pgl:
        g = F.primitive_element()
        gens.append(tuple(inf if x == inf else F.mul(g, x) for x in range(q + 1)))
    return gens


def _sym_gens(n):
    t = list(range(n))
    t[0], t[1] = 1, 0
    c = tuple((x + 1) % n for x in range(n))
    return [tuple(t), c]


def _alt_gens(n):
    c3 = tuple([1, 2, 0] + list(range(3, n)))
    cn = tuple((x + 1) % n for x in range(n))
    return [c3, cn]


def _base_tables():
    specs = []
    for q in (5, 7, 8, 9, 11):
        specs.append((f"PSL(2,{q})", _pgl_gens(q, False)))
        specs.append((f"PGL(2,{q})", _pgl_gens(q, True)))
    specs.append(("S4", _sym_gens(4)))
    specs.append(("A5", _alt_gens(5)))
    specs.append(("S5", _sym_gens(5)))
    specs.append(("S6", _sym_gens(6)))
    out = []
    for name, gens in specs:
        elems = _closure(gens, 1100)
        if elems is None or len(elems) < 4:
            continue
        out.append((name, _table_from_perms(elems)))
    return out


def _product_table(T0, k):
    """Direct product with Z_k; element (x, c) has index x*k + c."""
    o = T0.shape[0]
    a = np.arange(k)
    addk = (a[:, None] + a[None, :]) % k
    P = T0[:, None, :, None] * k + addk[None, :, None, :]
    return P.reshape(o * k, o * k)


def _semidirect_table(m, k, r):
    """Z_m x|_r Z_k; element a*k + b, (a,b)(c,e) = (a + r^b c, b + e)."""
    rp = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(m * k, dtype=np.int64)
    a, b = x // k, x % k
    A = a[:, None]
    B = b[:, None]
    Cc = a[None, :]
    Ee = b[None, :]
    return ((A + rp[B] * Cc) % m) * k + (B + Ee) % k


def _candidates(seed, lo, hi, tables):
    """Candidate groups as (order, name, T0, k, semidirect params)."""
    out = []
    for name, T0 in tables:
        o = T0.shape[0]
        for k in range(1, hi // o + 1):
            N = o * k
            if lo <= N <= hi:
                out.append((N, f"{name}xZ{k}", T0, k, None))
    rs = random.Random(seed * 7919 + 13)
    for _ in range(80):
        N = rs.randint(lo, hi)
        ms = [m for m in range(3, N) if N % m == 0 and N // m >= 2]
        if not ms:
            continue
        m = rs.choice(ms)
        k = N // m
        rr = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if not rr:
            continue
        r = rs.choice(rr)
        out.append((N, f"Z{m}:{r}Z{k}", None, None, (m, k, r)))
    return out


def _make_table(cand):
    N, name, T0, k, sd = cand
    if T0 is not None:
        return T0 if k == 1 else _product_table(T0, k)
    m, kk, r = sd
    return _semidirect_table(m, kk, r)


def _bfs(T, gens):
    N = T.shape[0]
    seen = [False] * N
    seen[0] = True
    order = [0]
    par = [-1] * N
    gk = [-1] * N
    i = 0
    while i < len(order):
        x = order[i]
        i += 1
        for k, s in enumerate(gens):
            y = int(T[x, s])
            if not seen[y]:
                seen[y] = True
                par[y] = x
                gk[y] = k
                order.append(y)
    return order, par, gk


def _structure(T):
    """Relabel T in BFS order from generators; return (N, pairs) for the C engine, or None."""
    N = T.shape[0]
    gens = []
    order, par, gk = _bfs(T, gens)
    while len(order) < N:
        if len(gens) >= _MAXGEN:
            return None
        inset = set(order)
        x = next(y for y in range(N) if y not in inset)
        gens.append(x)
        order, par, gk = _bfs(T, gens)
    pos = np.empty(N, dtype=np.int64)
    pos[np.array(order, dtype=np.int64)] = np.arange(N)
    T2 = pos[T[np.ix_(order, order)]]
    par2 = [0] * N
    gk2 = [0] * N
    for i in range(1, N):
        old = order[i]
        par2[i] = int(pos[par[old]])
        gk2[i] = gk[old]
    gnew = [int(pos[g]) for g in gens]
    pairs = [(par2[i], gk2[i]) for i in range(1, N)]
    for k in range(len(gens)):
        col = T2[:, gnew[k]]
        pairs += [(k, int(v)) for v in col.tolist()]
    return N, pairs


# ------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d < 3 or d > 31 or D < 2 or best[0] >= moore:
        return best

    deadline = t0 + 0.92 * time_limit - 1.5
    lo = max(d + 1, best[0] // (2 * _MAXP) + 1)
    hi = moore // 2
    if hi < lo:
        return best

    try:
        tables = _base_tables()
        cands = _candidates(seed, lo, hi, tables)
    except Exception:
        return best
    random.Random(seed).shuffle(cands)

    for cand in cands:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_t = min(3.0, remaining - 1.0)
        try:
            st = _structure(_make_table(cand))
            if st is None:
                continue
            N, pairs = st
            text = lib.run_c(C_SOURCE, [d, D, seed, round(slice_t, 2), best[0]],
                             stdin_graph=(N, pairs), timeout=slice_t + 10)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            continue
    return best
