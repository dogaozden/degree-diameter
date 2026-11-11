import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (first stage).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Second stage (new construction family): a C annealer that grows a valid
# bipartite graph by two vertices at a time. Each candidate state is judged
# by the number of vertex pairs at distance > D (bitset BFS). Moves are
# degree-preserving endpoint shifts and 2-switches, plus edge additions
# between spare vertices. Every accepted state keeps max degree <= d and is
# bipartite. The best valid state is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int d_, D_, n_, cap_, W_;
static int *deg_, *nb_, *col_, *spA_, *spB_;
static uint64_t *adj_, *R0_, *R1_;
static int *bdeg_, *bcol_, *bnb_, bn_;
static uint64_t *badj_;
static uint64_t rs_ = 88172645463325252ULL;
static clock_t T_START;
static double T_LIMIT;

static uint64_t rnd64(void) {
    rs_ ^= rs_ >> 12; rs_ ^= rs_ << 25; rs_ ^= rs_ >> 27;
    return rs_ * 2685821657736338717ULL;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) {
    return (double)(clock() - T_START) / CLOCKS_PER_SEC >= T_LIMIT;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    return (int)((adj_[(size_t)a * W_ + (b >> 6)] >> (b & 63)) & 1ULL);
}
static void set_bit(int a, int b, int on) {
    uint64_t *p = &adj_[(size_t)a * W_ + (b >> 6)];
    if (on) *p |= 1ULL << (b & 63);
    else *p &= ~(1ULL << (b & 63));
}
static void del_nb(int a, int b) {
    int *L = nb_ + (size_t)a * d_;
    for (int k = 0; k < deg_[a]; k++) {
        if (L[k] == b) { L[k] = L[--deg_[a]]; return; }
    }
}
static void add_edge(int a, int b) {
    nb_[(size_t)a * d_ + deg_[a]++] = b;
    nb_[(size_t)b * d_ + deg_[b]++] = a;
    set_bit(a, b, 1);
    set_bit(b, a, 1);
}
static void remove_edge(int a, int b) {
    del_nb(a, b);
    del_nb(b, a);
    set_bit(a, b, 0);
    set_bit(b, a, 0);
}

/* Number of unordered pairs at distance > D_ (including unreachable pairs). */
static long long cost_eval(void) {
    int W = (n_ + 63) >> 6;
    for (int v = 0; v < n_; v++) {
        uint64_t *r = R0_ + (size_t)v * W_;
        memset(r, 0, sizeof(uint64_t) * (size_t)W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D_; it++) {
        for (int v = 0; v < n_; v++) {
            uint64_t *o = R1_ + (size_t)v * W_;
            memcpy(o, R0_ + (size_t)v * W_, sizeof(uint64_t) * (size_t)W);
            const int *L = nb_ + (size_t)v * d_;
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *ru = R0_ + (size_t)L[k] * W_;
                for (int w = 0; w < W; w++) o[w] |= ru[w];
            }
        }
        uint64_t *t = R0_; R0_ = R1_; R1_ = t;
    }
    long long bad = 0;
    for (int v = 0; v < n_; v++) {
        const uint64_t *r = R0_ + (size_t)v * W_;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        bad += n_ - c;
    }
    return bad / 2;
}

/* Anneal the current state for at most maxit iterations. Returns its final cost. */
static long long anneal(long long maxit) {
    long long cost = cost_eval();
    const double T0 = 3.0, T1 = 0.1;
    for (long long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);

        int na = 0, nbb = 0;
        for (int v = 0; v < n_; v++) {
            if (deg_[v] < d_) {
                if (col_[v] == 0) spA_[na++] = v;
                else spB_[nbb++] = v;
            }
        }

        /* Add an edge between non-adjacent spare vertices of opposite sides. */
        if (na > 0 && nbb > 0) {
            int done = 0;
            for (int t = 0; t < 30 && !done; t++) {
                int a = spA_[rndint(na)], b = spB_[rndint(nbb)];
                if (!has_edge(a, b)) { add_edge(a, b); done = 1; }
            }
            if (done) { cost = cost_eval(); continue; }
        }

        int total = na + nbb;
        if (total > 0 && rnd01() < 0.6) {
            int s = (rndint(total) < na) ? spA_[rndint(na)] : spB_[rndint(nbb)];
            int sc = col_[s], x = -1, y = -1, moved = 0;
            for (int t = 0; t < 60 && !moved; t++) {
                int xx = rndint(n_);
                if (col_[xx] != sc || deg_[xx] == 0) continue;
                int yy = nb_[(size_t)xx * d_ + rndint(deg_[xx])];
                if (has_edge(s, yy)) continue;
                x = xx; y = yy; moved = 1;
            }
            if (moved) {
                /* Endpoint shift: (x,y) becomes (s,y); x becomes spare. */
                remove_edge(x, y);
                add_edge(s, y);
                long long nc = cost_eval();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
                else { remove_edge(s, y); add_edge(x, y); }
                continue;
            }
        }

        /* Degree-preserving 2-switch on side A. */
        {
            int moved = 0;
            for (int t = 0; t < 60 && !moved; t++) {
                int a = rndint(n_);
                if (col_[a] != 0 || deg_[a] == 0) continue;
                int b = nb_[(size_t)a * d_ + rndint(deg_[a])];
                int c = rndint(n_);
                if (col_[c] != 0 || deg_[c] == 0 || c == a) continue;
                int e = nb_[(size_t)c * d_ + rndint(deg_[c])];
                if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
                remove_edge(a, b);
                remove_edge(c, e);
                add_edge(a, e);
                add_edge(c, b);
                long long nc = cost_eval();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
                else {
                    remove_edge(a, e);
                    remove_edge(c, b);
                    add_edge(a, b);
                    add_edge(c, e);
                }
                moved = 1;
            }
        }
    }
    return cost;
}

static void save_state(void) {
    bn_ = n_;
    memcpy(bdeg_, deg_, sizeof(int) * (size_t)cap_);
    memcpy(bcol_, col_, sizeof(int) * (size_t)cap_);
    memcpy(bnb_, nb_, sizeof(int) * (size_t)cap_ * d_);
    memcpy(badj_, adj_, sizeof(uint64_t) * (size_t)cap_ * W_);
}

static void load_state(void) {
    n_ = bn_;
    memcpy(deg_, bdeg_, sizeof(int) * (size_t)cap_);
    memcpy(col_, bcol_, sizeof(int) * (size_t)cap_);
    memcpy(nb_, bnb_, sizeof(int) * (size_t)cap_ * d_);
    memcpy(adj_, badj_, sizeof(uint64_t) * (size_t)cap_ * W_);
}

static void print_state(void) {
    long long m = 0;
    for (int v = 0; v < n_; v++)
        for (int k = 0; k < deg_[v]; k++)
            if (nb_[(size_t)v * d_ + k] > v) m++;
    printf("%d %lld\n", n_, m);
    for (int v = 0; v < n_; v++)
        for (int k = 0; k < deg_[v]; k++) {
            int u = nb_[(size_t)v * d_ + k];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    T_LIMIT = atof(argv[4]);
    T_START = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || d_ < 1) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m0 = i; break; }
    }

    cap_ = n0 + 600;
    W_ = (cap_ + 63) >> 6;
    deg_ = calloc((size_t)cap_, sizeof(int));
    col_ = calloc((size_t)cap_, sizeof(int));
    nb_ = calloc((size_t)cap_ * d_, sizeof(int));
    adj_ = calloc((size_t)cap_ * W_, sizeof(uint64_t));
    R0_ = calloc((size_t)cap_ * W_, sizeof(uint64_t));
    R1_ = calloc((size_t)cap_ * W_, sizeof(uint64_t));
    spA_ = calloc((size_t)cap_, sizeof(int));
    spB_ = calloc((size_t)cap_, sizeof(int));
    bdeg_ = calloc((size_t)cap_, sizeof(int));
    bcol_ = calloc((size_t)cap_, sizeof(int));
    bnb_ = calloc((size_t)cap_ * d_, sizeof(int));
    badj_ = calloc((size_t)cap_ * W_, sizeof(uint64_t));

    n_ = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < n_; v++) col_[v] = -1;
    int *q = spA_;
    int bip = 1;
    for (int s = 0; s < n_ && bip; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t && bip) {
            int u = q[h++];
            for (int k = 0; k < deg_[u]; k++) {
                int w = nb_[(size_t)u * d_ + k];
                if (col_[w] == -1) { col_[w] = 1 - col_[u]; q[t++] = w; }
                else if (col_[w] == col_[u]) { bip = 0; break; }
            }
        }
    }
    if (!bip) { print_state(); return 0; }

    if (cost_eval() != 0) { print_state(); return 0; }
    save_state();

    while (!timeup()) {
        if (n_ + 2 > cap_) break;
        int a = n_, b = n_ + 1;
        n_ += 2;
        deg_[a] = 0;
        deg_[b] = 0;
        col_[a] = 0;
        col_[b] = 1;
        memset(adj_ + (size_t)a * W_, 0, sizeof(uint64_t) * (size_t)W_);
        memset(adj_ + (size_t)b * W_, 0, sizeof(uint64_t) * (size_t)W_);
        long long c = anneal(2500);
        if (c == 0) save_state();
        else load_state();
    }
    load_state();
    print_state();
    return 0;
}
'''


def _c_stage(d, D, seed, graph, c_budget):
    """Run the C annealer on graph for about c_budget seconds; returns (n, edges) or None."""
    n, edges = graph
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                        stdin_graph=(n, edges), timeout=c_budget + 20.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    lift_budget = max(1.0, min(0.4 * time_limit, time_limit - 6.0))
    deadline = start + lift_budget

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: bi-Cayley lift search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Short slack extension of the current best.
    n2, e2 = _slack_extend(best[0], best[1], d, D, rng, time.monotonic() + 2.0)
    consider(n2, e2)

    # Stage 2: C annealer grows the best graph by two vertices at a time.
    if D >= 3:
        c_budget = time_limit - (time.monotonic() - start) - 8.0
        if c_budget >= 3.0:
            res = _c_stage(d, D, seed, best, c_budget)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
