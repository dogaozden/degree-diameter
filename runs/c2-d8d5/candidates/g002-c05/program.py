import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing for bi-Cayley lifts over Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = m*k2.
# Layer l matches A_i with B_{sig_l(i)} through voltage s: A_{i,g} ~ B_{j, g*s}.
# Each layer is a permutation, so every vertex gets degree d exactly.
#
# Fast exact diameter test: the group acts on the left and preserves the lift,
# so the diameter is at most D iff every vertex reaches every block representative
# (block b, identity) within D steps. Reachability is a bitmask over 2k blocks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000LL
#define ITERS 200000LL
#define PATIENCE 4000LL

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int pw[256];
static int *ginv_t;
static int *sig, *sv, *nbr, *perm, *badlist;
static uint32_t *cur, *cand, *scr;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int t = (int)(((long long)pw[b] * c) % m_);
    return ((a + t) % m_) * k2_ + (b + e) % k2_;
}

static int ginv_calc(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long v = (-(long long)pw[nb] * a) % m_;
    if (v < 0) v += m_;
    return (int)v * k2_ + nb;
}

static void set_dart(int l, int i) {
    int k = k_, G = G_, N = N_;
    int j = sig[l * k + i], v = sv[l * k + i];
    int iv = ginv_t[v];
    int *row = nbr + (size_t)l * N;
    int bi = (k + j) * G;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = bi + gmul(g, v);
        row[bi + g] = i * G + gmul(g, iv);
    }
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) {
        x &= x - 1;
        c++;
    }
    return c;
}

/* Number of (vertex, block) pairs whose block representative is farther than D. */
static long long eval_unreached(uint32_t *out) {
    int N = N_, G = G_, d = d_, B = 2 * k_;
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < B; b++) out[b * G] |= 1u << b;
    uint32_t *src = out, *dst = scr;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = src[v];
            for (int l = 0; l < d; l++) x |= src[nbr[(size_t)l * N + v]];
            dst[v] = x;
            if (x != src[v]) changed = 1;
        }
        uint32_t *tmp = src;
        src = dst;
        dst = tmp;
        if (!changed) break;
    }
    if (src != out) memcpy(out, src, sizeof(uint32_t) * (size_t)N);
    long long un = 0;
    for (int v = 0; v < N; v++) un += B - popc(out[v]);
    return un;
}

/* Repeated (i, j, s) triples across layers give duplicate edges. */
static long long dupcount(void) {
    long long c = 0;
    int k = k_, d = d_;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l * k + i] == sig[l2 * k + i] && sv[l * k + i] == sv[l2 * k + i]) c++;
    return c;
}

static void random_init(void) {
    int d = d_, k = k_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            sig[l * k + i] = perm[i];
            sv[l * k + i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
}

static void output_graph(void) {
    int N = N_, G = G_, k = k_, d = d_;
    long long M = (long long)d * k * G;
    printf("%d %lld\n", N, M);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || k_ > 8 || m_ < 2 || k2_ < 1 || k2_ > 200 ||
        r_ < 1 || r_ >= m_) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r_ % m_);
    if (((long long)pw[k2_ - 1] * r_) % m_ != 1 % m_) {
        printf("0 0\n");
        return 0;
    }

    ginv_t = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) ginv_t[x] = ginv_calc(x);
    sig = malloc(sizeof(int) * (size_t)d_ * k_);
    sv = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)d_ * N_);
    perm = malloc(sizeof(int) * (size_t)k_);
    badlist = malloc(sizeof(int) * (size_t)N_);
    cur = malloc(sizeof(uint32_t) * (size_t)N_);
    cand = malloc(sizeof(uint32_t) * (size_t)N_);
    scr = malloc(sizeof(uint32_t) * (size_t)N_);

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    double t_end = cpu_now() + budget;
    uint32_t full = (uint32_t)((1u << (2 * k_)) - 1);

    while (cpu_now() < t_end) {
        random_init();
        long long cost = eval_unreached(cur) + PEN * dupcount();
        long long c0 = cost > 0 ? cost : 1;
        long long best = cost, last = 0;

        for (long long t = 0; t < ITERS && cost > 0; t++) {
            if ((t & 127) == 0 && cpu_now() > t_end) break;
            if (t - last > PATIENCE) break;
            double temp = fmax(0.5, 0.01 * (double)c0 * (1.0 - (double)t / (double)ITERS));

            if (k_ >= 2 && rnd01() < 0.25) {
                int l = rndint(d_);
                int i1 = rndint(k_), i2 = rndint(k_ - 1);
                if (i2 >= i1) i2++;
                int tmp = sig[l * k_ + i1];
                sig[l * k_ + i1] = sig[l * k_ + i2];
                sig[l * k_ + i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
                long long nc = eval_unreached(cand) + PEN * dupcount();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                    cost = nc;
                    uint32_t *tp = cur;
                    cur = cand;
                    cand = tp;
                } else {
                    tmp = sig[l * k_ + i1];
                    sig[l * k_ + i1] = sig[l * k_ + i2];
                    sig[l * k_ + i2] = tmp;
                    set_dart(l, i1);
                    set_dart(l, i2);
                }
            } else {
                int l, i;
                int nb = 0;
                if (rnd01() < 0.4) {
                    for (int v = 0; v < N_; v++)
                        if (cur[v] != full) badlist[nb++] = v;
                }
                if (nb > 0) {
                    int u0 = badlist[rndint(nb)];
                    int block = u0 / G_;
                    l = rndint(d_);
                    if (block < k_) {
                        i = block;
                    } else {
                        i = -1;
                        for (int ii = 0; ii < k_; ii++)
                            if (sig[l * k_ + ii] == block - k_) {
                                i = ii;
                                break;
                            }
                        if (i < 0) i = rndint(k_);
                    }
                } else {
                    l = rndint(d_);
                    i = rndint(k_);
                }
                int old = sv[l * k_ + i];
                int nv = rndint(G_);
                if (nv == old) continue;
                sv[l * k_ + i] = nv;
                set_dart(l, i);
                long long nc = eval_unreached(cand) + PEN * dupcount();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                    cost = nc;
                    uint32_t *tp = cur;
                    cur = cand;
                    cand = tp;
                } else {
                    sv[l * k_ + i] = old;
                    set_dart(l, i);
                }
            }
            if (cost < best) {
                best = cost;
                last = t;
            }
        }
        if (cost == 0) {
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


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
# Edge-split pair insertion with 2-switch annealing (from the parent).
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (adj: list of sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _is_regular(n, edges, d):
    adj = lib.adjacency(n, edges)
    return all(len(a) == d for a in adj)


def _pair_insert(n, edges, d, D, rng, deadline, iters):
    """Try to grow a d-regular bipartite graph by two vertices. Returns (n+2, edges) or None."""
    adj0 = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj0):
        return None
    color = _bipartition(n, adj0)
    if color is None:
        return None

    adj = [set(a) for a in adj0] + [set(), set()]
    w, w2 = n, n + 1
    side1 = [v for v in range(n) if color[v] == 1]
    rng.shuffle(side1)
    used_a = set()
    picks = []
    for b in side1:
        cands = [a for a in adj[b] if a not in used_a]
        if not cands:
            continue
        a = rng.choice(cands)
        used_a.add(a)
        picks.append((a, b))
        if len(picks) == d:
            break
    if len(picks) < d:
        return None

    for a, b in picks:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[w].add(b)
        adj[b].add(w)
        adj[w2].add(a)
        adj[a].add(w2)

    col = color + [0, 1]
    side0 = [v for v in range(n + 2) if col[v] == 0]
    E = []
    S = set()
    for a in side0:
        for b in adj[a]:
            E.append((a, b))
            S.add((a, b))

    N = n + 2
    cur = _bad_count(N, adj, D)
    T0 = 1.0 + 0.05 * cur
    m = len(E)
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if (x1, y2) in S or (x2, y1) in S:
            continue
        adj[x1].discard(y1)
        adj[y1].discard(x1)
        adj[x2].discard(y2)
        adj[y2].discard(x2)
        adj[x1].add(y2)
        adj[y2].add(x1)
        adj[x2].add(y1)
        adj[y1].add(x2)
        new = _bad_count(N, adj, D)
        T = max(0.05, T0 * (1.0 - t / iters))
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            S.discard((x1, y1))
            S.discard((x2, y2))
            S.add((x1, y2))
            S.add((x2, y1))
            E[i] = (x1, y2)
            E[j] = (x2, y1)
        else:
            adj[x1].discard(y2)
            adj[y2].discard(x1)
            adj[x2].discard(y1)
            adj[y1].discard(x2)
            adj[x1].add(y1)
            adj[y1].add(x1)
            adj[x2].add(y2)
            adj[y2].add(x2)

    if cur != 0:
        return None
    return N, E


# ----------------------------------------------------------------------------
# Group sampling for Z_m x| Z_k2 (r^k2 = 1 mod m).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.80 * budget
    insert_deadline = start + 0.92 * budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search in C, with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    per_call = max(2.0, 0.08 * budget)
    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            continue
        left = search_deadline - time.monotonic()
        per = min(left, per_call)
        if per < 1.0:
            break
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 10 ** 9), round(per, 2), k, m, k2, r],
                            timeout=per + 5.0)
            n2, e2 = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            break
        if n2 > 0 and e2:
            wins[k] += 1
            consider(n2, e2)

    # Edge-split pair insertion from the best regular graph.
    if time.monotonic() < insert_deadline and _is_regular(best[0], best[1], d):
        fails = 0
        while time.monotonic() < insert_deadline and fails < 400:
            chunk = min(insert_deadline, time.monotonic() + 8.0)
            res = _pair_insert(best[0], best[1], d, D, rng, chunk, 800)
            if res is None:
                fails += 1
                continue
            fails = 0
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
