import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: rarest-first cover growth with cover local search (from parent c05).
# A vertex is added on colour c when its neighbourhood S (opposite colour, spare
# degree) covers every existing vertex within distance D-1. Adding vertices and
# edges never breaks diameter <= D. The final graph is verified before printing.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 6144
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define ATTEMPTS 40
#define LS_ITERS 150

typedef uint64_t u64;

static int dd, DD, n, W;
static int color[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static u64 ball[MAXN][MAXW];
static u64 tmpb[MAXN][MAXW];
static int cntx[MAXN];
static int cand[MAXN];
static int ncand;
static char taken[MAXN];
static int chosen[MAXD];
static int nch;
static u64 rs = 88172645463325252ULL;
static double deadline_s;
static int eu[MAXE], ev[MAXE];
static int n_in, m_in;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int k) {
    return (int)(rnd64() % (u64)k);
}

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int count_bits(const u64 *a) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(a[w]);
    return c;
}

static int count_union(const u64 *a, const u64 *b) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(a[w] | b[w]);
    return c;
}

/* ball[v] = all vertices within distance r of v. */
static void compute_balls(int r) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(ball[v], 0, sizeof(u64) * W);
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            u64 *t = tmpb[v];
            memcpy(t, ball[v], sizeof(u64) * W);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *bu = ball[adj[v][k]];
                for (int w = 0; w < W; w++) t[w] |= bu[w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(ball[v], tmpb[v], sizeof(u64) * W);
    }
}

static int bipartite_color(void) {
    static int queue[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (color[v] == -1) {
                    color[v] = 1 - color[u];
                    queue[qt++] = v;
                } else if (color[v] == color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Greedy rarest-first cover of all n vertices by at most dd candidate balls. */
static int greedy_cover(void) {
    u64 cov[MAXW];
    for (int x = 0; x < n; x++) cntx[x] = 0;
    for (int i = 0; i < ncand; i++) {
        const u64 *b = ball[cand[i]];
        for (int w = 0; w < W; w++) {
            u64 bits = b[w];
            while (bits) {
                cntx[(w << 6) + __builtin_ctzll(bits)]++;
                bits &= bits - 1;
            }
        }
    }
    memset(cov, 0, sizeof(u64) * W);
    nch = 0;
    int covered = 0;
    while (covered < n && nch < dd) {
        int bx = -1, bc = 0x7fffffff, ties = 0;
        for (int x = 0; x < n; x++) {
            if ((cov[x >> 6] >> (x & 63)) & 1ULL) continue;
            if (cntx[x] <= 0) return 0;
            if (cntx[x] < bc) {
                bc = cntx[x];
                bx = x;
                ties = 1;
            } else if (cntx[x] == bc) {
                ties++;
                if (rnd_int(ties) == 0) bx = x;
            }
        }
        int noisy = (rnd_int(100) < 15);
        int bs = -1;
        long long bsc = -1;
        for (int i = 0; i < ncand; i++) {
            int s = cand[i];
            if (taken[s]) continue;
            if (!((ball[s][bx >> 6] >> (bx & 63)) & 1ULL)) continue;
            long long sc;
            if (noisy) {
                sc = rnd_int(1 << 30);
            } else {
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(ball[s][w] & ~cov[w]);
                sc = (long long)g * 4096 + rnd_int(4096);
            }
            if (sc > bsc) {
                bsc = sc;
                bs = s;
            }
        }
        if (bs < 0) return 0;
        taken[bs] = 1;
        chosen[nch++] = bs;
        for (int w = 0; w < W; w++) {
            u64 bits = ball[bs][w];
            covered += pc64(bits & ~cov[w]);
            cov[w] |= bits;
            while (bits) {
                cntx[(w << 6) + __builtin_ctzll(bits)]--;
                bits &= bits - 1;
            }
        }
    }
    return covered == n;
}

/* Swap-based local search on a full set of dd chosen candidates. */
static int cover_ls(void) {
    u64 cc[MAXW], rest[MAXW];
    for (int it = 0; it <= LS_ITERS; it++) {
        memset(cc, 0, sizeof(u64) * W);
        for (int j = 0; j < nch; j++)
            for (int w = 0; w < W; w++) cc[w] |= ball[chosen[j]][w];
        int cur = n - count_bits(cc);
        if (cur == 0) return 1;
        if (it == LS_ITERS) break;
        int i = rnd_int(nch);
        memset(rest, 0, sizeof(u64) * W);
        for (int j = 0; j < nch; j++) {
            if (j == i) continue;
            for (int w = 0; w < W; w++) rest[w] |= ball[chosen[j]][w];
        }
        int bc = -1, bu = 0x7fffffff;
        for (int t = 0; t < 60; t++) {
            int c = cand[rnd_int(ncand)];
            if (taken[c]) continue;
            int u = n - count_union(rest, ball[c]);
            if (u < bu) {
                bu = u;
                bc = c;
            }
        }
        if (bc >= 0 && bu <= cur) {
            taken[chosen[i]] = 0;
            chosen[i] = bc;
            taken[bc] = 1;
        }
    }
    return 0;
}

static void add_vertex(int c) {
    int v = n++;
    color[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        adj[s][deg[s]++] = v;
        adj[v][deg[v]++] = s;
    }
}

static int try_add(void) {
    int first = rnd_int(2);
    for (int t = 0; t < 2; t++) {
        int c = (t == 0) ? first : 1 - first;
        ncand = 0;
        for (int v = 0; v < n; v++)
            if (color[v] == 1 - c && deg[v] < dd) cand[ncand++] = v;
        if (ncand == 0) continue;
        for (int att = 0; att < ATTEMPTS; att++) {
            if (now_s() > deadline_s) return 0;
            for (int i = 0; i < ncand; i++) taken[cand[i]] = 0;
            int ok = greedy_cover();
            if (!ok && nch == dd) ok = cover_ls();
            if (ok) {
                add_vertex(c);
                return 1;
            }
        }
    }
    return 0;
}

static int verify(void) {
    compute_balls(DD);
    for (int v = 0; v < n; v++) {
        if (count_bits(ball[v]) != n) return 0;
        if (deg[v] > dd) return 0;
        for (int k = 0; k < deg[v]; k++)
            if (color[adj[v][k]] == color[v]) return 0;
    }
    return 1;
}

static void print_input(void) {
    printf("%d %d\n", n_in, m_in);
    for (int i = 0; i < m_in; i++) printf("%d %d\n", eu[i], ev[i]);
}

static void print_current(void) {
    long long sum = 0;
    for (int v = 0; v < n; v++) sum += deg[v];
    printf("%d %lld\n", n, sum / 2);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (scanf("%d %d", &n, &m_in) != 2 || n <= 0 || n > MAXN - 2 ||
        m_in < 0 || m_in > MAXE || dd < 1 || dd > MAXD) {
        printf("0 0\n");
        return 0;
    }
    n_in = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || deg[u] >= dd || deg[v] >= dd) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        eu[i] = u;
        ev[i] = v;
    }
    if (DD < 2 || !bipartite_color()) {
        print_input();
        return 0;
    }
    deadline_s = now_s() + budget;
    compute_balls(DD - 1);
    while (n < MAXN - 2 && now_s() < deadline_s) {
        if (!try_add()) break;
        compute_balls(DD - 1);
    }
    if (!verify()) {
        print_input();
        return 0;
    }
    print_current();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

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


def _prime_powers_upto(d, cap=None):
    """Prime powers q with q + 1 <= d (and q <= cap), largest first."""
    return [q for q in range(d - 1, 1, -1)
            if lib.is_prime_power(q) and (cap is None or q <= cap)]


# ----------------------------------------------------------------------------
# Local moves that preserve validity (both only add vertices or edges).
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twins: a new vertex with the same neighbourhood as an existing x keeps diameter and bipartiteness."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices (adding edges keeps diameter <= D)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# C growth wrapper and the combined improvement loop.
# ----------------------------------------------------------------------------

def _grow_c(n, edges, d, D, budget, seed):
    """Run the C rarest-first cover growth from a valid graph; return (n, edges) if it grew and is valid."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 8.0)
        gn, ge = lib.parse_graph_text(out)
    except Exception:
        return None
    if gn > n and lib.is_valid(gn, ge, d, D):
        return gn, ge
    return None


def _improve(n, edges, d, D, deadline, rng, time_limit, seed):
    """Alternate C cover growth, edge saturation and twin growth until two rounds add no vertex.

    Every intermediate graph is validated; returns the best valid (n, edges) seen.
    """
    best = (n, edges)
    cur_n, cur_e = n, edges
    stale, runs = 0, 0
    while time.monotonic() < deadline - 1.0 and stale < 2:
        before = cur_n
        budget = min(deadline - time.monotonic() - 1.0, max(5.0, 0.2 * time_limit))
        res = _grow_c(cur_n, cur_e, d, D, budget, seed * 7919 + runs)
        runs += 1
        if res is not None:
            cur_n, cur_e = res
        if time.monotonic() >= deadline - 1.0:
            break
        se = _saturate_edges(cur_n, cur_e, d, rng)
        tn, te = _twin_grow(cur_n, se, d, rng, deadline - 1.0)
        te = _saturate_edges(tn, te, d, rng)
        if lib.is_valid(tn, te, d, D):
            cur_n, cur_e = tn, te
        if cur_n > best[0] and lib.is_valid(cur_n, cur_e, d, D):
            best = (cur_n, cur_e)
        stale = 0 if cur_n > before else stale + 1
    return best


# ----------------------------------------------------------------------------
# Voltage lifts over non-cyclic groups (semidirect Z_m x| Z_k2), for leftover time.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    deadline = t_start + 0.85 * time_limit
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(gn, ge):
        nonlocal best, best_n
        if gn > best_n and lib.is_valid(gn, ge, d, D):
            best = (gn, ge)
            best_n = gn

    # Starting graphs with spare degree for growth.
    starts = []
    if D == 3:
        for q in _prime_powers_upto(d)[:2]:
            starts.append(lib.projective_plane_incidence(q))
    elif D == 4:
        for q in _prime_powers_upto(d, cap=16)[:2]:
            if time.monotonic() > t_start + 0.3 * time_limit and starts:
                break
            starts.append(_gq_w(q))

    # Growth pipeline: each start is improved with C growth, saturation and twins.
    for i, (sn, se) in enumerate(starts):
        consider(sn, se)
        if time.monotonic() >= deadline - 1.0:
            break
        share = (deadline - time.monotonic()) / (len(starts) - i)
        gn, ge = _improve(sn, se, d, D, time.monotonic() + share, rng,
                          time_limit, seed * 31 + i)
        consider(gn, ge)

    # Leftover time: non-cyclic group-lift search for D >= 4.
    if D >= 4:
        G_next = {k: 2 for k in (1, 2, 3, 4)}
        while time.monotonic() < deadline - 1.0:
            k = rng.choice([1, 2, 3, 4])
            G = max(G_next[k], best_n // (2 * k) + 1, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                G_next[k] = G + 1
            else:
                G_next[k] = G

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
