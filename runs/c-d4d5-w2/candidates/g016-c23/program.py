"""Bi-Cayley search for bipartite degree-diameter graphs.

Construction: pick a finite group G of order N and a connection set S of d distinct elements.
Vertices are A_g and B_g for g in G, with A_g adjacent to B_{gs} for s in S. The graph is
bipartite, exactly d-regular, and has 2N vertices. Left multiplication is an automorphism, so the
diameter test needs only two BFS runs, from A_e and B_e.

The C engine hill-climbs over S for each candidate group. Groups are abelian, metacyclic
Z_m x| Z_k, dihedral, or dihedral times cyclic, and are tried in increasing order of N. The
engine searches for orders above the best known start, so every accepted graph is larger.

Trade-off: this replaces the parent's voltage-lift and grow-by-two engine on purpose. If no
bi-Cayley graph beats the algebraic start, the result falls back to that start (PG(2,q),
Araujo-Pardo-Lopez, W(q) or K_{d,d}), which is valid but may be well below the parent's score.
Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley hill-climb over a list of groups.
 * Usage:  prog d D seed time_limit < stream
 * stream: header "n m" (ignored), then the integers
 *         G, then for each group: N and an N x N multiplication table (identity = 0).
 * stdout: "V E" and E edges of the largest valid bi-Cayley graph found, or "0 0".
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXD 16
#define MAXV (2 * MAXG)
#define MAXE (MAXG * MAXD)

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int N;
static int mt[MAXG][MAXG];
static int inv_[MAXG];
static int S[MAXD], iS[MAXD];
static unsigned char inS[MAXG];
static int vis[MAXV], dep[MAXV], qu[MAXV];
static int vstamp = 0;

static int best_V = 0, best_E = 0;
static int best_eu[MAXE], best_ev[MAXE];

/* Vertices within distance D of src that are NOT reached (out of 2N). */
static int unreached(int src) {
    int V = 2 * N, head = 0, tail = 0, cnt = 1;
    vstamp++;
    vis[src] = vstamp;
    dep[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        if (dep[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = (v < N) ? N + mt[v][S[i]] : mt[v - N][iS[i]];
            if (vis[u] != vstamp) {
                vis[u] = vstamp;
                dep[u] = dep[v] + 1;
                qu[tail++] = u;
                cnt++;
            }
        }
    }
    return V - cnt;
}

/* Left-transitivity on each side: diameter <= D iff BFS from A_e and B_e reach everything. */
static int eval_S(void) {
    for (int i = 0; i < d; i++) iS[i] = inv_[S[i]];
    return unreached(0) + unreached(N);
}

static void record(void) {
    best_V = 2 * N;
    best_E = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            best_eu[best_E] = g;
            best_ev[best_E] = N + mt[g][S[i]];
            best_E++;
        }
}

static int hill(double until) {
    while (now() < until) {
        memset(inS, 0, (size_t)N);
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (inS[x]);
            inS[x] = 1;
            S[i] = x;
        }
        int cur = eval_S();
        double T = 0.8;
        for (long step = 0; step < 60000 && cur > 0; step++) {
            if ((step & 511) == 0 && now() > until) break;
            int i = rndint(d);
            int old = S[i];
            int x;
            do { x = rndint(N); } while (inS[x]);
            inS[old] = 0;
            inS[x] = 1;
            S[i] = x;
            int nv = eval_S();
            if (nv <= cur || rnd01() < exp((cur - nv) / T)) {
                cur = nv;
            } else {
                inS[x] = 0;
                inS[old] = 1;
                S[i] = old;
            }
            T *= 0.9995;
            if (T < 0.08) T = 0.8;
        }
        if (cur == 0) {
            record();
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(atol(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + atof(argv[4]);

    int hdrN, hdrM;
    if (scanf("%d %d", &hdrN, &hdrM) != 2) {
        printf("0 0\n");
        return 0;
    }
    int G = 0;
    if (scanf("%d", &G) != 1) G = 0;
    for (int gi = 0; gi < G; gi++) {
        int n;
        if (scanf("%d", &n) != 1 || n < 1 || n > MAXG) break;
        N = n;
        int bad = 0;
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++)
                if (scanf("%d", &mt[x][y]) != 1) bad = 1;
        if (bad) break;
        for (int x = 0; x < N; x++) inv_[x] = 0;
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++)
                if (mt[x][y] == 0) inv_[x] = y;
        int left = G - gi;
        if (2 * N <= best_V || N <= d) continue;
        if (now() >= t_end) break;
        double until = now() + (t_end - now()) / left;
        hill(until);
    }

    if (best_V == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_V, best_E);
    for (int e = 0; e < best_E; e++) printf("%d %d\n", best_eu[e], best_ev[e]);
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
    return out


# ------------------------------------------------------------ group families
# Every group is (order N, mul) on codes 0..N-1, with identity code 0.

def _divisors(n):
    return [a for a in range(1, n + 1) if n % a == 0]


def _abelian(a, b):
    """Z_a x Z_b, code u*b + v."""
    def mul(x, y):
        return ((x // b + y // b) % a) * b + (x % b + y % b) % b
    return a * b, mul


def _metacyclic(m, k, r):
    """Z_m x|_r Z_k, code a*k + b; needs gcd(r, m) = 1 and r^k = 1 mod m."""
    rp = [pow(r, e, m) for e in range(k)]

    def mul(x, y):
        a, b = divmod(x, k)
        c, e = divmod(y, k)
        return ((a + rp[b] * c) % m) * k + (b + e) % k
    return m * k, mul


def _dihedral(n):
    """Dihedral group of order 2n, code s*n + i for r^i f^s."""
    def mul(x, y):
        s, i = divmod(x, n)
        t, j = divmod(y, n)
        return ((s + t) % 2) * n + (i + (j if s == 0 else -j)) % n
    return 2 * n, mul


def _product(G1, G2):
    """Direct product, code x1 * N2 + x2."""
    N1, m1 = G1
    N2, m2 = G2

    def mul(x, y):
        a, b = divmod(x, N2)
        c, e = divmod(y, N2)
        return m1(a, c) * N2 + m2(b, e)
    return N1 * N2, mul


def _groups_of_order(N):
    out = []
    for a in _divisors(N):
        b = N // a
        if a <= b:
            out.append(_abelian(a, b))
    for m in _divisors(N):
        k = N // m
        if m < 3 or k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(_metacyclic(m, k, r))
    if N % 2 == 0 and N // 2 >= 3:
        half = N // 2
        out.append(_dihedral(half))
        for k in _divisors(half):
            n = half // k
            if k >= 2 and n >= 3:
                out.append(_product(_dihedral(n), _abelian(1, k)))
    return out


def _table(N, mul):
    tab = [[mul(x, y) for y in range(N)] for x in range(N)]
    if any(tab[0][x] != x or tab[x][0] != x for x in range(N)):
        return None
    if any(sorted(row) != list(range(N)) for row in tab):
        return None
    return tab


MAX_GROUPS = 80
MAX_CELLS = 2_000_000


def _pick_groups(lo, hi, seed):
    rng = random.Random(seed)
    pool = []
    for N in range(lo, hi + 1):
        for g in _groups_of_order(N):
            pool.append((N, g[1]))
    rng.shuffle(pool)
    chosen = []
    cells = 0
    for N, mul in pool:
        if len(chosen) >= MAX_GROUPS:
            break
        if cells + N * N > MAX_CELLS:
            continue
        tab = _table(N, mul)
        if tab is None:
            continue
        chosen.append((N, tab))
        cells += N * N
    chosen.sort(key=lambda t: t[0])
    return chosen


def _encode(chosen):
    """Flatten the group stream and wrap it as pairs for lib.run_c (the C side reads raw ints)."""
    stream = [len(chosen)]
    for N, tab in chosen:
        stream.append(N)
        for row in tab:
            stream.extend(row)
    if len(stream) % 2:
        stream.append(0)
    return [(stream[i], stream[i + 1]) for i in range(0, len(stream), 2)]


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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 16 or best[0] >= moore:
        return best

    lo = best[0] // 2 + 1          # need 2N > current best order
    hi = min(moore // 2, lo + 25, 256)
    lo = max(lo, d + 1)
    if hi < lo:
        return best

    chosen = _pick_groups(lo, hi, seed)
    if not chosen:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=(0, _encode(chosen)), timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
