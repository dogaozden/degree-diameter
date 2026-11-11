"""Signed 2-lift doubling with annealing on the sign vector.

This replaces the bi-Cayley/metacyclic search with a different construction. Starting from the
best algebraic graph (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}), the C engine repeatedly
doubles the graph. A 2-lift of a bipartite base b sends each base edge (u,v) to a sign s in {0,1}:
(u,0)-(v,s) and (u,1)-(v,1-s). Degree is preserved, bipartiteness is preserved automatically, and
the diameter is checked exactly with a bitset ball expansion. Signs are annealed to minimise the
number of pairs at distance > D. A doubling is accepted only at zero bad pairs, so every stored
base is valid. The engine stops when the next doubling is out of reach and prints the last valid
graph. Python keeps the largest valid candidate, falling back to the algebraic start.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXW (MAXN / 64)
#define MAXD 32
#define MAXE (MAXN * MAXD / 2)

static int d, D;
static long MOORE;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
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

/* Base graph: simple bipartite graph on bn vertices with bm edges eu[e]-ev[e]. */
static int bn, bm;
static int eu[MAXE], ev[MAXE];
static int sg[MAXE];

/* Working lifted adjacency. */
static int ldeg[MAXN];
static int ladj[MAXN][MAXD];

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static void add_l(int a, int b) {
    ladj[a][ldeg[a]++] = b;
    ladj[b][ldeg[b]++] = a;
}

/* Number of unordered pairs at distance > D in the first n vertices of the working graph. */
static long bad_pairs(int n) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < ldeg[v]; i++) {
                const uint64_t *s = cur + (size_t)ladj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

/* Build the 2-lift of the base with the current signs sg[]. Vertex x + i*bn is copy i of x. */
static void build_lift(void) {
    int n = 2 * bn;
    for (int v = 0; v < n; v++) ldeg[v] = 0;
    for (int e = 0; e < bm; e++) {
        int u = eu[e], v = ev[e], s = sg[e];
        add_l(u, v + s * bn);
        add_l(u + bn, v + (1 - s) * bn);
    }
}

static long score_signs(void) {
    build_lift();
    return bad_pairs(2 * bn);
}

/* One annealing run from random signs. Returns 1 if the lift has diameter <= D.
 * On success the working adjacency matches sg[] (the last accepted state). */
static int anneal_once(int iters, double until) {
    if (bm == 0) return 0;
    for (int e = 0; e < bm; e++) sg[e] = rndint(2);
    long bad = score_signs();
    if (bad == 0) return 1;
    double T = 2.0 + 0.02 * (double)bad;
    double cool = pow(0.2 / T, 1.0 / iters);
    for (int it = 0; it < iters && bad > 0; it++) {
        if ((it & 15) == 0 && now() > until) break;
        int e = rndint(bm);
        sg[e] ^= 1;
        long nb = score_signs();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            sg[e] ^= 1;
        }
        T *= cool;
    }
    return bad == 0;
}

/* Replace the base by its 2-lift (valid, since bad == 0 was checked). */
static void promote(void) {
    static int tu[MAXE], tv[MAXE];
    int n2 = 2 * bn, m2 = 0;
    for (int e = 0; e < bm; e++) {
        int s = sg[e];
        tu[m2] = eu[e];
        tv[m2] = ev[e] + s * bn;
        m2++;
        tu[m2] = eu[e] + bn;
        tv[m2] = ev[e] + (1 - s) * bn;
        m2++;
    }
    for (int e = 0; e < m2; e++) {
        eu[e] = tu[e];
        ev[e] = tv[e];
    }
    bn = n2;
    bm = m2;
}

static void print_base(void) {
    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", eu[e], ev[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    MOORE = moore_bound();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN / 2 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) ldeg[v] = 0;
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || ldeg[u] >= d || ldeg[v] >= d) {
            ok = 0;
            break;
        }
        for (int i = 0; i < ldeg[u]; i++)
            if (ladj[u][i] == v) ok = 0;
        if (!ok) break;
        add_l(u, v);
        eu[e] = u;
        ev[e] = v;
    }
    if (!ok) { printf("0 0\n"); return 0; }

    /* Bipartiteness check of the start. */
    static int col[MAXN], qu[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        qu[tail++] = s;
        while (head < tail) {
            int v = qu[head++];
            for (int i = 0; i < ldeg[v]; i++) {
                int u = ladj[v][i];
                if (col[u] < 0) { col[u] = 1 - col[v]; qu[tail++] = u; }
                else if (col[u] == col[v]) ok = 0;
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }
    if (bad_pairs(n) != 0) { printf("0 0\n"); return 0; }

    bn = n;
    bm = m;

    /* Doubling loop: each level is kept only if a valid signed 2-lift is found. */
    while (2L * bn <= MOORE && 2 * bn <= MAXN && now() < t_end) {
        int found = 0;
        while (now() < t_end) {
            if (anneal_once(400, t_end)) { found = 1; break; }
        }
        if (!found) break;
        promote();
    }

    print_base();
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
