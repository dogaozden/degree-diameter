"""Bi-Cayley / multi-fibre voltage lift search for the degree-diameter problem.

Construction: pick a group G of order N (cyclic or Z_m x| Z_k), p fibres per side, and d
perfect matchings between the A-fibres and the B-fibres, each carrying a group voltage.
Vertex A_i x is joined to B_j (x g) for every dart (i -> j, g). Left multiplication by G is an
automorphism that acts regularly on every fibre, so the diameter test only needs BFS from the
2p fibre representatives. The C engine hill-climbs permutations and voltages to reach diameter
<= D and only reports graphs larger than the lower bound it receives. The Python side keeps the
algebraic and K_{d,d} starts as a fallback and validates everything before returning it.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXD 32
#define MAXP 4
#define MAXN 512

static int d, D, lb;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

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

/* Group: Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int N;
static int mt[MAXN * MAXN];

static void build_group(int m, int k, int r) {
    N = m * k;
    int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mt[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
}

static void pick_group(int n) {
    int cnt = 0, bm = 1, bk = n, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cnt++;
            if (rndint(cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    build_group(bm, bk, br);
}

/* Lift state: P fibres per side, d darts per fibre (one per row t). */
static int P;
static int sig[MAXD][MAXP];   /* dart (t,i) joins A_i to B_{sig[t][i]} */
static int gv[MAXD][MAXP];    /* voltage of dart (t,i) */
static int adjv[MAXV][MAXD], degv[MAXV];
static int V;

static int bV = 0, bdeg[MAXV], badj[MAXV][MAXD];

/* Would dart (t,i) with voltage g clash with another dart from A_i to the same B_j? */
static int clash(int t, int i, int g) {
    int j = sig[t][i];
    for (int t2 = 0; t2 < d; t2++) {
        if (t2 == t) continue;
        if (sig[t2][i] == j && gv[t2][i] == g) return 1;
    }
    return 0;
}

static int fresh(int t, int i) {
    for (;;) {
        int g = rndint(N);
        if (!clash(t, i, g)) return g;
    }
}

static void build_graph(void) {
    V = 2 * P * N;
    for (int v = 0; v < V; v++) degv[v] = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) {
            int j = sig[t][i], g = gv[t][i];
            for (int x = 0; x < N; x++) {
                int a = i * N + x;
                int b = (P + j) * N + mt[x * N + g];
                adjv[a][degv[a]++] = b;
                adjv[b][degv[b]++] = a;
            }
        }
}

static int distv[MAXV], qv[MAXV];

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    for (int v = 0; v < V; v++) distv[v] = -1;
    int head = 0, tail = 0;
    distv[src] = 0;
    qv[tail++] = src;
    while (head < tail) {
        int v = qv[head++];
        if (distv[v] >= D) continue;
        for (int k = 0; k < degv[v]; k++) {
            int u = adjv[v][k];
            if (distv[u] < 0) {
                distv[u] = distv[v] + 1;
                qv[tail++] = u;
            }
        }
    }
    return tail;
}

/* Orbit-reduced objective: unreached pairs from the 2P fibre representatives. */
static long eval_bad(void) {
    build_graph();
    long bad = 0;
    for (int b = 0; b < 2 * P; b++)
        bad += V - bfs_reach(b * N);
    return bad;
}

/* Exact check on the current lift: simple, bipartite, degree <= d, diameter <= D. */
static int full_check(void) {
    build_graph();
    int half = P * N;
    for (int v = 0; v < V; v++) {
        if (degv[v] > d) return 0;
        for (int k = 0; k < degv[v]; k++) {
            int u = adjv[v][k];
            if (u == v) return 0;
            if ((u < half) == (v < half)) return 0;
            for (int l = 0; l < k; l++)
                if (adjv[v][l] == u) return 0;
        }
    }
    for (int v = 0; v < V; v++)
        if (bfs_reach(v) != V) return 0;
    return 1;
}

static void save_best(void) {
    bV = V;
    for (int v = 0; v < V; v++) {
        bdeg[v] = degv[v];
        memcpy(badj[v], adjv[v], sizeof(int) * degv[v]);
    }
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < P; i++) sig[t][i] = perm[i];
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++)
            gv[t][i] = fresh(t, i);
}

static void mutate(void) {
    if (P > 1 && rnd01() < 0.25) {
        int t = rndint(d);
        int a = rndint(P), b = rndint(P - 1);
        if (b >= a) b++;
        int s = sig[t][a]; sig[t][a] = sig[t][b]; sig[t][b] = s;
        gv[t][a] = fresh(t, a);
        gv[t][b] = fresh(t, b);
    } else {
        int t = rndint(d), i = rndint(P);
        gv[t][i] = fresh(t, i);
    }
}

static int attempt(long steps) {
    random_state();
    long bad = eval_bad();
    static int sg[MAXD][MAXP], gg[MAXD][MAXP];
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        memcpy(sg, sig, sizeof sig);
        memcpy(gg, gv, sizeof gv);
        mutate();
        long nb = eval_bad();
        if (nb <= bad || rnd01() < 0.03) {
            bad = nb;
        } else {
            memcpy(sig, sg, sizeof sig);
            memcpy(gv, gg, sizeof gv);
        }
    }
    return bad == 0;
}

static void print_best(void) {
    long m = 0;
    for (int u = 0; u < bV; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (u < badj[u][k]) m++;
    printf("%d %ld\n", bV, m);
    for (int u = 0; u < bV; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (u < badj[u][k]) printf("%d %d\n", u, badj[u][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lower_bound]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    lb = argc > 5 ? atoi(argv[5]) : 0;

    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long cap = moore < MAXV ? moore : MAXV;
    int found = 0;

    while (now() < t_end) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 8 ? 2 : 3;
        int Nlo = lb / (2 * p) + 1;
        if (Nlo < d) Nlo = d;
        if (2L * p * Nlo > cap || Nlo > MAXN) continue;
        int Nt = Nlo + rndint(3);
        while (Nt > Nlo && (2L * p * Nt > cap || Nt > MAXN)) Nt--;

        P = p;
        pick_group(Nt);
        if (attempt(15000) && full_check() && 2 * P * N > lb) {
            save_best();
            lb = bV;
            found = 1;
        }
    }

    if (!found) printf("0 0\n");
    else print_best();
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

    # Safe fallback: K_{d,d} (valid for D >= 2), upgraded by any valid algebraic start.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0]],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
