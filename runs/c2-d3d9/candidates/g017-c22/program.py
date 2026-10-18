"""Starter program: Python builds the best known start graph, the C engine searches from it.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: simulated annealing over voltage lifts.
 *
 * Usage:   prog d D seed time_limit
 * stdin:   ignored.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Model: P base vertices per side (P = 1, 2 or 3). The base is d-regular: d permutations of
 * P points, giving darts (i -> j). A lift over a group G of order N has vertices A(i,x) and
 * B(j,y), x,y in G, and edges A(i,x) -- B(j, x*g) for each dart (i,j,g). Distinct darts
 * between the same pair get distinct voltages, so the lift is simple and d-regular.
 *
 * Cost: number of vertices not within distance D of the 2P orbit representatives
 * (identities of each A-class and B-class). Left multiplication is an automorphism, so cost 0
 * is equivalent to diameter <= D.
 *
 * Search: a target vertex count T starts at K_{d,d} and grows by a step that doubles on
 * success and halves on failure. For each T, random (P, group, base) are annealed on the
 * voltages until cost 0. Every accepted graph is re-verified by BFS from every vertex.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXD 32
#define MAXP 3
#define MAXND (MAXD * MAXP)

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

static int gcd_i(int a, int b) {
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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, order N = m*k. Element (a,b) is a*k+b; identity is 0.
 * (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Needs gcd(r,m)=1 and r^k = 1 mod m. */
static int N;                 /* current group order */
static int *cmul = NULL;      /* N*N multiplication table */
static int cmul_cap = 0;
static int cinv[MAXV];
static int rp_tab[MAXV];

static void build_group(int m, int k, int r) {
    int n = m * k;
    if (n * n > cmul_cap) {
        free(cmul);
        cmul = malloc(sizeof(int) * (size_t)n * (size_t)n);
        if (!cmul) { fprintf(stderr, "oom\n"); exit(1); }
        cmul_cap = n * n;
    }
    for (int b = 0; b < k; b++) rp_tab[b] = (int)powmod(r, b, m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            cmul[x * n + y] = (int)(((long)a + (long)rp_tab[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (cmul[x * n + y] == 0) { cinv[x] = y; break; }
    N = n;
}

/* Uniformly random (m, k, r) with m*k = n. Two passes: count, then pick. */
static void pick_group(int n, int *pm, int *pk, int *pr) {
    int count = 0, target = 0;
    for (int pass = 0; pass < 2; pass++) {
        if (pass == 1) target = rndint(count);
        int idx = 0;
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            int rmax = (m == 1) ? 1 : m;
            for (int r = 0; r < rmax; r++) {
                if (m > 1 && gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                if (pass == 0) {
                    count++;
                } else if (idx++ == target) {
                    *pm = m; *pk = k; *pr = r;
                    return;
                }
            }
        }
    }
}

/* ------------------------------------------------------------------ base and darts */

static int P;                          /* base vertices per side */
static int nd;                         /* number of darts = d * P */
static int dI[MAXND], dJ[MAXND], dG[MAXND];
static int outn[MAXP][MAXD], inn[MAXP][MAXD];

/* d random permutations of P points: dart t*P+i goes from A-base i to B-base perm_t[i].
 * Retried until the base multigraph is connected. */
static void make_base(void) {
    for (;;) {
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < P; i++) {
                int idx = t * P + i;
                dI[idx] = i;
                dJ[idx] = perm[i];
                outn[i][t] = idx;
                inn[perm[i]][t] = idx;
            }
        }
        int conn[2 * MAXP][2 * MAXP];
        memset(conn, 0, sizeof conn);
        for (int t = 0; t < nd; t++) {
            conn[dI[t]][P + dJ[t]] = 1;
            conn[P + dJ[t]][dI[t]] = 1;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, cnt = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * P; u++)
                if (conn[v][u] && !seen[u]) { seen[u] = 1; cnt++; st[top++] = u; }
        }
        if (cnt == 2 * P) return;
    }
}

/* Voltage of dart t must differ from the voltages of other darts with the same endpoints. */
static int conflict(int t, int g) {
    for (int u = 0; u < nd; u++)
        if (u != t && dI[u] == dI[t] && dJ[u] == dJ[t] && dG[u] == g) return 1;
    return 0;
}

static void init_voltages(void) {
    for (int t = 0; t < nd; t++) dG[t] = -1;
    for (int t = 0; t < nd; t++) {
        int g;
        do { g = rndint(N); } while (conflict(t, g));
        dG[t] = g;
    }
}

/* ------------------------------------------------------------------ cost */

static int distv[MAXV], qv[MAXV];

/* Sum over the 2P orbit representatives of vertices NOT within distance D. */
static long eval_cost(void) {
    int pN = P * N, V = 2 * pN;
    long miss = 0;
    for (int src = 0; src < 2 * P; src++) {
        int s0 = src < P ? src * N : pN + (src - P) * N;
        for (int v = 0; v < V; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[s0] = 0;
        qv[tail++] = s0;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < pN) {
                int i = v / N, x = v - i * N;
                for (int c = 0; c < d; c++) {
                    int t = outn[i][c];
                    int u = pN + dJ[t] * N + cmul[x * N + dG[t]];
                    if (distv[u] < 0) { distv[u] = dv + 1; qv[tail++] = u; }
                }
            } else {
                int w = v - pN, j = w / N, y = w - j * N;
                for (int c = 0; c < d; c++) {
                    int t = inn[j][c];
                    int u = dI[t] * N + cmul[y * N + cinv[dG[t]]];
                    if (distv[u] < 0) { distv[u] = dv + 1; qv[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

/* ------------------------------------------------------------------ graphs */

static int gadj[MAXV][MAXD], gdeg[MAXV], gV;   /* candidate graph */
static int badj[MAXV][MAXD], bdeg[MAXV], bV;   /* best graph so far */

static void build_explicit(void) {
    int pN = P * N;
    gV = 2 * pN;
    for (int v = 0; v < gV; v++) gdeg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = pN + dJ[t] * N + cmul[x * N + dG[t]];
            gadj[a][gdeg[a]++] = b;
            gadj[b][gdeg[b]++] = a;
        }
}

/* Full check on the explicit candidate: simple, bipartite, degree <= d, diameter <= D. */
static int full_check(void) {
    if (gV <= 0 || gV > MAXV) return 0;
    int half = P * N;
    for (int v = 0; v < gV; v++) {
        if (gdeg[v] > d) return 0;
        for (int i = 0; i < gdeg[v]; i++) {
            int u = gadj[v][i];
            if (u < 0 || u >= gV || u == v) return 0;
            if ((v < half) == (u < half)) return 0;
            for (int j = 0; j < i; j++)
                if (gadj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < gV; s++) {
        for (int v = 0; v < gV; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[s] = 0;
        qv[tail++] = s;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            for (int i = 0; i < gdeg[v]; i++) {
                int u = gadj[v][i];
                if (distv[u] < 0) { distv[u] = dv + 1; qv[tail++] = u; }
            }
        }
        if (tail != gV) return 0;
    }
    return 1;
}

static void save_best(void) {
    bV = gV;
    for (int v = 0; v < gV; v++) {
        bdeg[v] = gdeg[v];
        memcpy(badj[v], gadj[v], sizeof(int) * (size_t)gdeg[v]);
    }
}

/* Start: K_{d,d} for D >= 2, K_{1,1} otherwise. Both are valid. */
static void init_best(void) {
    int k = (D >= 2) ? d : 1;
    bV = 2 * k;
    for (int v = 0; v < bV; v++) bdeg[v] = 0;
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++) {
            badj[a][bdeg[a]++] = k + b;
            badj[k + b][bdeg[k + b]++] = a;
        }
}

static void print_best(void) {
    long m = 0;
    for (int v = 0; v < bV; v++) m += bdeg[v];
    m /= 2;
    printf("%d %ld\n", bV, m);
    for (int u = 0; u < bV; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (u < badj[u][i]) printf("%d %d\n", u, badj[u][i]);
}

/* ------------------------------------------------------------------ annealing */

static int pick_P(void) {
    int r = rndint(10);
    return r < 5 ? 1 : (r < 8 ? 2 : 3);
}

/* One annealing attempt on a random group of order Nn and random base with P = Pp.
 * On success (valid, and larger than the best) the best graph is replaced. */
static int attempt(int Pp, int Nn, double until, long steps) {
    P = Pp;
    nd = d * P;
    int m, k, r;
    pick_group(Nn, &m, &k, &r);
    build_group(m, k, r);
    make_base();
    init_voltages();
    long cost = eval_cost();
    double T0 = 1.5, T1 = 0.05;
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double temp = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(nd);
        int g = rndint(N);
        if (g == dG[t] || conflict(t, g)) continue;
        int old = dG[t];
        dG[t] = g;
        long nc = eval_cost();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) cost = nc;
        else dG[t] = old;
    }
    if (cost != 0) return 0;
    build_explicit();
    if (!full_check()) return 0;
    if (gV > bV) save_best();
    return 1;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    t_end = now() + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    init_best();
    long moore = moore_bound();

    if (D >= 2 && d >= 2 && moore > bV) {
        long step = 2;
        while (now() < t_end) {
            long target = bV + step;
            if (target > moore || target > MAXV) {
                if (step > 2) { step = 2; continue; }
                break;
            }
            double rem = t_end - now();
            double slice = 0.3 * rem;
            if (slice < 1.0) slice = rem;
            double until = now() + slice;
            int ok = 0;
            while (!ok && now() < until) {
                int Pp = pick_P();
                int Nn = (int)((target + 2 * Pp - 1) / (2 * Pp));
                if (Nn < d) Nn = d;
                if (2L * Pp * Nn > moore || 2 * Pp * Nn > MAXV) {
                    Pp = 1;
                    Nn = (int)((target + 1) / 2);
                    if (Nn < d) Nn = d;
                    if (2L * Nn > moore || 2 * Nn > MAXV) break;
                }
                ok = attempt(Pp, Nn, until, 60000);
            }
            if (ok) {
                if (step < 64) step *= 2;
            } else {
                if (step <= 2) break;
                step /= 2;
            }
        }
    }
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _valid_or_none(g, d, D):
    """Return g if it is a valid graph for (d, D), else None."""
    try:
        if g is not None and lib.is_valid(g[0], g[1], d, D):
            return g
    except Exception:
        pass
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _valid_or_none(known_start(d, D), d, D)
    if best is None:
        best = _valid_or_none(lib.haar_graph(d, range(d)), d, D)   # K_{d,d} (valid for D >= 2)
    if best is None:
        best = (1, [])                                             # single vertex: always valid
    if best[0] >= lib.moore_bound(d, D):
        return best   # already optimal; no search needed

    budget = 0.7 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget < 2.0:
        return best
    try:
        # The C engine ignores stdin and builds its own graphs from scratch.
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 10.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
