"""Difference-cover program for the D = 3 targets.

For D = 3, the Haar graph H(G, S) of an abelian group G of order N with connection set S
(|S| = d, a_x ~ b_{x+s}) has diameter at most 3 exactly when every nonzero element of G is a
difference s - t of two elements of S. The C engine searches for such covers (S, with 0 in S)
by simulated annealing on the number of uncovered differences. Each move costs O(d), so it runs
millions of moves per second. It tries N = (start order / 2) + 1, +2, ... over every abelian
group of order N, and returns the largest valid Haar graph found, which has 2N vertices.

Known constructions remain the fallback. Python keeps the Moore graph or the Araujo-Pardo
graph as the start, and returns it unless the C result is strictly larger and passes lib.is_valid.
This island scores only D = 3, so the general lift/grow search of the parent is dropped for D != 3,
and those cases return the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Difference-cover search for bipartite Haar graphs of diameter 3.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   ignored apart from the start order (any "n m" + edges, or "0 0").
 * stdout:  "n m" then m lines "u v" for the largest valid graph found, else K_{d,d}.
 *
 * Model: abelian group G = Z_a x Z_b (a | b, a*b = N), connection set S = {0, s_1..s_{d-1}}.
 * Vertices a_x (0..N-1) and b_y (N..2N-1); a_x ~ b_{x+s} for s in S. Every vertex has degree d.
 * Diameter <= 3 iff every nonzero g in G is an ordered difference s - t (s != t in S).
 * Anneal S to minimise the number of uncovered nonzero elements. Each move updates the
 * difference-count table in O(d). The final graph is checked by BFS from every vertex.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXV (2 * MAXG)
#define MAXD 40
#define ITERS 300000L

static int d, D;
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

/* ------------------------------------------------------------ group tables */

static int GA, GB, GN;
static int addt[MAXG][MAXG], subt[MAXG][MAXG];

/* Z_a x Z_b, element x = x1*b + x2. */
static void set_group(int a, int b) {
    GA = a;
    GB = b;
    GN = a * b;
    for (int x = 0; x < GN; x++) {
        int x1 = x / b, x2 = x % b;
        for (int y = 0; y < GN; y++) {
            int y1 = y / b, y2 = y % b;
            addt[x][y] = ((x1 + y1) % a) * b + (x2 + y2) % b;
            subt[x][y] = ((x1 - y1 + a) % a) * b + (x2 - y2 + b) % b;
        }
    }
}

/* ------------------------------------------------------------ cover search */

static int S[MAXD];
static unsigned char inS[MAXG];
static int cov[MAXG];
static int uncov; /* number of nonzero g with cov[g] == 0 */

static inline void cov_add(int g) {
    if (cov[g]++ == 0) uncov--;
}
static inline void cov_del(int g) {
    if (--cov[g] == 0) uncov++;
}

static void remove_elem(int i) {
    int x = S[i];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        cov_del(subt[x][S[j]]);
        cov_del(subt[S[j]][x]);
    }
}

static void insert_elem(int i) {
    int x = S[i];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        cov_add(subt[x][S[j]]);
        cov_add(subt[S[j]][x]);
    }
}

static void reset_state(void) {
    memset(cov, 0, sizeof(cov[0]) * (size_t)GN);
    memset(inS, 0, (size_t)GN);
    uncov = GN - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int t;
        do t = 1 + rndint(GN - 1); while (inS[t]);
        S[i] = t;
        inS[t] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) cov_add(subt[S[i]][S[j]]);
}

/* One annealing run. Returns 1 when S covers all differences; 0 on failure or timeout. */
static int anneal(long iters, double T0, double T1, double until) {
    reset_state();
    if (uncov == 0) return 1;
    double T = T0;
    double f = pow(T1 / T0, 1.0 / (double)iters);
    for (long it = 0; it < iters; it++) {
        if ((it & 1023) == 0 && now() > until) return 0;
        int i = 1 + rndint(d - 1);
        int old = S[i];
        int before = uncov;
        remove_elem(i);
        inS[old] = 0;
        int t;
        do t = 1 + rndint(GN - 1); while (inS[t]);
        S[i] = t;
        inS[t] = 1;
        insert_elem(i);
        int delta = uncov - before;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            if (uncov == 0) return 1;
        } else {
            remove_elem(i);
            inS[t] = 0;
            S[i] = old;
            inS[old] = 1;
            insert_elem(i);
        }
        T *= f;
    }
    return 0;
}

/* ------------------------------------------------------------ graph build / check */

static int vdeg[MAXV], vadj[MAXV][MAXD];

static void add_e(int u, int v) {
    vadj[u][vdeg[u]++] = v;
    vadj[v][vdeg[v]++] = u;
}

/* Build the Haar graph of the current group (set_group must match N) and connection set Sx. */
static int build_graph(int N, const int *Sx) {
    int n = 2 * N;
    for (int v = 0; v < n; v++) vdeg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_e(x, N + addt[x][Sx[i]]);
    return n;
}

/* BFS from every vertex: all vertices must be reached within D steps. */
static int check_graph(int n) {
    static int dist[MAXV], q[MAXV];
    for (int v = 0; v < n; v++)
        if (vdeg[v] > d) return 0;
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < vdeg[v]; i++) {
                int u = vadj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    q[t++] = u;
                }
            }
        }
        if (t != n) return 0;
    }
    return 1;
}

static void print_graph(int n) {
    long m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < vdeg[u]; i++)
            if (u < vadj[u][i]) m++;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < vdeg[u]; i++)
            if (u < vadj[u][i]) printf("%d %d\n", u, vadj[u][i]);
}

/* K_{d,d}: valid for D >= 2. */
static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ------------------------------------------------------------ main */

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

    int sn = 0, sm = 0, start_n = 0;
    if (scanf("%d %d", &sn, &sm) == 2) start_n = sn;
    while (getchar() != EOF) {
    }

    if (D != 3 || d < 3 || d > MAXD) {
        if (D >= 2 && d >= 1 && d <= MAXD) print_complete();
        else printf("0 0\n");
        return 0;
    }

    int Nmax = d * (d - 1) + 1;
    if (Nmax > MAXG) Nmax = MAXG;
    int N = start_n / 2 + 1;
    if (N < d + 1) N = d + 1;

    int bestN = 0, bestA = 1, bestB = 1;
    int bestS[MAXD];

    while (N <= Nmax) {
        double remain = t_end - now();
        if (remain <= 0.2) break;
        double until = now() + remain * 0.6;

        int ga[64], gb[64], ng = 0;
        for (int a = 1; a * a <= N; a++) {
            if (N % a) continue;
            int b = N / a;
            if (b % a == 0 && ng < 64) {
                ga[ng] = a;
                gb[ng] = b;
                ng++;
            }
        }

        int found = 0;
        while (!found && now() < until && ng > 0) {
            int g = rndint(ng);
            set_group(ga[g], gb[g]);
            if (anneal(ITERS, 1.5, 0.05, until)) {
                found = 1;
                bestN = N;
                bestA = ga[g];
                bestB = gb[g];
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!found) break;
        N++;
    }

    if (bestN > 0) {
        set_group(bestA, bestB);
        int n = build_graph(bestN, bestS);
        if (check_graph(n)) {
            print_graph(n);
            return 0;
        }
    }
    print_complete();
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid

    if D != 3 or d < 3 or d > 40:
        return best
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start,
                         timeout=budget + 5)
        out = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return best

    if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
        best = out
    return best
