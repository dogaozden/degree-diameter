"""Multi-orbit bi-voltage lifts over metacyclic groups, found by simulated annealing.

New idea: a bipartite d-regular graph of order 2*a*N is the lift of a base bipartite
d-regular multigraph on a + a vertices, with voltages in a group G of order N. Vertex
(i, x) of side A is joined to (j, x*g) for every dart (i, j, g). The parent uses a = 1
(one Cayley-type orbit per side). With a >= 2 the graph has more orbits, which gives
more freedom.

Left multiplication is an automorphism, so the diameter check needs one BFS per base
vertex (2a BFS runs), not one per vertex. The search state is the dart list: which B
vertex each dart ends at (moves: swap endpoints, which keeps degrees) and its voltage
(move: change the voltage). The cost is the number of ordered pairs at distance > D
from the 2a block representatives, plus a large penalty for parallel darts. Simulated
annealing with restarts drives the cost to zero. The total order target T = a*N per side
is raised one step at a time while the search succeeds, and the last success is kept.
Everything is re-verified by a full BFS before printing. Python checks the result with
lib.is_valid and keeps the valid fallback.
"""
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

#define MAXT 512
#define MAXV (2 * MAXT)
#define MAXD 16
#define MAXA 8
#define MAXE (MAXA * MAXD)
#define MAXGL 4096
#define RUN_LEN 60000L

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp glist[MAXGL];
static int nglist;

static void add_group(int m, int k, int r) {
    if (nglist < MAXGL) {
        glist[nglist].m = m;
        glist[nglist].k = k;
        glist[nglist].r = r;
        nglist++;
    }
}

/* All metacyclic groups of order N: element (a, b) is coded a*k + b. */
static void enum_groups(int N) {
    nglist = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_group(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            add_group(m, k, r);
        }
    }
}

static int MT[MAXT * MAXT]; /* multiplication table of the current group */
static int INV[MAXT];
static int GN;

static void build_group(Grp G) {
    int m = G.m, k = G.k, r = G.r;
    int N = m * k;
    GN = N;
    static int rp[MAXT];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- lift state */

/* Base: A_ vertices per side, E_ = d*A_ darts. Dart e leaves A vertex e/d and
 * ends at B vertex Bj[e] with voltage Gg[e]. Each B vertex gets exactly d darts. */
static int A_, N_, E_, Vn;
static int Bj[MAXE], Gg[MAXE];
static int adj[MAXV][MAXD];
static int vis[MAXV], dist_[MAXV], que[MAXV];
static int stamp_ = 0;

/* Vertex (i, x) of side A is i*N + x; vertex (j, y) of side B is (A_+j)*N + y.
 * Edge A(i,x) -- B(j, x*g) for each dart (i, j, g). */
static void rebuild(void) {
    int a = A_, N = N_;
    int cnt[MAXA];
    for (int j = 0; j < a; j++) cnt[j] = 0;
    for (int e = 0; e < E_; e++) {
        int i = e / d, t = e % d, j = Bj[e], g = Gg[e];
        int s = cnt[j]++;
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            int v = (a + j) * N + MT[x * N + g];
            adj[u][t] = v;
            adj[v][s] = u;
        }
    }
}

static int dup_count(void) {
    int c = 0;
    for (int e = 0; e < E_; e++)
        for (int f = e + 1; f < E_; f++)
            if (e / d == f / d && Bj[e] == Bj[f] && Gg[e] == Gg[f]) c++;
    return c;
}

/* Number of ordered (source block, target) pairs not within distance D, plus a
 * penalty for parallel darts. Zero iff the lift is simple and has diameter <= D.
 * Left multiplication is an automorphism, so BFS from (block q, identity) suffices. */
static long eval_cost(void) {
    rebuild();
    long cost = (long)dup_count() * Vn;
    int nsrc = 2 * A_;
    for (int q = 0; q < nsrc; q++) {
        int src = q * N_;
        stamp_++;
        int head = 0, tail = 0, cnt = 1;
        vis[src] = stamp_;
        dist_[src] = 0;
        que[tail++] = src;
        while (head < tail) {
            int v = que[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            for (int t = 0; t < d; t++) {
                int u = adj[v][t];
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    dist_[u] = dv + 1;
                    que[tail++] = u;
                    cnt++;
                }
            }
        }
        cost += Vn - cnt;
    }
    return cost;
}

static void random_init(int a, int N) {
    A_ = a;
    N_ = N;
    E_ = a * d;
    Vn = 2 * a * N;
    int bs[MAXE];
    int p = 0;
    for (int j = 0; j < a; j++)
        for (int t = 0; t < d; t++) bs[p++] = j;
    for (int i = E_ - 1; i > 0; i--) {
        int k = rndint(i + 1);
        int tmp = bs[i];
        bs[i] = bs[k];
        bs[k] = tmp;
    }
    for (int e = 0; e < E_; e++) {
        Bj[e] = bs[e];
        Gg[e] = rndint(N);
    }
}

/* Simulated annealing on the current group. Returns 1 with a zero-cost state in
 * Bj/Gg, or 0 on time-out or when the iterations run out. */
static int anneal(long iters, double T0, double T1) {
    long cur = eval_cost();
    if (cur == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 1023) == 0 && now() > t_end) return 0;
        double temp = T0 * pow(T1 / T0, (double)it / (double)iters);
        int e1 = rndint(E_), e2 = -1, oldg = 0, oldj1 = 0, oldj2 = 0;
        int type = (A_ == 1) ? 0 : rndint(2);
        if (type == 0) {
            oldg = Gg[e1];
            Gg[e1] = rndint(N_);
        } else {
            e2 = rndint(E_ - 1);
            if (e2 >= e1) e2++;
            oldj1 = Bj[e1];
            oldj2 = Bj[e2];
            Bj[e1] = oldj2;
            Bj[e2] = oldj1;
        }
        long nc = eval_cost();
        if (nc == 0) return 1;
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
        } else {
            if (type == 0) Gg[e1] = oldg;
            else { Bj[e1] = oldj1; Bj[e2] = oldj2; }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- search over orders */

static int bestT = 0;
static int sA, sN, sE;
static Grp sG;
static int sBj[MAXE], sGg[MAXE];

/* Try to find a zero-cost lift with side order T (= a*N) until `until`. */
static int search_T(int T, double until) {
    while (now() < until) {
        int cand[MAXA], nc = 0;
        for (int a = 1; a <= MAXA; a++) {
            if (T % a) continue;
            int N = T / a;
            if (N >= d + 1 && N <= MAXT - 1) cand[nc++] = a;
        }
        if (nc == 0) return 0;
        int a = cand[rndint(nc)];
        int N = T / a;
        enum_groups(N);
        int nab[MAXGL], nn = 0;
        for (int g = 0; g < nglist; g++)
            if (glist[g].m > 1 && glist[g].r != 1) nab[nn++] = g;
        Grp G;
        if (nn > 0 && rndint(100) < 80) G = glist[nab[rndint(nn)]];
        else G = glist[rndint(nglist)];
        build_group(G);
        random_init(a, N);
        if (anneal(RUN_LEN, 2.5, 0.2)) {
            sA = a;
            sN = N;
            sE = E_;
            sG = G;
            memcpy(sBj, Bj, sizeof(int) * (size_t)E_);
            memcpy(sGg, Gg, sizeof(int) * (size_t)E_);
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- explicit graph */

static int xadj[MAXV][MAXD], xdeg[MAXV];

static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++)
        if (xdeg[v] != d) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < xdeg[v]; i++) {
                int u = xadj[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void set_complete(void) {
    int V = 2 * d;
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long moore = moore_bound();
    int Tmax = (int)(moore / 2);
    if (Tmax > MAXT - 1) Tmax = MAXT - 1;
    int T = nlo;
    if (T < d + 1) T = d + 1;

    if (d >= 2 && D >= 2) {
        while (T <= Tmax && now() < t_end) {
            if (search_T(T, t_end)) { bestT = T; T++; }
            else break;
        }
    }

    int ok = 0;
    if (bestT > 0) {
        int a = sA, N = sN, V = 2 * a * N;
        build_group(sG);
        for (int v = 0; v < V; v++) xdeg[v] = 0;
        for (int e = 0; e < sE; e++) {
            int i = e / d, j = sBj[e], g = sGg[e];
            for (int x = 0; x < N; x++) {
                int u = i * N + x;
                int v = (a + j) * N + MT[x * N + g];
                if (xdeg[u] < MAXD && xdeg[v] < MAXD) {
                    xadj[u][xdeg[u]++] = v;
                    xadj[v][xdeg[v]++] = u;
                }
            }
        }
        ok = verify_explicit(V);
        if (ok) {
            long m = 0;
            for (int u = 0; u < V; u++)
                for (int i = 0; i < xdeg[u]; i++)
                    if (u < xadj[u][i]) m++;
            printf("%d %ld\n", V, m);
            for (int u = 0; u < V; u++)
                for (int i = 0; i < xdeg[u]; i++)
                    if (u < xadj[u][i]) printf("%d %d\n", u, xadj[u][i]);
        }
    }
    if (!ok) set_complete();
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    # Lower bound on the per-side order T = a*N (half the total order).
    nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
    if nlo > moore // 2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
