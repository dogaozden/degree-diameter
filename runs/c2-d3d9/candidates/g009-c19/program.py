"""Voltage-lift search over metacyclic groups, with the old Cayley/grow engine removed.

Construction: a random d-regular bipartite base multigraph with P vertices per side and
darts (i, j, g), plus a metacyclic group G = Z_m x| Z_k of order N. The lift has vertices
A(i,x), B(j,y) for x, y in G, and edges A(i,x) -- B(j, x*g) for each dart. Left
multiplication is an automorphism that is transitive on each fibre, so the diameter check
needs only BFS from the 2P representatives A(i,e), B(j,e). Voltages are annealed to remove
all unreached pairs. Each success raises the target order by at least 2. Every result is
re-verified by a full check before it is kept, and the Python side keeps a valid fallback.
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

#define MAXV 4096
#define MAXD 12
#define MAXP 4
#define MAXE 70000
#define MAXDART (MAXD * MAXP)
#define STALL 4000

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

/* ------------------------------------------------------------ best graph */

static int best_n = 0, best_m = 0;
static int bu[MAXE], bv[MAXE];

static void store_best(int n, int m, const int *eu, const int *ev) {
    best_n = n;
    best_m = m;
    memcpy(bu, eu, sizeof(int) * (size_t)m);
    memcpy(bv, ev, sizeof(int) * (size_t)m);
}

/* ------------------------------------------------------------ generic BFS / check */

static int gdeg[MAXV], gadj[MAXV * MAXD], gdist[MAXV], gq[MAXV], gcol[MAXV], gstk[MAXV];

/* Number of vertices within distance lim of s (BFS on adjacency with given stride). */
static int bfs_reach(int n, const int *adj, const int *deg, int stride, int s, int lim,
                     int *dist, int *q) {
    for (int v = 0; v < n; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[s] = 0;
    q[tail++] = s;
    while (head < tail) {
        int v = q[head++];
        if (dist[v] >= lim) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * stride + i];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                q[tail++] = u;
            }
        }
    }
    return tail;
}

/* Full check: simple, degree <= d, bipartite, diameter <= D. */
static int check_graph(int n, int m, const int *eu, const int *ev) {
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return 0;
    for (int v = 0; v < n; v++) gdeg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (gdeg[u] >= d || gdeg[v] >= d) return 0;
        gadj[u * MAXD + gdeg[u]++] = v;
        gadj[v * MAXD + gdeg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int i = 0; i < gdeg[v]; i++)
            for (int j = 0; j < i; j++)
                if (gadj[v * MAXD + i] == gadj[v * MAXD + j]) return 0;
    for (int v = 0; v < n; v++) gcol[v] = -1;
    for (int s = 0; s < n; s++) {
        if (gcol[s] >= 0) continue;
        int head = 0, tail = 0;
        gcol[s] = 0;
        gstk[tail++] = s;
        while (head < tail) {
            int v = gstk[head++];
            for (int i = 0; i < gdeg[v]; i++) {
                int u = gadj[v * MAXD + i];
                if (gcol[u] < 0) {
                    gcol[u] = 1 - gcol[v];
                    gstk[tail++] = u;
                } else if (gcol[u] == gcol[v]) {
                    return 0;
                }
            }
        }
    }
    for (int s = 0; s < n; s++)
        if (bfs_reach(n, gadj, gdeg, MAXD, s, D, gdist, gq) != n) return 0;
    return 1;
}

static void read_start(void) {
    static int eu[MAXE], ev[MAXE];
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return;
    for (int e = 0; e < m; e++)
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) return;
    if (check_graph(n, m, eu, ev)) store_best(n, m, eu, ev);
}

/* ------------------------------------------------------------ metacyclic groups */

static int P, N;            /* base vertices per side, group order */
static int GM, GK, GR;      /* group Z_m x| Z_k with r */
static int *MT = NULL;      /* MT[x*N+y] = x*y */
static int mt_cap = 0;
static int GINV[MAXV];
static int RP[MAXV];

static void build_group(int n_) {
    int divs[64], nd = 0;
    for (int m = 1; m <= n_ && nd < 64; m++)
        if (n_ % m == 0) divs[nd++] = m;
    int m = 1, k = n_, r = 0, ok = 0;
    for (int tries = 0; tries < 200 && !ok; tries++) {
        int mm = divs[rndint(nd)];
        int kk = n_ / mm;
        if (mm == 1) {
            m = 1; k = n_; r = 0; ok = 1;
            break;
        }
        int rr = 1 + rndint(mm - 1);
        if (gcd(rr, mm) == 1 && powmod(rr, kk, mm) == 1 % mm) {
            m = mm; k = kk; r = rr; ok = 1;
        }
    }
    GM = m; GK = k; GR = r;
    if (n_ * n_ > mt_cap) {
        MT = realloc(MT, sizeof(int) * (size_t)n_ * (size_t)n_);
        if (!MT) exit(1);
        mt_cap = n_ * n_;
    }
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < n_; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n_; y++) {
            int c = y / k, e = y % k;
            MT[x * n_ + y] = (int)(((a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < n_; x++)
        for (int y = 0; y < n_; y++)
            if (MT[x * n_ + y] == 0) { GINV[x] = y; break; }
}

/* ------------------------------------------------------------ lift state */

static int dart_i[MAXDART], dart_j[MAXDART], dart_g[MAXDART], dart_s[MAXDART];
static int ND;
static int LADJ[MAXV * MAXD];   /* stride d */
static int LDEG[MAXV];
static int ldist[MAXV], lq[MAXV];
static int srcs[2 * MAXP];

/* Random d-regular bipartite base on P+P vertices: dart index t = s*P + i. */
static void build_base(void) {
    for (;;) {
        int perms[MAXD][MAXP];
        for (int s = 0; s < d; s++) {
            for (int i = 0; i < P; i++) perms[s][i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = perms[s][i];
                perms[s][i] = perms[s][j];
                perms[s][j] = tmp;
            }
        }
        int reach[2 * MAXP] = {0};
        reach[0] = 1;
        for (int it = 0; it < 2 * P; it++)
            for (int s = 0; s < d; s++)
                for (int i = 0; i < P; i++) {
                    int j = perms[s][i];
                    if (reach[i]) reach[P + j] = 1;
                    if (reach[P + j]) reach[i] = 1;
                }
        int ok = 1;
        for (int v = 0; v < 2 * P; v++) if (!reach[v]) ok = 0;
        if (!ok) continue;
        ND = d * P;
        for (int s = 0; s < d; s++)
            for (int i = 0; i < P; i++) {
                int t = s * P + i;
                dart_i[t] = i;
                dart_j[t] = perms[s][i];
                dart_s[t] = s;
            }
        return;
    }
}

/* Voltage for dart t not equal to any voltage of a parallel dart u < lim. -1 if none found. */
static int pick_voltage(int t, int lim) {
    for (int tries = 0; tries < 1000; tries++) {
        int g = rndint(N), clash = 0;
        for (int u = 0; u < lim; u++)
            if (u != t && dart_i[u] == dart_i[t] && dart_j[u] == dart_j[t] && dart_g[u] == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
    return -1;
}

/* Write the edges of dart t into LADJ. Vertex A(i,x)=i*N+x, B(j,y)=P*N+j*N+y. */
static void set_dart(int t) {
    int i = dart_i[t], j = dart_j[t], g = dart_g[t], s = dart_s[t];
    for (int x = 0; x < N; x++) {
        int y = MT[x * N + g];
        int a = i * N + x;
        int b = P * N + j * N + y;
        LADJ[a * d + s] = b;
        LADJ[b * d + s] = a;
    }
}

/* Total number of (representative, vertex) pairs at distance > D. 0 means a valid lift. */
static long eval_f(void) {
    int V = 2 * P * N;
    long f = 0;
    for (int k = 0; k < 2 * P; k++) {
        int reach = bfs_reach(V, LADJ, LDEG, d, srcs[k], D, ldist, lq);
        f += V - reach;
    }
    return f;
}

static int attempt(int p, int n_, long steps, double until) {
    P = p;
    N = n_;
    int V = 2 * P * N;
    build_group(N);
    build_base();
    for (int v = 0; v < V; v++) LDEG[v] = d;
    for (int i = 0; i < P; i++) srcs[i] = i * N;
    for (int j = 0; j < P; j++) srcs[P + j] = P * N + j * N;
    for (int t = 0; t < ND; t++) {
        int g = pick_voltage(t, t);
        if (g < 0) return 0;
        dart_g[t] = g;
    }
    for (int t = 0; t < ND; t++) set_dart(t);

    long f = eval_f(), bestf = f, stall = 0;
    for (long st = 0; st < steps && f > 0; st++) {
        if ((st & 127) == 0 && now() > until) break;
        double T = 2.0 * exp(-3.0 * (double)st / (double)steps) + 0.05;
        int t = rndint(ND);
        int old = dart_g[t];
        int ng = pick_voltage(t, ND);
        if (ng < 0 || ng == old) continue;
        dart_g[t] = ng;
        set_dart(t);
        long nf = eval_f();
        if (nf <= f || rnd01() < exp(-(double)(nf - f) / T)) {
            f = nf;
            if (f < bestf) { bestf = f; stall = 0; }
            else stall++;
        } else {
            dart_g[t] = old;
            set_dart(t);
            stall++;
        }
        if (stall > STALL) break;
    }
    if (f != 0) return 0;

    static int eu[MAXE], ev[MAXE];
    int E = 0;
    for (int a = 0; a < P * N; a++)
        for (int s = 0; s < d; s++) {
            if (E >= MAXE) return 0;
            eu[E] = a;
            ev[E] = LADJ[a * d + s];
            E++;
        }
    if (V > best_n && check_graph(V, E, eu, ev)) {
        store_best(V, E, eu, ev);
        return 1;
    }
    return 0;
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
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    read_start();
    if (best_n == 0) {
        static int eu[MAXE], ev[MAXE];
        int E = 0;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) { eu[E] = a; ev[E] = d + b; E++; }
        if (check_graph(2 * d, E, eu, ev)) store_best(2 * d, E, eu, ev);
    }

    long moore = moore_bound();
    if (d >= 2 && D >= 2) {
        while (now() < t_end) {
            long T = best_n + 2;
            if (T > moore || T > MAXV) break;
            int p = 1 + rndint(4);
            long n_ = (T + 2 * p - 1) / (2 * p) + rndint(2);
            if (n_ < d) n_ = d;
            if (2L * p * n_ > moore || 2L * p * n_ > MAXV) {
                p = 1;
                n_ = (T + 1) / 2;
                if (n_ < d) n_ = d;
                if (2 * n_ > moore || 2 * n_ > MAXV) continue;
            }
            attempt(p, (int)n_, 40000, t_end);
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", bu[e], bv[e]);
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
    if not lib.is_valid(*best, d, D):
        best = lib.haar_graph(d, range(d))
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing to search for
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and d >= 2 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
