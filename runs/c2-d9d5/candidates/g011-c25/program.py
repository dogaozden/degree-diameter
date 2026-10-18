"""Blocked affine lifts over general semidirect groups Z_m x|_r Z_k.

Change from the parent: the affine group F_q x| H is replaced by every semidirect
product Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1), which covers all group orders
and non-field structure. The C engine enumerates such groups for each order N,
samples a few per order, and binary-searches the order with simulated annealing over
voltages, for B in {3, 1, 2} orbits per side.

Vertices: L_(i,g) and R_(j,x) for orbits i, j < B and group elements g, x.
Dart (i,t) with voltage v joins L_(i,g) to R_(tgt[i][t], g*v). Left translations are
automorphisms, transitive on each orbit, so BFS from the 2B orbit representatives
decides the diameter. Each dart slot is a permutation of the B orbits, so every
vertex has degree d, and connectivity of the base is enforced. The C engine checks
simplicity and, for small graphs, a full BFS before printing. Python validates the
result with lib.is_valid and keeps a valid fallback (PG incidence, Araujo-Lopez, or K_{d,d}).
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Blocked lifts over Z_m x|_r Z_k with B orbits per side.
 * Usage: prog d D seed time_limit lo3 hi3 lo1 hi1 lo2 hi2
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4800
#define MAXD 32
#define MAXB 3
#define MAXG 40000
#define TMPG 40000
#define VMAX (2 * MAXB * MAXN)
#define ITERS 5000

typedef struct { int m, k, r, N; } Grp;

static int d, D, B, M, K, N;
static int rp[MAXN];
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int stamp_ = 0;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static void set_group(int m, int k, int r) {
    M = m;
    K = k;
    N = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        rp[b] = (int)p;
        p = p * r % m;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e); element index = a*K + b. */
static inline int gmul(int x, int y) {
    int a = x / K, b = x - a * K, c = y / K, e = y - c * K;
    int na = (a + rp[b] * c) % M;
    int nb = (b + e) % K;
    return na * K + nb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K, b = x - a * K;
    int nb = (K - b) % K;
    int na = (rp[nb] * a) % M;
    na = (M - na) % M;
    return na * K + nb;
}

/* ------------------------------------------------------------ lift state */

static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int vis[VMAX], que[VMAX];

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < N; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

static void build_inc(void) {
    for (int j = 0; j < B; j++) {
        int c = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++)
                if (tgt[i][t] == j && c < MAXD) {
                    incI[j][c] = i;
                    incT[j][c] = t;
                    c++;
                }
    }
}

static int connected_pattern(void) {
    int par[2 * MAXB];
    for (int i = 0; i < 2 * B; i++) par[i] = i;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int a = i, b = B + tgt[i][t];
            while (par[a] != a) a = par[a];
            while (par[b] != b) b = par[b];
            if (a != b) par[a] = b;
        }
    int root = -1;
    for (int i = 0; i < 2 * B; i++) {
        int a = i;
        while (par[a] != a) a = par[a];
        if (root < 0) root = a;
        else if (a != root) return 0;
    }
    return 1;
}

/* Each dart slot t is a permutation of the B orbits, so each right orbit gets d darts. */
static int random_pattern(void) {
    for (int tries = 0; tries < 200; tries++) {
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i];
                p[i] = p[r];
                p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (connected_pattern()) {
            build_inc();
            return 1;
        }
    }
    return 0;
}

/* Darts of the same (i, target) class need distinct voltages. */
static int ok_volt(int i, int t, int x, int lim) {
    for (int t2 = 0; t2 < lim; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(void) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

/* BFS to depth D from src; returns the number of vertices reached. */
static int reach_from(int src) {
    int BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w - j * N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Total number of vertices not within D of the 2B orbit representatives. */
static long cover_cost(void) {
    int V = 2 * B * N, BN = B * N;
    long c = 0;
    for (int i = 0; i < B; i++) c += V - reach_from(i * N);
    for (int j = 0; j < B; j++) c += V - reach_from(BN + j * N);
    return c;
}

/* Simulated annealing over voltages for the current group and B. */
static int search_group(double until) {
    while (now() < until) {
        if (!random_pattern()) return 0;
        int fail = 0;
        for (int i = 0; i < B && !fail; i++)
            for (int t = 0; t < d && !fail; t++) {
                int x = -1;
                for (int tr = 0; tr < 4000; tr++) {
                    int c = rndint(N);
                    if (ok_volt(i, t, c, t)) { x = c; break; }
                }
                if (x < 0) fail = 1;
                else set_dart(i, t, x);
            }
        if (fail) continue;
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int i = rndint(B), t = rndint(d);
            int x = rndint(N);
            if (x == vol[i][t] || !ok_volt(i, t, x, d)) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else set_dart(i, t, old);
        }
        if (cost == 0 && simple_state()) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidate groups */

static Grp tmpG[TMPG];
static Grp Gl[MAXG];
static int nG = 0;

/* For each order n in [lo, hi], keep up to 4 random semidirect products Z_m x| Z_k. */
static void collect(int lo, int hi) {
    nG = 0;
    for (int n = lo; n <= hi; n++) {
        int nt = 0;
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (nt < TMPG) { Grp g = {1, k, 0, n}; tmpG[nt++] = g; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                if (nt < TMPG) { Grp g = {m, k, r, n}; tmpG[nt++] = g; }
            }
        }
        int take = nt < 4 ? nt : 4;
        for (int s = 0; s < take && nG < MAXG; s++) {
            int j = s + rndint(nt - s);
            Grp tmp = tmpG[s];
            tmpG[s] = tmpG[j];
            tmpG[j] = tmp;
            Gl[nG++] = tmpG[s];
        }
    }
}

/* ------------------------------------------------------------ best record */

static int bestTotal = 0, bestB = 0;
static Grp bestG;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static int probe(int idx, double until) {
    Grp g = Gl[idx];
    set_group(g.m, g.k, g.r);
    if (!search_group(until)) return 0;
    int total = 2 * B * g.N;
    if (total > bestTotal) {
        bestTotal = total;
        bestB = B;
        bestG = g;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                bestTgt[i][t] = tgt[i][t];
                bestVol[i][t] = vol[i][t];
            }
    }
    return 1;
}

/* Binary search over the sorted candidate list, then extend upward. */
static void phase(int b, int lo, int hi, double until) {
    if (lo > hi || now() >= until) return;
    B = b;
    collect(lo, hi);
    if (nG == 0) return;
    int a = 0, z = nG - 1, found = -1, foundN = 0;
    while (a <= z && now() < until) {
        int mid = (a + z) / 2;
        double rem = until - now();
        double slice = 0.3 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (probe(mid, now() + slice)) {
            if (Gl[mid].N > foundN) { foundN = Gl[mid].N; found = mid; }
            a = mid + 1;
        } else {
            z = mid - 1;
        }
    }
    if (found < 0) return;
    int fails = 0;
    for (int idx = found + 1; idx < nG && fails < 2 && now() < until; idx++) {
        if (Gl[idx].N <= foundN) continue;
        double rem = until - now();
        double slice = 0.5 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (probe(idx, now() + slice)) {
            foundN = Gl[idx].N;
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

static int adj[VMAX][MAXD];

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo3 = atoi(argv[5]), hi3 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    int lo2 = atoi(argv[9]), hi2 = atoi(argv[10]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi3 > MAXN - 1) hi3 = MAXN - 1;
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (hi2 > MAXN - 1) hi2 = MAXN - 1;
    if (lo3 < 2 * d) lo3 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;
    if (lo2 < 2 * d) lo2 = 2 * d;

    double span = t_end - t0;
    if (lo3 <= hi3) phase(3, lo3, hi3, t0 + 0.4 * span);
    if (lo1 <= hi1) phase(1, lo1, hi1, t0 + 0.7 * span);
    if (lo2 <= hi2) phase(2, lo2, hi2, t0 + 0.85 * span);
    if (bestTotal > 0) {
        int hi = bestB == 3 ? hi3 : (bestB == 1 ? hi1 : hi2);
        int lo = bestG.N + 1;
        if (lo <= hi) phase(bestB, lo, hi, t_end);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    B = bestB;
    set_group(bestG.m, bestG.k, bestG.r);
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    build_inc();
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int BN = B * N, V = 2 * BN, E = BN * d;
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v - i * N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = w - BN - j * N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Simplicity: no repeated neighbour. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adj[v][k] == adj[v][l]) {
                    printf("0 0\n");
                    return 0;
                }

    /* Full diameter check when the graph is small enough. */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adj[v][t]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Leave room for the one-time C compile and the Python checks.
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo3 = max(2 * d, best[0] // 6 + 1, mb // 24)
        hi3 = mb // 6
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        lo2 = max(2 * d, mb // 16)
        hi2 = mb // 4
        if budget > 4.0 and (lo3 <= hi3 or lo1 <= hi1 or lo2 <= hi2):
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2),
                                  lo3, hi3, lo1, hi1, lo2, hi2],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
