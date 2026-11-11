"""Semidirect-product lifts for the bipartite degree-diameter problem (search version 2).

Family: G = Z_m x|_r Z_k (element (a, b) coded as a*k+b, product (a,b)(c,e) = (a + r^b c, b+e)),
with r^k = 1 mod m. The group is random for each attempt, so cyclic, abelian and
non-abelian groups are all tried. B left orbits and B right orbits, B in 1..6. Dart slot t
of left orbit i goes to right orbit sigma_t(i), where sigma_t is a random permutation.
Each right orbit then gets exactly d darts, so the base is d-regular and bipartite.

Left multiplication by G is an automorphism, so BFS from the 2B orbit representatives
decides the diameter. A ratchet keeps raising the vertex-count target after each success.
For each B, a failed group order caps the search below it. Python checks the output
with lib.is_valid and falls back to the valid constructions.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Semidirect-product lifts Z_m x|_r Z_k with B orbits per side.
 * Usage: prog d D seed time_limit lo_total hi_total
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 6
#define MAXD 32
#define MAXN 4800
#define MAXV (2 * MAXB * MAXN)

static int d, D;
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, GN;
static int PWR[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        PWR[b] = (int)p;
        p = (p * r) % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long)PWR[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - ((long)PWR[nb] * a) % GM) % GM);
    return na * GK + nb;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long modpow(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Random group of order N: random divisor k, random r with r^k = 1 (mostly non-trivial). */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    static int divs[MAXN];
    int nd = 0;
    for (int k = 1; k <= N; k++)
        if (N % k == 0 && N / k >= 2) divs[nd++] = k;
    if (nd == 0) return 0;
    int k = divs[rndint(nd)];
    int m = N / k, r = 1;
    if (k >= 2 && m >= 3 && rnd01() < 0.8) {
        for (int tries = 0; tries < 400; tries++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) != 1) continue;
            if (modpow(c, k, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *pm = m;
    *pk = k;
    *pr = r;
    return 1;
}

/* ------------------------------------------------------------ lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestN, bestGM, bestGK, bestGR;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static int base_connected(int B) {
    int seenL[MAXB], seenR[MAXB];
    for (int i = 0; i < B; i++) {
        seenL[i] = 0;
        seenR[i] = 0;
    }
    seenL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int j = tgt[i][t];
                if (seenL[i] && !seenR[j]) { seenR[j] = 1; changed = 1; }
                if (seenR[j] && !seenL[i]) { seenL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!seenL[i] || !seenR[i]) return 0;
    return 1;
}

static int set_incidence(int B) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= d) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != d) return 0;
    return 1;
}

static int random_pattern(int B) {
    for (int attempt = 0; attempt < 2000; attempt++) {
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
        if (base_connected(B) && set_incidence(B)) {
            curB = B;
            return 1;
        }
    }
    return 0;
}

/* Darts of the same (left orbit, target) class need distinct voltages. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* BFS up to depth D from src; returns number of vertices reached. */
static int bfs_count(int src) {
    int N = GN, BN = curB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices, summed over the 2B orbit representatives. */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Annealing over voltages; each restart draws a fresh base pattern.
 * Returns 1 with a simple cost-0 state in tgt/vol, 0 on timeout or failure. */
static int search_group(double until, int iters) {
    int N = GN, B = curB;
    while (now() < until) {
        if (!random_pattern(B)) return 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x = 0, tries = 0;
                do {
                    x = rndint(N);
                    tries++;
                } while (!valid_value(i, t, x, t) && tries < 20000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x = -1;
            for (int tries = 0; tries < 1000; tries++) {
                int cand = rndint(N);
                if (valid_value(i, t, cand, d)) {
                    x = cand;
                    break;
                }
            }
            if (x < 0) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0 && simple_state(B)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo_total = atol(argv[5]);
    long hi_total = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    long T = lo_total - 1;
    if (T < 0) T = 0;
    int failUB[MAXB + 1];
    for (int b = 0; b <= MAXB; b++) failUB[b] = MAXN;

    while (now() < t_end - 0.3) {
        int fb[MAXB], nfb = 0;
        long Nmin_b[MAXB + 1], Nmax_b[MAXB + 1];
        for (int B = 1; B <= MAXB; B++) {
            long twoB = 2L * B;
            long nmin = (T + 1 + twoB - 1) / twoB;
            if (nmin < d + 1) nmin = d + 1;
            long nmax = hi_total / twoB;
            if (nmax > MAXN - 1) nmax = MAXN - 1;
            if (nmax > failUB[B] - 1) nmax = failUB[B] - 1;
            Nmin_b[B] = nmin;
            Nmax_b[B] = nmax;
            if (nmin <= nmax) fb[nfb++] = B;
        }
        if (nfb == 0) break;
        int B = fb[rndint(nfb)];
        int N = (int)(Nmin_b[B] + rndint((int)(Nmax_b[B] - Nmin_b[B] + 1)));
        int m, k, r;
        if (!pick_group(N, &m, &k, &r)) {
            failUB[B] = N;
            continue;
        }
        double rem = t_end - now();
        double slice = rem * 0.12;
        if (slice < 1.5) slice = 1.5;
        if (slice > 5.0) slice = 5.0;
        if (slice > rem) slice = rem;
        setup_group(m, k, r);
        curB = B;
        if (search_group(now() + slice, 3000)) {
            long total = 2L * B * N;
            if (total > T) T = total;
            bestTotal = (int)total;
            bestB = B;
            bestN = N;
            bestGM = m;
            bestGK = k;
            bestGR = r;
            for (int i = 0; i < B; i++)
                for (int t = 0; t < d; t++) {
                    bestTgt[i][t] = tgt[i][t];
                    bestVol[i][t] = vol[i][t];
                }
        } else {
            if (N < failUB[B]) failUB[B] = N;
        }
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph from its stored state. */
    int B = bestB;
    setup_group(bestGM, bestGK, bestGR);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[MAXV][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
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

    /* Full diameter check from every vertex when cheap. */
    if (V <= 4000) {
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
                        if (vis[u] != stamp_) {
                            vis[u] = stamp_;
                            que[tail++] = u;
                        }
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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
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

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Semidirect-product lifts with B = 1..6 orbits per side, found by the C search.
    if 2 <= d <= 32 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Keep room for the one-time C compile, the C run and the Python checks.
        budget = 0.75 * time_limit - (time.monotonic() - t0) - 3.0
        if budget > 4.0 and best[0] + 1 <= mb:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2), best[0] + 1, mb],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
