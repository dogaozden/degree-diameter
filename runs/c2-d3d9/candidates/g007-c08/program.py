"""Bold variant: bi-Cayley scan plus cubic-style group lifts with a vertex-transitive fiber check.

Two phases share one C engine and one run_c call:
  Phase 1 (about 55% of the budget) is the parent's bi-Cayley scan over metacyclic
    groups Z_m x| Z_k with connection sets of size d. It sets the fallback order.
  Phase 2 (the rest) is new. It searches lifts of a small base multigraph with
    KB base vertices per side and d darts per base vertex. Each dart carries a
    group voltage. The lift is a G-invariant graph, so the diameter check only
    needs BFS from one vertex per fiber (2*KB BFS runs). Simulated annealing
    minimises the number of unreached pairs over permutations and voltages.
    Candidate orders are just above the best order found so far, and each
    candidate is retried with doubling time slices.

Every graph is verified by a full BFS from every vertex and checked for duplicate
edges before it is stored. Python keeps the known start unless the C result is
larger and passes lib.is_valid. Beating the record 506 is hard, and this search
may not get there. The fallback keeps the score from dropping below the parent's
result when phase 1 reaches the same order.
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

#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXDEG 16
#define MAXGRP 8192
#define MAXK 8
#define LMAXV (2 * MAXK * MAXG)
#define LMAXE (LMAXV * MAXDEG / 2)
#define BIGC 1000000000L

static int d, D;

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
static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

static void enum_groups(int n) {
    ngroups = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1 && ngroups < MAXGRP) {
                    groups[ngroups].m = 1;
                    groups[ngroups].k = k;
                    groups[ngroups].r = 0;
                    ngroups++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngroups < MAXGRP) {
                    groups[ngroups].m = m;
                    groups[ngroups].k = k;
                    groups[ngroups].r = r;
                    ngroups++;
                }
            }
        }
    }
}

static int MT[MAXG * MAXG];
static int INV[MAXG];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
    static int rp[MAXG];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- explicit graphs */

static int adjl[LMAXV][MAXDEG];
static int degl[LMAXV];
static int outEU[LMAXE], outEV[LMAXE];
static int outV = 0, outM = 0;

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

static int vdist[LMAXV], vq[LMAXV];

static int verify_adj(int V) {
    for (int v = 0; v < V; v++)
        if (degl[v] < 1 || degl[v] > d) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) vdist[i] = -1;
        int head = 0, tail = 0;
        vdist[s] = 0;
        vq[tail++] = s;
        while (head < tail) {
            int v = vq[head++];
            int dv = vdist[v];
            if (dv >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (vdist[u] < 0) { vdist[u] = dv + 1; vq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

/* Store the explicit graph on V vertices (adjl/degl) if valid and larger than the best so far. */
static int commit(int V) {
    if (V <= outV) return 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            for (int j = 0; j < i; j++)
                if (adjl[u][i] == adjl[u][j]) return 0;
    if (!verify_adj(V)) return 0;
    int m = 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++) {
            int w = adjl[u][i];
            if (u < w) { outEU[m] = u; outEV[m] = w; m++; }
        }
    outV = V;
    outM = m;
    return 1;
}

/* ---------------------------------------------------------- phase 1: bi-Cayley scan */

static int dist_[MAXV], queue_[MAXV];

static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

static int search_n(int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    int S[MAXDEG];
    while (now() < until) {
        for (int gi = 0; gi < ngroups; gi++) {
            if (now() >= until) break;
            build_group(groups[gi]);
            for (int t = 0; t < 200; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    bestN = n;
                    bestG = groups[gi];
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

static void phase1(int nlo, double until) {
    if (d < 2 || D < 2) return;
    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;
    double slice = (until - now()) / 40.0;
    if (slice < 0.5) slice = 0.5;
    if (slice > 3.0) slice = 3.0;
    for (int n = nstart; n <= nmax && now() < until; n++) {
        double u = now() + slice;
        if (u > until) u = until;
        search_n(n, u);
    }
    if (bestN > 0) {
        int n = bestN;
        build_group(bestG);
        for (int v = 0; v < 2 * n; v++) degl[v] = 0;
        for (int x = 0; x < n; x++)
            for (int i = 0; i < d; i++) {
                int y = MT[x * n + bestS[i]];
                add_e(x, n + y);
            }
        commit(2 * n);
    }
}

/* ---------------------------------------------------------- phase 2: group lifts */

static int KB = 1;
static int PP[MAXDEG][MAXK];   /* PP[t][i]: base B vertex joined to base A vertex i in layer t */
static int QQ[MAXDEG][MAXK];   /* inverse of PP[t] */
static int WW[MAXDEG][MAXK];   /* voltage of that dart */
static int ldist[LMAXV], lque[LMAXV];

/* Number of vertices within distance D of src in the current lift. */
static int lift_reach(int src) {
    int n = NN, k = KB, V = 2 * k * n, half = k * n;
    for (int i = 0; i < V; i++) ldist[i] = -1;
    int head = 0, tail = 0;
    ldist[src] = 0;
    lque[tail++] = src;
    while (head < tail) {
        int v = lque[head++];
        int dv = ldist[v];
        if (dv >= D) continue;
        if (v < half) {
            int i = v / n, x = v - i * n;
            for (int t = 0; t < d; t++) {
                int u = half + PP[t][i] * n + MT[x * n + WW[t][i]];
                if (ldist[u] < 0) { ldist[u] = dv + 1; lque[tail++] = u; }
            }
        } else {
            int w = v - half;
            int j = w / n, y = w - j * n;
            for (int t = 0; t < d; t++) {
                int i = QQ[t][j];
                int x = MT[y * n + INV[WW[t][i]]];
                int u = i * n + x;
                if (ldist[u] < 0) { ldist[u] = dv + 1; lque[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Cost = total unreached pairs from one source per fiber. Zero means a valid lift. */
static long lift_cost(void) {
    int n = NN, k = KB;
    for (int t = 0; t < d; t++)
        for (int t2 = t + 1; t2 < d; t2++)
            for (int i = 0; i < k; i++)
                if (PP[t][i] == PP[t2][i] && WW[t][i] == WW[t2][i]) return BIGC;
    long V = 2L * k * n, c = 0;
    for (int i = 0; i < k; i++) c += V - lift_reach(i * n);
    for (int j = 0; j < k; j++) c += V - lift_reach(k * n + j * n);
    return c;
}

static void lift_random_init(void) {
    int k = KB, n = NN;
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[r]; perm[r] = tmp;
        }
        for (int i = 0; i < k; i++) {
            PP[t][i] = perm[i];
            QQ[t][perm[i]] = i;
            WW[t][i] = rndint(n);
        }
    }
}

static void lift_swap(int t, int a, int b) {
    int ja = PP[t][a], jb = PP[t][b];
    PP[t][a] = jb;
    PP[t][b] = ja;
    QQ[t][jb] = a;
    QQ[t][ja] = b;
}

static void lift_build_adj(void) {
    int n = NN, k = KB, half = k * n;
    for (int v = 0; v < 2 * k * n; v++) degl[v] = 0;
    for (int i = 0; i < k; i++)
        for (int x = 0; x < n; x++)
            for (int t = 0; t < d; t++) {
                int u = i * n + x;
                int v = half + PP[t][i] * n + MT[x * n + WW[t][i]];
                add_e(u, v);
            }
}

static void search_lift(int k, int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return;
    KB = k;
    const long steps = 40000;
    while (now() < until) {
        build_group(groups[rndint(ngroups)]);
        lift_random_init();
        long cur = lift_cost();
        for (long s = 0; s < steps && cur > 0; s++) {
            if ((s & 127) == 0 && now() >= until) break;
            double T = 1.0 * (1.0 - (double)s / (double)steps) + 0.03;
            if (k > 1 && rndint(2) == 0) {
                int t = rndint(d), a = rndint(k), b = rndint(k);
                if (a == b) continue;
                lift_swap(t, a, b);
                long nc = lift_cost();
                if (nc <= cur || unif() < exp(-(double)(nc - cur) / T)) cur = nc;
                else lift_swap(t, a, b);
            } else {
                int t = rndint(d), i = rndint(k);
                int old = WW[t][i];
                int nv = rndint(n);
                if (nv == old) continue;
                WW[t][i] = nv;
                long nc = lift_cost();
                if (nc <= cur || unif() < exp(-(double)(nc - cur) / T)) cur = nc;
                else WW[t][i] = old;
            }
        }
        if (cur == 0) {
            lift_build_adj();
            if (commit(2 * k * n)) return;
        }
    }
}

static void phase2(int kmax, double until, long moore) {
    if (d < 3) return;
    long lowL = (long)(0.45 * (double)moore);
    if (outV > lowL) lowL = outV;
    int cK[64], cN[64], cV[64];
    int nc = 0;
    for (int k = 1; k <= kmax && k <= MAXK; k++) {
        long nlo = lowL / (2L * k) + 1;
        for (long n = nlo; n < nlo + 6; n++) {
            if (n > MAXG) break;
            long V = 2L * k * n;
            if (V > moore) break;
            if (nc < 64) {
                cK[nc] = k;
                cN[nc] = (int)n;
                cV[nc] = (int)V;
                nc++;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        int j = i;
        while (j > 0 && cV[j - 1] > cV[j]) {
            int tV = cV[j]; cV[j] = cV[j - 1]; cV[j - 1] = tV;
            int tK = cK[j]; cK[j] = cK[j - 1]; cK[j - 1] = tK;
            int tN = cN[j]; cN[j] = cN[j - 1]; cN[j - 1] = tN;
            j--;
        }
    }
    double slice = 0.5;
    while (now() < until) {
        int any = 0;
        for (int c = 0; c < nc && now() < until; c++) {
            if (cV[c] <= outV) continue;
            double u = now() + slice;
            if (u > until) u = until;
            search_lift(cK[c], cN[c], u);
            any = 1;
        }
        slice *= 2;
        if (!any) break;
    }
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed budget nlo kmax\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);
    int kmax = atoi(argv[6]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    if (kmax > MAXK) kmax = MAXK;
    if (kmax < 1) kmax = 1;

    double t0 = now();
    long moore = moore_bound();
    phase1(nlo, t0 + 0.55 * budget);
    phase2(kmax, t0 + 0.93 * budget, moore);

    if (outV <= 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", outV, outM);
    for (int e = 0; e < outM; e++) printf("%d %d\n", outEU[e], outEV[e]);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 2.0:
        return best

    # Lower bound for the phase-1 scan, as in the parent.
    nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
    if nlo > moore // 2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo, 3],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
