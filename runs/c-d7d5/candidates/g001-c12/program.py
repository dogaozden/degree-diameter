"""Bold variant: bi-Cayley voltage lifts over semidirect groups Z_m x| Z_k, searched by hill-climbing.

Vertex-transitivity: left multiplication by any group element is an automorphism of a group lift,
so a lift is valid iff every orbit representative (2p of them) reaches all vertices within D steps.
Each check is therefore 2p BFS runs over the lift, not an all-pairs bitset computation, which allows
far more voltage/base evaluations per second than the earlier engine.

The engine grows the order one step at a time (target = best + 2p) and restarts with fresh groups and
base graphs when a target fails. build() keeps the Moore-graph or K_{d,d} fallback and only accepts an
engine result that is strictly larger and passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXP 3
#define MAXN 1600
#define MAXV 4096
#define CAPV 3200
#define STEPS 60000

static int d, D;
static int p, N, nd;
static int m_, k_, r_;
static int rp[MAXN];
static int MT[MAXN * MAXN];
static int INV[MAXN];
static int di[MAXD * MAXP], dj[MAXD * MAXP], dg[MAXD * MAXP];
static int nbr[MAXV * MAXD];
static int best_nbr[MAXV * MAXD];
static int best_V = 0, best_p = 0, best_N = 0;
static int vis[MAXV], dep[MAXV], qu[MAXV];
static int stamp = 0;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Uniformly random semidirect group Z_m x|_r Z_k of order Nn (cyclic is included). */
static int pick_group(int Nn) {
    long cnt = 0;
    int bm = -1, bk = -1, br = -1;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int k = Nn / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (bm < 0) return 0;
    m_ = bm; k_ = bk; r_ = br;
    return 1;
}

/* Multiplication table and inverses for the chosen group, element (a,b) = a*k+b. */
static void set_group(void) {
    int m = m_, k = k_, r = r_;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int c1 = y / k, e1 = y % k;
            MT[x * N + y] = (int)(((long)a1 + (long)rp[b1] * c1) % m) * k + (b1 + e1) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        int e1 = (k - b1) % k;
        int c1 = (int)((m - ((long)a1 * rp[e1]) % m) % m);
        INV[x] = c1 * k + e1;
    }
}

/* Random d-regular base multigraph on p+p vertices as d permutations; darts e = t*p + i. */
static int init_darts(void) {
    nd = d * p;
    for (int t = 0; t < d; t++) {
        int sg[MAXP];
        for (int i = 0; i < p; i++) sg[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = sg[i]; sg[i] = sg[j]; sg[j] = s;
        }
        for (int i = 0; i < p; i++) {
            int e = t * p + i;
            di[e] = i;
            dj[e] = sg[i];
        }
    }
    for (int e = 0; e < nd; e++) {
        int ok = 0;
        for (int tr = 0; tr < 200 && !ok; tr++) {
            int g = rndint(N), clash = 0;
            for (int f = 0; f < e; f++)
                if (di[f] == di[e] && dj[f] == dj[e] && dg[f] == g) { clash = 1; break; }
            if (!clash) { dg[e] = g; ok = 1; }
        }
        if (!ok) return 0;
    }
    return 1;
}

/* Adjacency of the lift. A_{i,x} = i*N+x, B_{j,y} = p*N + j*N + y.
 * Dart (i,j,g) joins A_{i,x} to B_{j,x g}. */
static void build_nbr(void) {
    int pN = p * N;
    int cntB[MAXP];
    for (int j = 0; j < p; j++) cntB[j] = 0;
    for (int e = 0; e < nd; e++) {
        int i = di[e], j = dj[e], t = e / p, g = dg[e], gi = INV[g];
        for (int x = 0; x < N; x++)
            nbr[(i * N + x) * d + t] = pN + j * N + MT[x * N + g];
        int c = cntB[j]++;
        for (int y = 0; y < N; y++)
            nbr[(pN + j * N + y) * d + c] = i * N + MT[y * N + gi];
    }
}

/* Number of vertices within distance D of src (including src). */
static int reach_count(int src) {
    stamp++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    dep[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        if (dep[v] >= D) continue;
        const int *nb = nbr + v * d;
        for (int c = 0; c < d; c++) {
            int u = nb[c];
            if (vis[u] != stamp) {
                vis[u] = stamp;
                dep[u] = dep[v] + 1;
                qu[tail++] = u;
            }
        }
    }
    return tail;
}

/* Number of (source, vertex) pairs at distance > D over orbit representatives; 0 iff valid. */
static long evaluate(void) {
    int V = 2 * p * N, pN = p * N;
    build_nbr();
    long bad = 0;
    for (int i = 0; i < p; i++) bad += V - reach_count(i * N);
    for (int j = 0; j < p; j++) bad += V - reach_count(pN + j * N);
    return bad;
}

static int attempt(long steps) {
    if (!pick_group(N)) return 0;
    set_group();
    if (!init_darts()) return 0;
    long bad = evaluate();
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) return 0;
        int e = rndint(nd);
        if (p == 1 || rnd01() < 0.7) {
            int old = dg[e], g = -1;
            for (int tr = 0; tr < 30 && g < 0; tr++) {
                int c = rndint(N);
                if (c == old) continue;
                int clash = 0;
                for (int f = 0; f < nd; f++)
                    if (f != e && di[f] == di[e] && dj[f] == dj[e] && dg[f] == c) { clash = 1; break; }
                if (!clash) g = c;
            }
            if (g < 0) continue;
            dg[e] = g;
            long nb = evaluate();
            if (nb <= bad || rnd01() < 0.02) bad = nb;
            else dg[e] = old;
        } else {
            int t = rndint(d), i1 = rndint(p), i2 = rndint(p);
            if (i1 == i2) continue;
            int e1 = t * p + i1, e2 = t * p + i2;
            int j1 = dj[e1], j2 = dj[e2];
            dj[e1] = j2;
            dj[e2] = j1;
            int clash = 0;
            for (int f = 0; f < nd && !clash; f++) {
                if (f != e1 && di[f] == i1 && dj[f] == j2 && dg[f] == dg[e1]) clash = 1;
                if (f != e2 && di[f] == i2 && dj[f] == j1 && dg[f] == dg[e2]) clash = 1;
            }
            if (clash) { dj[e1] = j1; dj[e2] = j2; continue; }
            long nb = evaluate();
            if (nb <= bad || rnd01() < 0.02) bad = nb;
            else { dj[e1] = j1; dj[e2] = j2; }
        }
    }
    if (bad != 0) return 0;
    int V = 2 * p * N;
    build_nbr();
    if (V > best_V) {
        best_V = V;
        best_p = p;
        best_N = N;
        memcpy(best_nbr, nbr, sizeof(int) * V * d);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
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

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    if (moore > CAPV) moore = CAPV;

    while (now() < t_end) {
        int fitp[MAXP], nf = 0;
        for (int pp = 1; pp <= MAXP; pp++) {
            int NN = best_V / (2 * pp) + 1;
            if (NN < d) NN = d;
            if (2L * pp * NN <= moore && NN <= MAXN) fitp[nf++] = pp;
        }
        if (nf == 0) break;
        int pp = fitp[rndint(nf)];
        int NN = best_V / (2 * pp) + 1;
        if (NN < d) NN = d;
        p = pp;
        N = NN;
        attempt(STEPS);
    }

    if (best_V == 0) {
        printf("0 0\n");
        return 0;
    }
    int pN = best_p * best_N;
    printf("%d %d\n", best_V, pN * d);
    for (int v = 0; v < pN; v++)
        for (int c = 0; c < d; c++)
            printf("%d %d\n", v, best_nbr[v * d + c]);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid

    if D >= 2 and best[0] < lib.moore_bound(d, D):
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 5)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(*out, d, D):
                    best = out
            except (RuntimeError, ValueError):
                pass   # keep the fallback
    return best
