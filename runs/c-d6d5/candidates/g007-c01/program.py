"""Bi-Cayley (Haar) search for diameter-D bipartite graphs, replacing the voltage-lift annealing.

Construction: for a finite group G of order g and a connection set S = {s_1..s_d} of distinct
elements, the Haar graph H(G, S) has parts A = G and B = G, with a in A adjacent to b in B
iff a^{-1} b is in S. It is d-regular and bipartite on 2g vertices. Left multiplication is an
automorphism that is transitive on each part, so the diameter test reduces to two BFS runs
(from the identity of A and from the identity of B). The C engine searches over
G = Z_m x|_r Z_k (r^k = 1 mod m, abelian when r = 1) and over S by simulated annealing,
minimising the number of unreached vertices. Each success adds 2 vertices, and the group
order is pushed upward from the best success so far.

Python: K_{d,d} fallback, known D = 3 constructions (projective plane, Araujo-Pardo-Lopez),
generalized quadrangle W(q) for D >= 4, and final validation with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 64
#define MAXG 2048
#define MAXK 12
#define ITERS 25000
#define RESTARTS 3

static int DEG, DIAM;
static double T_END;
static struct timespec T0;
static uint64_t rs[2];

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_M x|_R Z_K
 * element index x = a*K + b, product (a,b)(c,e) = (a + R^b c, b + e mod K). Identity is 0. */

static int M, K, R, G;
static int Rpow[MAXK];

static void set_group(int m, int k, int r) {
    M = m;
    K = k;
    R = r;
    G = m * k;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    long long ra = ((long long)a + (long long)Rpow[b] * c) % M;
    return (int)(ra * K + (b + e) % K);
}

/* Pick a random group of order g: K from the divisors of g (K <= MAXK), R random with
 * R^K = 1 mod M and gcd(R, M) = 1, falling back to the abelian choice R = 1. */
static void pick_group(int g) {
    int opts[MAXK], no = 0;
    for (int k = 1; k <= MAXK; k++)
        if (g % k == 0 && g / k >= 2) opts[no++] = k;
    int k = opts[rnd_int(no)];
    int m = g / k;
    int r = 1;
    if (k > 1) {
        for (int tr = 0; tr < 400; tr++) {
            int cand = rnd_int(m);
            if (cand >= 2 && gcd_i(cand, m) == 1 && powmod_i(cand, k, m) == 1 % m) {
                r = cand;
                break;
            }
        }
    }
    set_group(m, k, r);
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXDEG];
static int RT[MAXDEG][MAXG];   /* RT[i][x] = x * s_i        (A x -> B) */
static int RI[MAXDEG][MAXG];   /* RI[i][y] = y * s_i^{-1}   (B y -> A) */
static int vis[2 * MAXG], qu[2 * MAXG];
static int stamp_ctr = 0;

static void set_elem(int i, int s) {
    int inv = 0;
    for (int y = 0; y < G; y++)
        if (gmul(s, y) == 0) { inv = y; break; }
    S[i] = s;
    for (int x = 0; x < G; x++) {
        RT[i][x] = gmul(x, s);
        RI[i][x] = gmul(x, inv);
    }
}

static int in_S(int s, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == s) return 1;
    return 0;
}

/* Number of vertices (of 2G) reached from src within DIAM steps. */
static int bfs_reach(int src) {
    stamp_ctr++;
    if (stamp_ctr == 0x7fffffff) {
        memset(vis, 0, sizeof vis);
        stamp_ctr = 1;
    }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp_ctr;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = qu[head++];
            if (v < G) {
                for (int i = 0; i < DEG; i++) {
                    int w = G + RT[i][v];
                    if (vis[w] != stamp_ctr) {
                        vis[w] = stamp_ctr;
                        qu[tail++] = w;
                    }
                }
            } else {
                int y = v - G;
                for (int i = 0; i < DEG; i++) {
                    int w = RI[i][y];
                    if (vis[w] != stamp_ctr) {
                        vis[w] = stamp_ctr;
                        qu[tail++] = w;
                    }
                }
            }
        }
    }
    return tail;
}

/* Vertex transitivity on each part makes two BFS runs decide the diameter. */
static int cost(void) {
    int N = 2 * G;
    return (N - bfs_reach(0)) + (N - bfs_reach(G));
}

/* Simulated annealing over the connection set for the current group. */
static int sa_try(void) {
    for (int i = 0; i < DEG; i++) {
        int s;
        do { s = rnd_int(G); } while (in_S(s, i));
        set_elem(i, s);
    }
    int c = cost();
    if (c == 0) return 1;
    for (int it = 0; it < ITERS; it++) {
        if ((it & 255) == 0 && elapsed() > T_END) break;
        double temp = 2.0 * (1.0 - (double)it / ITERS) + 0.05;
        int i = rnd_int(DEG);
        int s = rnd_int(G);
        if (in_S(s, DEG)) continue;
        int old = S[i];
        set_elem(i, s);
        int c2 = cost();
        if (c2 <= c || rnd_unit() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            set_elem(i, old);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ search driver */

static int best_G = 0, best_M, best_K, best_R;
static int best_S[MAXDEG];

/* Largest G with 2G <= bipartite Moore bound for degree DEG and diameter DIAM. */
static long moore_G(void) {
    if (DEG == 1) return 1;
    if (DEG == 2) return DIAM;
    long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        if (s > 1000000L) break;
        p *= (DEG - 1);
    }
    return s;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 2;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    T_END = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 977ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    long gcap = moore_G();
    if (gcap > MAXG - 1) gcap = MAXG - 1;

    while (elapsed() < T_END) {
        long gmin = best_G + 1;
        if (best_G == 0) {
            long floor_g = gcap * 2 / 5;   /* start high: small groups are already known */
            if (floor_g > gmin) gmin = floor_g;
        }
        if (gmin < DEG) gmin = DEG;
        if (gmin < 2) gmin = 2;
        if (gmin > gcap) break;
        long span = gcap - gmin;
        if (span > 60) span = 60;
        int g = (int)(gmin + rnd_int((int)span + 1));

        pick_group(g);
        int found = 0;
        for (int r = 0; r < RESTARTS && !found && elapsed() < T_END; r++)
            found = sa_try();
        if (found) {
            best_G = G;
            best_M = M;
            best_K = K;
            best_R = R;
            memcpy(best_S, S, sizeof(int) * (size_t)DEG);
        }
    }

    if (best_G <= 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(best_M, best_K, best_R);
    for (int i = 0; i < DEG; i++) set_elem(i, best_S[i]);
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * G;
    long m = (long)G * DEG;
    printf("%d %ld\n", n, m);
    for (int x = 0; x < G; x++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", x, G + RT[i][x]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: known constructions, fallbacks and validation.
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Best construction Python builds directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])   # a single edge is valid for any d >= 1, D >= 1

    known = _known_start(d, D)
    if known is not None and lib.is_valid(known[0], known[1], d, D) and known[0] > best[0]:
        best = known

    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=None, timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass   # keep the valid fallback

    return best
