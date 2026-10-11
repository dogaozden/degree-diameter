import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New engine: bi-Cayley (Haar-type) graphs over semidirect products
# G = Z_M x|_R Z_K2, element (a, b) coded as a*K2 + b.
#
# Vertices: A_g = g and B_h = G + h. The connection set S = {s_0..s_{DEG-1}}
# (distinct group elements) gives edges A_g -- B_{g*s} for all s in S.
# Each A has DEG neighbours B_{g s_i}, each B has DEG neighbours A_{h s_i^-1},
# so the graph is simple, bipartite and DEG-regular.
#
# Left multiplication by any h is an automorphism (A_g -> A_{hg}, B_x -> B_{hx}),
# so the diameter is <= DIAM iff BFS of depth DIAM from A_0 and from B_0
# reaches every vertex. The cost is the number of unreached vertices.
#
# Search: tabu search over the connection set. A move replaces one element of S
# by a sampled outside element. Tabu forbids restoring the value just removed
# from that position for a few steps. Aspiration allows a tabu move that beats
# the best cost of the run. Each run uses a fresh random group of order G near
# the current frontier (best_n / 2 + 1 and above). Any zero-cost run is a valid
# graph of order 2G; the group order then climbs.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

#define MAXG 4096
#define MAXD 16
#define MAXK2 12
#define SAMPLES 160
#define MAXIT 6000
#define STALL 700

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int DEG, DIAM;
static int G, M, K2, R;
static int Rpow[MAXK2];
static int S[MAXD], invS[MAXD];
static int adj[2 * MAXG * MAXD];
static int stamp[2 * MAXG];
static int curst = 0;
static int fa[2 * MAXG], fb[2 * MAXG];
static int tabu[MAXD * MAXG];
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

/* (a,b)*(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = b + e;
    if (rb >= K2) rb -= K2;
    return ra * K2 + rb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b), with r^(-b) = r^(K2-b). */
static inline int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb = (K2 - b) % K2;
    int na = (int)((M - ((long long)Rpow[nb] * a) % M) % M);
    return na * K2 + nb;
}

static void setup_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    R = r;
    G = m * k2;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void build_adj(void) {
    for (int i = 0; i < DEG; i++) invS[i] = ginv(S[i]);
    for (int g = 0; g < G; g++) {
        int *ag = adj + (size_t)g * DEG;
        for (int i = 0; i < DEG; i++) ag[i] = G + gmul(g, S[i]);
    }
    for (int h = 0; h < G; h++) {
        int *bh = adj + (size_t)(G + h) * DEG;
        for (int i = 0; i < DEG; i++) bh[i] = gmul(h, invS[i]);
    }
}

/* Number of vertices within distance DIAM of src (including src). */
static int bfs_count(int src) {
    if (curst >= 2000000000) {
        memset(stamp, 0, sizeof(stamp));
        curst = 0;
    }
    curst++;
    int *f = fa, *h = fb;
    int fsz = 1, cnt = 1;
    f[0] = src;
    stamp[src] = curst;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            const int *au = adj + (size_t)f[q] * DEG;
            for (int e = 0; e < DEG; e++) {
                int v = au[e];
                if (stamp[v] != curst) {
                    stamp[v] = curst;
                    h[nsz++] = v;
                }
            }
        }
        cnt += nsz;
        int *t = f; f = h; h = t;
        fsz = nsz;
    }
    return cnt;
}

/* Number of unreached (source-to-vertex) pairs from A_0 and B_0. */
static long long eval_cost(void) {
    build_adj();
    long long N2 = 2LL * G;
    long long c1 = N2 - bfs_count(0);
    long long c2 = N2 - bfs_count(G);
    return c1 + c2;
}

static int inS(int x) {
    for (int i = 0; i < DEG; i++) if (S[i] == x) return 1;
    return 0;
}

static void random_S(void) {
    for (int i = 0; i < DEG; i++) {
        int x, dup;
        do {
            x = rnd_int(G);
            dup = 0;
            for (int j = 0; j < i; j++) if (S[j] == x) { dup = 1; break; }
        } while (dup);
        S[i] = x;
    }
}

/* Tabu search over connection sets. Returns 1 if a zero-cost set was found (left in S). */
static int run_tabu(void) {
    random_S();
    long long cur = eval_cost();
    long long bestc = cur;
    memset(tabu, 0, sizeof(int) * (size_t)DEG * (size_t)G);
    int stall = 0;
    for (int it = 1; it <= MAXIT && cur > 0; it++) {
        if (elapsed() > DEADLINE) break;
        int bp = -1, bx = -1, nt = 0;
        long long bc = LLONG_MAX;
        for (int s = 0; s < SAMPLES; s++) {
            int p = rnd_int(DEG);
            int x = rnd_int(G);
            if (inS(x)) continue;
            int old = S[p];
            int istabu = tabu[p * G + x] > it;
            S[p] = x;
            long long c = eval_cost();
            S[p] = old;
            if (istabu && c >= bestc) continue;
            if (c < bc) {
                bc = c; bp = p; bx = x; nt = 1;
            } else if (c == bc) {
                nt++;
                if (rnd_int(nt) == 0) { bp = p; bx = x; }
            }
        }
        if (bp < 0) continue;
        int old = S[bp];
        tabu[bp * G + old] = it + 4 + rnd_int(8);
        S[bp] = bx;
        cur = bc;
        if (cur < bestc) {
            bestc = cur;
            stall = 0;
        } else if (++stall > STALL) {
            break;
        }
    }
    return cur == 0;
}

static void emit_best(void) {
    int N2 = 2 * G, m = G * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int g = 0; g < G; g++)
        for (int i = 0; i < DEG; i++) {
            e[idx++] = g;
            e[idx++] = G + gmul(g, S[i]);
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N2;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 2 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int gmin = best_n / 2 + 1;
        if (gmin < DEG + 1) gmin = DEG + 1;
        if (gmin > MAXG) break;
        int spread = gmin / 10 + 3;
        int G0 = gmin + rnd_int(spread);
        if (G0 > MAXG) G0 = gmin;

        int opts[MAXK2], no = 0;
        for (int c = 1; c <= MAXK2; c++)
            if (G0 % c == 0 && G0 / c >= 2) opts[no++] = c;
        int k2 = opts[rnd_int(no)];
        int m = G0 / k2;
        int r = 1 % m;
        if (k2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                k2 = 1;
                m = G0;
                r = 1 % m;
            }
        }
        setup_group(m, k2, r);
        if (run_tabu() && 2 * G > best_n) emit_best();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (valid for small D and as fallbacks).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C tabu search over bi-Cayley graphs.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Reserve time for compile, parsing and validation (the C clock excludes compile).
    remaining = 0.93 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0 and d >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
