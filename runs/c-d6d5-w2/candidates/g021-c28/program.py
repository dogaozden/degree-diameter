import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family for the weakest target: bi-Cayley graphs.
#
# A bi-Cayley graph over a group H of order G has vertices A_x and B_x (x in H),
# with A_x joined to B_{x*s} for each s in a connection set S of size d. Left
# multiplication is an automorphism that is transitive on each side, so the
# diameter is at most D iff BFS of depth D from A_e and from B_e reaches every
# vertex. The order is 2G.
#
# Groups are semidirect products Z_m x| Z_k (r^k = 1 mod m), chosen at random.
# The search is a tabu search on the connection set: each step samples moves
# "replace s_i by a new group element", applies the best non-tabu move, and
# keeps a tabu tenure on the removed element. Orders climb one at a time from
# a start order; each order gets a time share, and the search stops at the
# first order that cannot be solved. Every success is stored and emitted.
#
# Safe fallbacks: projective-plane incidence graphs, the Araujo-Pardo-Lopez
# graph, W(q) quadrangle incidence graphs, and K_{d,d}. Every returned graph is
# checked with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM;
static int G, M, K2, R;
static int *Rpow = NULL, *MUL = NULL, *INV = NULL;
static int *S = NULL, *inS = NULL, *tabu = NULL;
static int *stamp = NULL, *fr = NULL, *nx = NULL;
static int curst = 0;

static int best_m = 0, best_n = 0;
static int *best_e = NULL;

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

static void free_all(void) {
    free(Rpow); free(MUL); free(INV); free(S); free(inS); free(tabu);
    free(stamp); free(fr); free(nx);
    Rpow = MUL = INV = S = inS = tabu = stamp = fr = nx = NULL;
}

/* Element (a,b) is coded a*K2+b, with (a,b)(c,e) = (a + r^b c, b + e). */
static void setup(int m, int k2, int r) {
    free_all();
    M = m; K2 = k2; R = r; G = m * k2;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    MUL = malloc(sizeof(int) * (size_t)G * G);
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < G; y++) {
            int c = y / K2, e = y % K2;
            int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
            int rb = (b + e) % K2;
            MUL[(size_t)x * G + y] = ra * K2 + rb;
        }
    }
    INV = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        INV[x] = 0;
        for (int y = 0; y < G; y++)
            if (MUL[(size_t)x * G + y] == 0) { INV[x] = y; break; }
    }
    S = malloc(sizeof(int) * (size_t)DEG);
    inS = calloc((size_t)G, sizeof(int));
    tabu = calloc((size_t)DEG * G, sizeof(int));
    stamp = calloc(2 * (size_t)G, sizeof(int));
    fr = malloc(sizeof(int) * 2 * (size_t)G);
    nx = malloc(sizeof(int) * 2 * (size_t)G);
    curst = 0;
}

/* Pick a random semidirect product of order g (cyclic when the k2 choice is 1). */
static void pick_group(int g) {
    int divs[16], nd = 0;
    for (int c = 1; c <= 12; c++)
        if (c <= g && g % c == 0 && g / c >= 2) divs[nd++] = c;
    int k2 = divs[rnd_int(nd)];
    int m = g / k2, r = 1;
    if (k2 > 1 && rnd_unit() < 0.7) {
        for (int tr = 0; tr < 300; tr++) {
            int cand = 1 + rnd_int(m - 1);
            if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                r = cand;
                break;
            }
        }
    }
    setup(m, k2, r);
}

/* Number of vertices within DIAM of src. Vertex A_x = x, B_y = G + y. */
static int reach(int src) {
    int N2 = 2 * G;
    curst++;
    if (curst >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)N2);
        curst = 1;
    }
    int *f = fr, *h = nx;
    int fsz = 1, cnt = 1;
    f[0] = src;
    stamp[src] = curst;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < G) {
                for (int i = 0; i < DEG; i++) {
                    int w = G + MUL[(size_t)v * G + S[i]];
                    if (stamp[w] != curst) { stamp[w] = curst; h[nsz++] = w; }
                }
            } else {
                int y = v - G;
                for (int i = 0; i < DEG; i++) {
                    int w = MUL[(size_t)y * G + INV[S[i]]];
                    if (stamp[w] != curst) { stamp[w] = curst; h[nsz++] = w; }
                }
            }
        }
        cnt += nsz;
        int *t = f; f = h; h = t;
        fsz = nsz;
    }
    return cnt;
}

static int cost(void) {
    return (2 * G - reach(0)) + (2 * G - reach(G));
}

static void random_S(void) {
    memset(inS, 0, sizeof(int) * (size_t)G);
    for (int i = 0; i < DEG; i++) {
        int v;
        do v = rnd_int(G); while (inS[v]);
        S[i] = v;
        inS[v] = 1;
    }
}

#define NS_SAMPLES 96
#define STALL_LIMIT 400

/* Tabu search on the connection set. Returns 1 if a zero-cost set is found (S holds it). */
static int tabu_attempt(double until) {
    random_S();
    memset(tabu, 0, sizeof(int) * (size_t)DEG * G);
    int c = cost();
    int bestc = c, stall = 0;
    for (int it = 1; ; it++) {
        if (c == 0) return 1;
        if ((it & 7) == 0 && elapsed() > until) break;
        int bi = -1, bv = -1, bc = 1 << 30, ties = 0;
        for (int s = 0; s < NS_SAMPLES; s++) {
            int i = rnd_int(DEG), v = rnd_int(G);
            if (inS[v]) continue;
            int old = S[i];
            S[i] = v;
            int c2 = cost();
            S[i] = old;
            int istabu = tabu[(size_t)i * G + v] > it;
            if (istabu && c2 >= bestc) continue;
            if (c2 < bc) {
                bc = c2; bi = i; bv = v; ties = 1;
            } else if (c2 == bc) {
                ties++;
                if (rnd_int(ties) == 0) { bi = i; bv = v; }
            }
        }
        if (bi < 0) continue;
        int old = S[bi];
        inS[old] = 0;
        S[bi] = bv;
        inS[bv] = 1;
        tabu[(size_t)bi * G + old] = it + 4 + rnd_int(8);
        c = bc;
        if (c < bestc) { bestc = c; stall = 0; } else stall++;
        if (stall > STALL_LIMIT) {
            for (int k = 0; k < 2; k++) {
                int i = rnd_int(DEG), v;
                do v = rnd_int(G); while (inS[v]);
                inS[S[i]] = 0;
                S[i] = v;
                inS[v] = 1;
            }
            c = cost();
            bestc = c;
            stall = 0;
        }
    }
    return c == 0;
}

/* Store the current valid S as the best graph: A_x -- B_{x*s} for each s in S. */
static void emit(void) {
    int m = DEG * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int i = 0; i < DEG; i++)
        for (int x = 0; x < G; x++) {
            best_e[idx++] = x;
            best_e[idx++] = G + MUL[(size_t)x * G + S[i]];
        }
    best_m = m;
    best_n = 2 * G;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int gstart = argc > 5 ? atoi(argv[5]) : 2;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int g = gstart;
    if (g < DEG) g = DEG;
    if (g < 2) g = 2;

    while (1) {
        double now = elapsed();
        double remaining = DEADLINE - now;
        if (remaining < 0.5) break;
        double level_end = now + fmax(3.0, 0.4 * remaining);
        if (level_end > DEADLINE) level_end = DEADLINE;
        int ok = 0;
        while (elapsed() < level_end && !ok) {
            double slice_end = elapsed() + fmax(1.5, 0.25 * (level_end - elapsed()));
            if (slice_end > level_end) slice_end = level_end;
            pick_group(g);
            if (tabu_attempt(slice_end)) ok = 1;
        }
        if (!ok) break;
        emit();
        g++;
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    free_all();
    free(best_e);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe algebraic baselines.
# ----------------------------------------------------------------------------

_START_ORDER = {(6, 5): 343}  # group order to start the bi-Cayley search from (order 2G > 684)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Driver.
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
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search most of the budget. Leave room for the compile and for validation.
    elapsed = time.monotonic() - start
    remaining = 0.85 * time_limit - elapsed - 3.0
    if remaining >= 2.0:
        gstart = max(best_n // 2 + 1, _START_ORDER.get((d, D), 0))
        hard = min(remaining + 4.0, time_limit - elapsed - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", gstart],
                            timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
