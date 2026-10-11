import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family for the D >= 4 target: bipartite Cayley (Haar-type)
# graphs over non-abelian groups. The group is Z_m x|_r Z_k2 with
# (a,b)*(c,e) = (a + r^b c, b + e). Vertices are A_g = g and B_h = G + h, and
# the connection set S (|S| = DEG, distinct elements) gives edges A_g - B_{g s}.
#
# Why two sources suffice: left multiplication is an automorphism that fixes
# each side, so distance(A_g, B_h) = distance(A_e, B_{g^-1 h}) and the same
# reduction holds for same-side pairs. The graph has diameter <= D iff BFS of
# depth D from A_e and from B_e reaches every vertex. Each layer is regular, so
# the degree is exactly DEG and the graph is simple and bipartite by design.
#
# Search: tabu search over connection sets. A move swaps one element of S for an
# element outside S. Candidates are sampled and the best non-tabu one is taken.
# The cost is the number of vertices not reached by the two BFS trees. Group
# orders climb from the current record upward.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXGRP 3000
#define MAXDEG 60
#define SAMPLE 160
#define TABU_LEN 6
#define ITERS 1500
#define STAG 300

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static int DEG, DIAM, G, M, K2, R;
static int *mt = NULL, *inv_ = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int S[MAXDEG], Si[MAXDEG];
static int inS[MAXGRP];
static int tok = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

static void free_group(void) {
    free(mt); free(inv_); free(stamp); free(fr); free(nx);
    mt = inv_ = stamp = fr = nx = NULL;
}

/* Multiplication and inverse tables of Z_m x|_r Z_k2, element (a,b) = a*k2+b. */
static void build_group(int m, int k2, int r) {
    free_group();
    M = m; K2 = k2; R = r; G = m * k2;
    mt = malloc(sizeof(int) * (size_t)G * G);
    inv_ = malloc(sizeof(int) * (size_t)G);
    stamp = calloc((size_t)2 * G, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * G);
    nx = malloc(sizeof(int) * (size_t)2 * G);
    int *Rp = malloc(sizeof(int) * (size_t)k2);
    Rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) Rp[b] = (int)((long long)Rp[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int ra = (int)(((long long)a + (long long)Rp[b] * c) % m);
            int rb = (b + e) % k2;
            mt[(size_t)x * G + y] = ra * k2 + rb;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mt[(size_t)x * G + y] == 0) inv_[x] = y;
    free(Rp);
}

static void set_S(int e, int val) {
    S[e] = val;
    Si[e] = inv_[val];
}

static void random_S(void) {
    memset(inS, 0, sizeof(int) * (size_t)G);
    for (int e = 0; e < DEG;) {
        int x = rnd_int(G);
        if (!inS[x]) { inS[x] = 1; set_S(e, x); e++; }
    }
}

/* Number of vertices reached from src within DIAM steps. */
static int bfs_count(int src) {
    tok++;
    if (tok >= 0x7ffffff0) {
        memset(stamp, 0, sizeof(int) * (size_t)2 * G);
        tok = 1;
    }
    int *f = fr, *h = nx;
    int fsz = 1, cnt = 1;
    f[0] = src;
    stamp[src] = tok;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < G) {
                const int *row = mt + (size_t)v * G;
                for (int e = 0; e < DEG; e++) {
                    int u = G + row[S[e]];
                    if (stamp[u] != tok) { stamp[u] = tok; h[nsz++] = u; }
                }
            } else {
                const int *row = mt + (size_t)(v - G) * G;
                for (int e = 0; e < DEG; e++) {
                    int u = row[Si[e]];
                    if (stamp[u] != tok) { stamp[u] = tok; h[nsz++] = u; }
                }
            }
        }
        cnt += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return cnt;
}

/* Uncovered ordered pairs from the two block representatives A_e and B_e. */
static int cost_of(void) {
    int N2 = 2 * G;
    return (N2 - bfs_count(0)) + (N2 - bfs_count(G));
}

static void save_best(void) {
    if (2 * G <= best_n) return;
    int m = G * DEG;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int g = 0; g < G; g++)
        for (int e = 0; e < DEG; e++) {
            best_e[idx++] = g;
            best_e[idx++] = G + mt[(size_t)g * G + S[e]];
        }
    best_n = 2 * G;
    best_m = m;
}

/* Tabu search over connection sets. Returns 1 if a zero-cost set is found. */
static int tabu_search(int iters) {
    int *tabu = calloc((size_t)G, sizeof(int));
    if (!tabu) return 0;
    random_S();
    int cur = cost_of();
    int bestc = cur, stall = 0, ok = (cur == 0);
    for (int it = 1; it <= iters && !ok && elapsed() < DEADLINE; it++) {
        int be = -1, by = -1, bc = 1 << 30, nb = 0;
        for (int s = 0; s < SAMPLE; s++) {
            int e = rnd_int(DEG);
            int y = rnd_int(G);
            if (inS[y] || tabu[y] > it) continue;
            int x = S[e];
            set_S(e, y);
            int c = cost_of();
            set_S(e, x);
            if (c < bc) { bc = c; be = e; by = y; nb = 1; }
            else if (c == bc && rnd_int(++nb) == 0) { be = e; by = y; }
        }
        if (be < 0) continue;
        int x = S[be];
        inS[x] = 0;
        inS[by] = 1;
        set_S(be, by);
        tabu[x] = it + TABU_LEN + rnd_int(TABU_LEN);
        cur = bc;
        if (cur == 0) { ok = 1; break; }
        if (cur < bestc) { bestc = cur; stall = 0; }
        else stall++;
        if (stall > STAG) {
            for (int k = 0; k < 3; k++) {
                int e = rnd_int(DEG);
                int y = rnd_int(G);
                if (inS[y]) continue;
                inS[S[e]] = 0;
                inS[y] = 1;
                set_S(e, y);
            }
            cur = cost_of();
            bestc = cur;
            stall = 0;
        }
    }
    free(tabu);
    return ok;
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
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int lo = start_n / 2 + 1;
    if (lo < DEG) lo = DEG;
    if (lo < 2) lo = 2;
    int fails = 0;

    while (elapsed() < DEADLINE) {
        int width = 3 + (fails / 2 < 17 ? fails / 2 : 17);
        int Gc = lo + rnd_int(width);
        if (Gc > MAXGRP) break;

        int opts[16], no = 0, abopts[16], nab = 0;
        for (int c = 1; c <= 12 && c <= Gc; c++)
            if (Gc % c == 0 && Gc / c >= 2) {
                opts[no++] = c;
                if (c > 1) abopts[nab++] = c;
            }
        if (no == 0) { lo++; continue; }
        int k2;
        if (nab > 0 && rnd_unit() < 0.75) k2 = abopts[rnd_int(nab)];
        else k2 = opts[rnd_int(no)];

        int m = Gc / k2, r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) { k2 = 1; m = Gc; r = 1; }
        }

        build_group(m, k2, r);
        int ok = tabu_search(ITERS);
        if (ok) {
            save_best();
            lo = G + 1;
            fails = 0;
        } else {
            fails++;
        }
        free_group();
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
# Safe baseline families (valid for their diameters, used as fallbacks).
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C tabu search over bipartite Cayley graphs.
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

    # The C deadline starts after compile and excludes it, so reserve time for
    # compile, parsing and validation.
    remaining = 0.93 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
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
