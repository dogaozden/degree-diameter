"""Bi-Cayley voltage-lift annealer in C with exact source-bitmask cost, plus
vertex-deletion repair of near-valid lifts, on top of the general C growth engine."""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine. argv: mode d D seed seconds [args]
#   mode 0: general annealer. Reads a start graph on stdin and grows it by
#           vertex pairs (edge toggles, cost = ordered pairs at distance > D).
#   mode 1: bi-Cayley lift annealer over Z_m x| Z_k2 with k blocks per side.
#           args: K M K2 R. Cost = (vertex, source-block) pairs not within D
#           plus a duplicate penalty. Outputs the lowest-cost lift it found,
#           which may be invalid (Python repairs it or discards it).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* ============ Part 1: general graph annealer with vertex growth ============ */

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

static long long bad_pairs(void) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

static int run_growth(double limit, int grow_max) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }
    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    double tstart = cpu_now();
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
    }
    while (1) {
        double el = cpu_now() - tstart;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = rint_(N), y = rint_(N);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}

/* ============ Part 2: bi-Cayley lift annealer ============ */

/* Vertices: left block i, element g -> i*G+g; right block j, element h -> (K+j)*G+h.
   Dart (layer l, left block i): right block j = lay[l][i], voltage s = sv[l][i].
   Edges: (i,g) ~ (j, g*s). Left multiplication by x is an automorphism, so
   the distance from (b, e) to every vertex covers all pairs. Sources are the
   2K identity vertices, one bit each, and cost = sum over vertices of the
   number of sources that miss it. */

static int L_d, L_D, L_K, L_M, L_K2, L_G, L_NV;
static int L_pw[64];
static int *L_lay, *L_linv, *L_sv, *L_sinv, *L_nb, *L_bLay, *L_bSv;
static unsigned char *L_cur, *L_nxt, *L_res, *L_curSrc;

static int gcd_int(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int lgmul(int x, int y) {
    int a = x / L_K2, b = x % L_K2, c = y / L_K2, e = y % L_K2;
    long long t = (long long)L_pw[b] * c % L_M;
    int aa = (int)((a + t) % L_M);
    return aa * L_K2 + (b + e) % L_K2;
}

static int lginv(int x) {
    int a = x / L_K2, b = x % L_K2;
    int nbk = (L_K2 - b) % L_K2;
    long long t = (long long)L_pw[nbk] * a % L_M;
    int aa = (int)((L_M - t) % L_M);
    return aa * L_K2 + nbk;
}

static void lfix_linv(int l) {
    for (int i = 0; i < L_K; i++) L_linv[l * L_K + L_lay[l * L_K + i]] = i;
}

static void l_build_nb(void) {
    int K = L_K, G = L_G, DG = L_d;
    for (int i = 0; i < K; i++) {
        for (int g = 0; g < G; g++) {
            int *q = L_nb + (size_t)(i * G + g) * DG;
            for (int l = 0; l < DG; l++) {
                int j = L_lay[l * K + i], s = L_sv[l * K + i];
                q[l] = (K + j) * G + lgmul(g, s);
            }
        }
    }
    for (int j = 0; j < K; j++) {
        for (int h = 0; h < G; h++) {
            int *q = L_nb + (size_t)((K + j) * G + h) * DG;
            for (int l = 0; l < DG; l++) {
                int i = L_linv[l * K + j];
                int s = L_sv[l * K + i];
                q[l] = i * G + lgmul(h, L_sinv[s]);
            }
        }
    }
}

static int l_dup(void) {
    int c = 0, K = L_K, DG = L_d;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DG; l1++)
            for (int l2 = l1 + 1; l2 < DG; l2++)
                if (L_lay[l1 * K + i] == L_lay[l2 * K + i] && L_sv[l1 * K + i] == L_sv[l2 * K + i]) c++;
    return c;
}

static long long l_eval(void) {
    int NV = L_NV, DG = L_d, K = L_K;
    unsigned char *cur = L_cur, *nxt = L_nxt;
    memset(cur, 0, (size_t)NV);
    for (int b = 0; b < 2 * K; b++) cur[b * L_G] |= (unsigned char)(1u << b);
    for (int t = 0; t < L_D; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            unsigned char x = cur[v];
            const int *q = L_nb + (size_t)v * DG;
            for (int l = 0; l < DG; l++) x |= cur[q[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        unsigned char *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    memcpy(L_res, cur, (size_t)NV);
    long long miss = 0;
    for (int v = 0; v < NV; v++) miss += 2 * K - __builtin_popcount((unsigned)L_res[v]);
    return miss + 20LL * l_dup();
}

static void l_init(void) {
    int K = L_K, DG = L_d;
    int perm[8];
    for (int l = 0; l < DG; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) L_lay[l * K + i] = perm[i];
        for (int i = 0; i < K; i++) L_sv[l * K + i] = rint_(L_G);
    }
    for (int l = 0; l < DG; l++) lfix_linv(l);
}

static void l_emit(void) {
    int K = L_K, G = L_G, DG = L_d, NV = L_NV;
    int cap = K * G * DG;
    int *eu = malloc(sizeof(int) * (size_t)(cap > 0 ? cap : 1));
    int *ev = malloc(sizeof(int) * (size_t)(cap > 0 ? cap : 1));
    int cnt = 0;
    for (int v = 0; v < K * G; v++) {
        const int *q = L_nb + (size_t)v * DG;
        for (int l = 0; l < DG; l++) {
            int u = q[l], dup = 0;
            for (int l2 = 0; l2 < l; l2++) if (q[l2] == u) { dup = 1; break; }
            if (!dup) { eu[cnt] = v; ev[cnt] = u; cnt++; }
        }
    }
    printf("%d %d\n", NV, cnt);
    for (int e = 0; e < cnt; e++) printf("%d %d\n", eu[e], ev[e]);
}

static int run_lift(double limit, int K, int M, int K2, int R) {
    int DG = L_d;
    if (K < 1 || K > 4 || M < 1 || K2 < 1 || K2 > 64 || DG < 1 || DG > 64 || L_D < 1) {
        printf("0 0\n");
        return 0;
    }
    long long Gl = (long long)M * K2;
    if (Gl > 20000 || 2LL * K * Gl > 40000) { printf("0 0\n"); return 0; }
    L_K = K; L_M = M; L_K2 = K2; L_G = (int)Gl; L_NV = 2 * K * L_G;
    int G = L_G, NV = L_NV;

    int rr = R % M; if (rr < 0) rr += M;
    L_pw[0] = 1 % M;
    for (int t = 1; t < K2; t++) L_pw[t] = (int)((long long)L_pw[t - 1] * rr % M);
    if ((long long)L_pw[K2 - 1] * rr % M != 1 % M || gcd_int(rr, M) != 1) {
        printf("0 0\n");
        return 0;
    }

    L_sinv = malloc(sizeof(int) * (size_t)G);
    for (int s = 0; s < G; s++) L_sinv[s] = lginv(s);
    L_lay = malloc(sizeof(int) * (size_t)DG * K);
    L_linv = malloc(sizeof(int) * (size_t)DG * K);
    L_sv = malloc(sizeof(int) * (size_t)DG * K);
    L_bLay = malloc(sizeof(int) * (size_t)DG * K);
    L_bSv = malloc(sizeof(int) * (size_t)DG * K);
    L_nb = malloc(sizeof(int) * (size_t)NV * DG);
    L_cur = malloc((size_t)NV);
    L_nxt = malloc((size_t)NV);
    L_res = malloc((size_t)NV);
    L_curSrc = malloc((size_t)NV);
    if (!L_sinv || !L_lay || !L_linv || !L_sv || !L_bLay || !L_bSv || !L_nb || !L_cur || !L_nxt || !L_res || !L_curSrc) {
        printf("0 0\n");
        return 0;
    }

    unsigned char full = (unsigned char)((1u << (2 * K)) - 1);
    l_init();
    l_build_nb();
    long long cur = l_eval();
    memcpy(L_curSrc, L_res, (size_t)NV);
    long long best = cur;
    memcpy(L_bLay, L_lay, sizeof(int) * (size_t)DG * K);
    memcpy(L_bSv, L_sv, sizeof(int) * (size_t)DG * K);

    const double T0 = 4.0, T1 = 0.15;
    double period = limit / 3.0;
    if (period < 0.25) period = 0.25;
    double tstart = cpu_now();

    while (best > 0) {
        double el = cpu_now() - tstart;
        if (el >= limit) break;
        double ph = fmod(el, period) / period;
        double T = T0 * pow(T1 / T0, ph);

        /* Pick a dart, aimed at a vertex that still misses a source when possible. */
        int l = -1, i = -1;
        for (int tr = 0; tr < 30; tr++) {
            int v = rint_(NV);
            if (L_curSrc[v] == full) continue;
            if (v < K * G) {
                i = v / G;
                l = rint_(DG);
            } else {
                int j = v / G - K;
                l = rint_(DG);
                i = L_linv[l * K + j];
            }
            break;
        }
        if (l < 0) { l = rint_(DG); i = rint_(K); }

        int kind = (K >= 2 && rdbl() < 0.35) ? 1 : 0;
        int i2 = -1, oldv = -1;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int *lay = L_lay + l * K;
            int t = lay[i]; lay[i] = lay[i2]; lay[i2] = t;
            lfix_linv(l);
        } else {
            oldv = L_sv[l * K + i];
            int nw = rint_(G);
            if (nw == oldv) continue;
            L_sv[l * K + i] = nw;
        }
        l_build_nb();
        long long nc = l_eval();
        long long diff = nc - cur;
        if (diff <= 0 || rdbl() < exp(-(double)diff / T)) {
            cur = nc;
            memcpy(L_curSrc, L_res, (size_t)NV);
            if (cur < best) {
                best = cur;
                memcpy(L_bLay, L_lay, sizeof(int) * (size_t)DG * K);
                memcpy(L_bSv, L_sv, sizeof(int) * (size_t)DG * K);
            }
        } else {
            if (kind) {
                int *lay = L_lay + l * K;
                int t = lay[i]; lay[i] = lay[i2]; lay[i2] = t;
                lfix_linv(l);
            } else {
                L_sv[l * K + i] = oldv;
            }
            l_build_nb();
        }
    }

    memcpy(L_lay, L_bLay, sizeof(int) * (size_t)DG * K);
    memcpy(L_sv, L_bSv, sizeof(int) * (size_t)DG * K);
    for (int q = 0; q < DG; q++) lfix_linv(q);
    l_build_nb();
    l_emit();
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int mode = atoi(argv[1]);
    d_ = atoi(argv[2]);
    D_ = atoi(argv[3]);
    rs ^= (u64)strtoull(argv[4], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[5]);
    if (mode == 0) {
        int grow_max = argc > 6 ? atoi(argv[6]) : 200;
        return run_growth(limit, grow_max);
    }
    if (argc < 10) { printf("0 0\n"); return 0; }
    L_d = d_;
    L_D = D_;
    return run_lift(limit, atoi(argv[6]), atoi(argv[7]), atoi(argv[8]), atoi(argv[9]));
}
"""

_KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _lift_in_c(d, D, seed, seconds, k, m, k2, r):
    """Bi-Cayley lift annealing in C; returns (n, edges), possibly invalid."""
    out = lib.run_c(C_SOURCE, [1, d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """General annealer growth from a valid graph; returns (n, edges)."""
    out = lib.run_c(C_SOURCE, [0, d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 5.0)
    return lib.parse_graph_text(out)


def _ball_masks(n, adj, D):
    """Per-vertex bitmask of vertices within distance D (Python big ints)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return reach


def _prune(n, edges, d, D, deadline):
    """Repair by vertex deletion: repeatedly drop the vertices missing the most
    others (in batches). Returns a valid (n, edges) or None."""
    edges = [tuple(e) for e in edges]
    while time.monotonic() < deadline:
        adj = lib.adjacency(n, edges)
        reach = _ball_masks(n, adj, D)
        miss = [n - r.bit_count() for r in reach]
        if sum(miss) == 0:
            break
        nbad = sum(1 for x in miss if x)
        batch = max(1, nbad // 12)
        order = sorted(range(n), key=lambda v: -miss[v])
        drop = set(order[:batch])
        keep = [v for v in range(n) if v not in drop]
        if not keep:
            return None
        idx = {v: i for i, v in enumerate(keep)}
        n = len(keep)
        edges = [(idx[u], idx[v]) for u, v in edges if u in idx and v in idx]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bi-Cayley lifts annealed in C, repaired by deletion when near-valid.
    lift_end = t0 + max(1.0, 0.72 * time_limit)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        now = time.monotonic()
        remain = lift_end - now
        if remain < 1.5:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        secs = min(remain, rng.uniform(2.5, 5.0))
        trials[k] += 1
        try:
            n, e = _lift_in_c(d, D, rng.randrange(1, 1 << 30), secs, k, m, k2, r)
        except Exception:
            continue
        if n == 0:
            continue
        if lib.is_valid(n, e, d, D):
            wins[k] += 1
            consider(n, e)
        elif n > best[0]:
            try:
                pr = _prune(n, e, d, D, min(lift_end, time.monotonic() + 8.0))
            except Exception:
                pr = None
            if pr is not None:
                wins[k] += 1
                consider(pr[0], pr[1])

    # Phase 2: general C annealer grows the best valid graph by vertex pairs.
    rem = (t0 + time_limit - 4.0) - time.monotonic()
    if rem >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, rem,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
