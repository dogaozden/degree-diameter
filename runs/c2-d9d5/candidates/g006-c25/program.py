"""Multi-block voltage lifts over Z_m x|_r Z_k for the bipartite degree-diameter problem.

Change of construction: the parent searched Haar graphs (one base block per side).
This version searches general base graphs with B blocks per side (B <= 6). Dart e joins
A-block src[e] to B-block tgt[e] with a voltage vol[e] in a semidirect product G of
Z_m by Z_k. The lift is (u, x) ~ (B+v, x*g) for each dart (u, v, g).

Invariants that keep every output valid:
  * every A-block and every B-block has exactly d darts, so the lift is d-regular;
  * darts that share a block pair have distinct voltages, so the lift is simple;
  * the graph is bipartite by construction.
Left multiplication is an automorphism that is transitive on each block, so the
diameter test is one BFS per block (2B BFS runs). The search is simulated annealing
over voltages and over the block-pair pattern (swaps of targets or sources).
Candidates are ordered by vertex count, ascending from a threshold just above the
safe fallback, so easy orders succeed quickly and push the threshold up.

The Python side keeps the valid fallbacks (K_{d,d}, projective-plane and
Araujo-Pardo--Lopez constructions, the W(q) quadrangle for D = 4) and accepts the C
output only after lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-block voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 6
#define MAXBLK (2 * MAXB)
#define MAXD 32
#define MAXE (MAXB * MAXD)
#define MAXV 8192
#define MAXCAND 60000
#define KPER 12
#define TMPMAX 4096

typedef struct { int B, m, k, r, total; uint64_t key; } Cand;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int a, int e, int m) {
    long r = 1 % m, x = a % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

/* Element (a, b) is coded as a*k + b. Product: (a,b)(c,e) = (a + r^b c, b + e). */
static int G, B, V, NE;
static int GM, GK;
static int PW[MAXV];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)(((long)a + (long)PW[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - (long)PW[nb] * a % GM) % GM);
    return na * GK + nb;
}

static void setup_group(Cand c) {
    B = c.B;
    GM = c.m;
    GK = c.k;
    G = c.m * c.k;
    V = 2 * B * G;
    NE = B * d;
    PW[0] = 1 % GM;
    for (int b = 1; b < GK; b++) PW[b] = (int)(((long)PW[b - 1] * c.r) % GM);
}

/* ------------------------------------------------------------ state */

static int src[MAXE], tgt[MAXE], vol[MAXE];
static int bsrc[MAXE], btgt[MAXE], bvol[MAXE];
static int NB[MAXV][MAXD];
static int stampA[MAXV], queA[MAXV];
static int stampCtr = 0;
static Cand cand_arr[MAXCAND];
static Cand bestC;

/* Neighbour table of the lift for the current state. Blocks 0..B-1 are A, B..2B-1 are B-side. */
static void build_nb(void) {
    static int AT[MAXBLK][MAXD], AV[MAXBLK][MAXD];
    int cnt[MAXBLK];
    for (int i = 0; i < 2 * B; i++) cnt[i] = 0;
    for (int e = 0; e < NE; e++) {
        int u = src[e], w = B + tgt[e], g = vol[e];
        AT[u][cnt[u]] = w;
        AV[u][cnt[u]] = g;
        cnt[u]++;
        AT[w][cnt[w]] = u;
        AV[w][cnt[w]] = ginv(g);
        cnt[w]++;
    }
    for (int id = 0; id < V; id++) {
        int blk = id / G, x = id % G;
        for (int j = 0; j < d; j++)
            NB[id][j] = AT[blk][j] * G + gmul(x, AV[blk][j]);
    }
}

/* Number of vertices within distance D of vertex s. */
static int bfs_reach(int s) {
    stampCtr++;
    int head = 0, tail = 0;
    queA[tail++] = s;
    stampA[s] = stampCtr;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = queA[head++];
            for (int j = 0; j < d; j++) {
                int u = NB[v][j];
                if (stampA[u] != stampCtr) {
                    stampA[u] = stampCtr;
                    queA[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Sum over blocks of vertices not reached from (block, identity). Zero iff diameter <= D. */
static long cost_state(void) {
    build_nb();
    long c = 0;
    for (int s = 0; s < 2 * B; s++) c += (long)(V - bfs_reach(s * G));
    return c;
}

static int valid_state(void) {
    int ca[MAXB] = {0}, cb[MAXB] = {0};
    for (int e = 0; e < NE; e++) {
        ca[src[e]]++;
        cb[tgt[e]]++;
    }
    for (int i = 0; i < B; i++)
        if (ca[i] != d || cb[i] != d) return 0;
    for (int e = 0; e < NE; e++) {
        if (vol[e] < 0 || vol[e] >= G) return 0;
        for (int f = e + 1; f < NE; f++)
            if (src[e] == src[f] && tgt[e] == tgt[f] && vol[e] == vol[f]) return 0;
    }
    return 1;
}

static int init_state(void) {
    int p[MAXB];
    for (int i = 0; i < d; i++) {
        for (int u = 0; u < B; u++) p[u] = u;
        for (int u = B - 1; u > 0; u--) {
            int j = rndint(u + 1);
            int t = p[u];
            p[u] = p[j];
            p[j] = t;
        }
        for (int u = 0; u < B; u++) {
            int e = i * B + u;
            src[e] = u;
            tgt[e] = p[u];
        }
    }
    for (int e = 0; e < NE; e++) {
        int tries = 0, ok;
        do {
            vol[e] = rndint(G);
            ok = 1;
            for (int f = 0; f < e; f++)
                if (src[f] == src[e] && tgt[f] == tgt[e] && vol[f] == vol[e]) {
                    ok = 0;
                    break;
                }
            tries++;
        } while (!ok && tries < 5000);
        if (!ok) return 0;
    }
    return valid_state();
}

/* One random move: change a voltage, or swap two darts' targets (same source) or sources (same target). */
static void mutate(void) {
    int e = rndint(NE);
    if (rnd01() < 0.5) {
        vol[e] = rndint(G);
        return;
    }
    int f = rndint(NE);
    if (f == e) return;
    if (src[e] == src[f] && tgt[e] != tgt[f]) {
        int t = tgt[e];
        tgt[e] = tgt[f];
        tgt[f] = t;
    } else if (tgt[e] == tgt[f] && src[e] != src[f]) {
        int s = src[e];
        src[e] = src[f];
        src[f] = s;
    }
}

static void save_st(int *os, int *ot, int *ov) {
    memcpy(os, src, sizeof(int) * (size_t)NE);
    memcpy(ot, tgt, sizeof(int) * (size_t)NE);
    memcpy(ov, vol, sizeof(int) * (size_t)NE);
}

static void load_st(const int *os, const int *ot, const int *ov) {
    memcpy(src, os, sizeof(int) * (size_t)NE);
    memcpy(tgt, ot, sizeof(int) * (size_t)NE);
    memcpy(vol, ov, sizeof(int) * (size_t)NE);
}

/* Simulated annealing for one group and block count. Returns 1 when diameter <= D is reached. */
static int search_cand(int idx, double until) {
    Cand c = cand_arr[idx];
    setup_group(c);
    const int iters = 4000;
    int os[MAXE], ot[MAXE], ov[MAXE];
    while (now() < until) {
        if (!init_state()) return 0;
        long cost = cost_state();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            save_st(os, ot, ov);
            mutate();
            if (!valid_state()) {
                load_st(os, ot, ov);
                continue;
            }
            long c2 = cost_state();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                load_st(os, ot, ov);
            }
        }
        if (cost == 0) {
            memcpy(bsrc, src, sizeof(int) * (size_t)NE);
            memcpy(btgt, tgt, sizeof(int) * (size_t)NE);
            memcpy(bvol, vol, sizeof(int) * (size_t)NE);
            bestC = c;
            return 1;
        }
    }
    return 0;
}

static void print_best(void) {
    setup_group(bestC);
    memcpy(src, bsrc, sizeof(int) * (size_t)NE);
    memcpy(tgt, btgt, sizeof(int) * (size_t)NE);
    memcpy(vol, bvol, sizeof(int) * (size_t)NE);
    printf("%d %d\n", V, G * NE);
    for (int e = 0; e < NE; e++)
        for (int x = 0; x < G; x++)
            printf("%d %d\n", src[e] * G + x, (B + tgt[e]) * G + gmul(x, vol[e]));
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->total != y->total) return (x->total < y->total) ? -1 : 1;
    if (x->key != y->key) return (x->key < y->key) ? -1 : 1;
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    /* Candidates: (B, m, k, r) with total = 2*B*m*k vertices, r^k = 1 mod m. */
    int nc = 0;
    static int tmpM[TMPMAX], tmpR[TMPMAX];
    for (int total = lo; total <= hi; total++) {
        for (int Bb = 1; Bb <= MAXB; Bb++) {
            if (total % (2 * Bb)) continue;
            int g = total / (2 * Bb);
            if (g < d || g < 2) continue;
            int cnt = 0;
            for (int m = 2; m <= g; m++) {
                if (g % m) continue;
                int k = g / m;
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1) continue;
                    if (cnt < TMPMAX) {
                        tmpM[cnt] = m;
                        tmpR[cnt] = r;
                        cnt++;
                    }
                }
            }
            if (cnt > KPER) {
                for (int i = 0; i < KPER; i++) {
                    int j = i + rndint(cnt - i);
                    int t = tmpM[i];
                    tmpM[i] = tmpM[j];
                    tmpM[j] = t;
                    t = tmpR[i];
                    tmpR[i] = tmpR[j];
                    tmpR[j] = t;
                }
                cnt = KPER;
            }
            for (int i = 0; i < cnt && nc < MAXCAND; i++) {
                Cand cd;
                cd.B = Bb;
                cd.m = tmpM[i];
                cd.k = g / tmpM[i];
                cd.r = tmpR[i];
                cd.total = total;
                cd.key = 0;
                cand_arr[nc++] = cd;
            }
        }
    }
    for (int i = 0; i < nc; i++) cand_arr[i].key = rnd();
    qsort(cand_arr, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending order: each attempt gets a share of the remaining time. Successes raise
     * the threshold, so later attempts must beat the current best. */
    int best_total = 0, found = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand_arr[ci].total <= best_total) continue;
        int left = nc - ci;
        if (left > 30) left = 30;
        double slice = rem / left;
        if (slice < 0.4) slice = 0.4;
        if (slice > 4.0) slice = 4.0;
        if (slice > rem) slice = rem;
        if (search_cand(ci, now() + slice)) {
            best_total = cand_arr[ci].total;
            found = 1;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    print_best();
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

    # Search: multi-block voltage lifts over semidirect groups, ascending from just
    # above the fallback value (and above a quarter of the Moore bound).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, int(0.25 * mb))
        hi = min(mb // 3, 8000)
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
