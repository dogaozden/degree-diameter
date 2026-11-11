"""Multi-orbit affine lifts for the bipartite degree-diameter problem.

New construction: the parent searches Haar graphs on one group G = F_q x| H, where a
single voltage set S gives a bipartite graph with one orbit per side. This version
uses a base graph with B left and B right vertices (B = 1, 2, 3). The base has d
slots. Slot k sends left vertex i to right vertex pi_k(i), for a permutation pi_k of
{0..B-1}, with voltage v_{k,i} in G. The lift has vertices L_{i,x} and R_{j,y} for
x, y in G, and edges L_{i,x} ~ R_{pi_k(i), x*v_{k,i}}.

Each left and each right vertex has degree d, because every pi_k is a permutation.
Left multiplication by h in G is an automorphism, and it is transitive on each class
L_{i,*} and R_{j,*}. So diameter <= D reduces to 2B BFS runs, from L_{i,e} and R_{j,e}.
Two darts from the same i to the same j with equal voltage would make a multi-edge.
Such pairs are penalised in the cost.

Simulated annealing changes one voltage, or re-draws the permutation of one slot. The
order budget is split between B = 1 (the parent's family), B = 2 and B = 3. Every
returned graph is checked with lib.is_valid, with the K_{d,d} and projective-plane
fallbacks kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine lift search.
 * Usage: prog d D seed time_limit lo hi B     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4096
#define MAXD 32
#define MAXB 3
#define MAXCAND 16384

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, B;
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

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int GINV[MAXN];

/* Element (a, h_j) is coded a*c + j, h_j = g^(j*(q-1)/c); product (a,h_j)(b,h_t) = (a + h_j*b, h_j*h_t). */
static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
    for (int x = 0; x < GN; x++) GINV[x] = ginv(x);
}

/* ------------------------------------------------------------ multi-orbit lift state */

/* Slot k: left i joins right PERM[k][i] with voltage VOLT[k][i].
 * FW[k][i][x] = x*v (right index in its class), BW[k][j][y] = y*v^-1 for the left i = PINV[k][j]. */
static int PERM[MAXD][MAXB], PINV[MAXD][MAXB], VOLT[MAXD][MAXB];
static int FW[MAXD][MAXB][MAXN], BW[MAXD][MAXB][MAXN];
static int bestP[MAXD][MAXB], bestV[MAXD][MAXB];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static void rebuild_slot(int k) {
    int N = GN;
    for (int i = 0; i < B; i++) PINV[k][PERM[k][i]] = i;
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            FW[k][i][x] = gmul(x, VOLT[k][i]);
    for (int j = 0; j < B; j++) {
        int i = PINV[k][j];
        int gi = GINV[VOLT[k][i]];
        for (int y = 0; y < N; y++)
            BW[k][j][y] = gmul(y, gi);
    }
}

static void rebuild_all(void) {
    for (int k = 0; k < d; k++) rebuild_slot(k);
}

/* Number of vertices within distance D of src. Vertices: L_{i,x} = i*N + x, R_{j,y} = B*N + j*N + y. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < B * N) {
                int i = v / N, x = v % N;
                for (int k = 0; k < d; k++) {
                    int u = B * N + PERM[k][i] * N + FW[k][i][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - B * N, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int i = PINV[k][j];
                    int u = i * N + BW[k][j][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left-multiplication is an automorphism, so BFS from one representative per class suffices.
 * Duplicate darts (same i, same j, same voltage) are penalised heavily. */
static long total_cost(void) {
    int N = GN, V = 2 * B * N;
    long cost = 0;
    for (int i = 0; i < B; i++) cost += V - bfs_count(i * N);
    for (int j = 0; j < B; j++) cost += V - bfs_count(B * N + j * N);
    long dup = 0;
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++)
            for (int k2 = k + 1; k2 < d; k2++)
                if (PERM[k][i] == PERM[k2][i] && VOLT[k][i] == VOLT[k2][i]) dup++;
    cost += dup * (long)(2 * N);
    return cost;
}

static void random_perm(int *p) {
    for (int i = 0; i < B; i++) p[i] = i;
    for (int i = B - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

static void save_state(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < B; i++) {
            bestP[k][i] = PERM[k][i];
            bestV[k][i] = VOLT[k][i];
        }
}

/* Simulated annealing over slot permutations and voltages in the current group.
 * Returns 1 at cost 0, 0 on timeout. */
static int search_multi(double until) {
    int N = GN;
    const int iters = 6000;
    while (now() < until) {
        for (int k = 0; k < d; k++) {
            random_perm(PERM[k]);
            for (int i = 0; i < B; i++) VOLT[k][i] = rndint(N);
            rebuild_slot(k);
        }
        long cost = total_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(d);
            int saveP[MAXB], saveV[MAXB];
            memcpy(saveP, PERM[k], sizeof(int) * (size_t)B);
            memcpy(saveV, VOLT[k], sizeof(int) * (size_t)B);
            if (B > 1 && rnd01() < 0.3) {
                random_perm(PERM[k]);
            } else {
                int i = rndint(B);
                VOLT[k][i] = rndint(N);
            }
            rebuild_slot(k);
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                memcpy(PERM[k], saveP, sizeof(int) * (size_t)B);
                memcpy(VOLT[k], saveV, sizeof(int) * (size_t)B);
                rebuild_slot(k);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * B * N, B * N * d);
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, B * N + PERM[k][i] * N + FW[k][i][x]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    B = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || B < 1 || B > MAXB) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search over orders, with equal time slices per remaining probe. */
    int a = 0, bb = nc - 1;
    while (a <= bb && now() < t_end) {
        int mid = (a + bb) / 2;
        int span = bb - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_multi(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                save_state();
            }
            a = mid + 1;
        } else {
            bb = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_multi(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            save_state();
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    for (int k = 0; k < d; k++)
        for (int i = 0; i < B; i++) {
            PERM[k][i] = bestP[k][i];
            VOLT[k][i] = bestV[k][i];
        }
    rebuild_all();
    if (total_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    print_result();
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

    # Multi-orbit affine lifts with B left and B right base vertices.
    # A lift on 2*B*N vertices needs 2*B*N <= moore_bound.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        plan = [(1, 0.45), (2, 0.5), (3, 1.0)]
        for B, frac in plan:
            avail = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
            budget = avail * frac
            if budget < 3.0:
                continue
            lo = max(best[0] // (2 * B) + 1, mb // (8 * B), 2 * d)
            hi = min(mb // (2 * B), 4096)
            if lo > hi:
                continue
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, B],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the best valid graph so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
