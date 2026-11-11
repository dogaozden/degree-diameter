"""Two-stage voltage-lift search for the bipartite degree-diameter problem.

Stage 1 is the parent's single-group Haar lift (base: one vertex per side, d parallel
darts), kept as the fallback. Stage 2 is the new, different construction: a base graph
with kb = 2 vertices per side. Each base graph is d permutations (layers) of kb
vertices, and every dart carries a voltage in an affine group F_q x| H. The lift has
2*kb*|G| vertices and is d-regular and bipartite. Left translations are automorphisms,
so the diameter check needs only 2*kb BFS runs. Simulated annealing moves voltages and
swaps heads within a layer. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Voltage-lift search over affine groups.
 * Usage: prog d D seed time_limit kb lo hi     (stdin ignored)
 * kb = base vertices per side. Group order N in [lo, hi].
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
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
#define MAXN 8192
#define MAXD 32
#define MAXK 4
#define MAXE (MAXD * MAXK)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 8192

typedef struct { int q, p, kd, c, N; } Cand;

static int d, D, kb;
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

static int factor_pp(int q, int *p, int *kd) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *kd = kk;
    return 1;
}

static int polymul(int a, int b, int p, int kd, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < kd; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * kd; i++) prod[i] = 0;
    for (int i = 0; i < kd; i++)
        for (int j = 0; j < kd; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * kd - 2; deg >= kd; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < kd; i++) {
            int idx = deg - kd + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < kd; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int kd) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= kd; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < kd; i++)
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
        for (int i = 0; i < kd; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, kd, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, kd, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(int q, int p, int kd, int c) {
    build_field(q, p, kd);
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
}

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

/* ------------------------------------------------------------ voltage lift state
 * Left vertex L_{i,g} = i*N + g, right vertex R_{j,h} = kb*N + j*N + h.
 * Dart e = t*kb + i goes from left i to right perm[t][i] with voltage volt[e]:
 * L_{i,g} ~ R_{perm[t][i], g*volt[e]}. Each layer t is a permutation, so every
 * vertex has degree d. Left translations are automorphisms, so only BFS from the
 * 2*kb base vertices is needed. */

static int perm[MAXD][MAXK], invp[MAXD][MAXK];
static int volt[MAXE];
static int gf[MAXE][MAXN], gb[MAXE][MAXN];
static int bestPerm[MAXD][MAXK], bestVolt[MAXE];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_volt(int e, int x) {
    volt[e] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        gf[e][g] = gmul(g, x);
        gb[e][g] = gmul(g, xi);
    }
}

static void swap_heads(int t, int i, int i2) {
    int tmp = perm[t][i];
    perm[t][i] = perm[t][i2];
    perm[t][i2] = tmp;
    invp[t][perm[t][i]] = i;
    invp[t][perm[t][i2]] = i2;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int KN = kb * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / GN, g = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int e = t * kb + i;
                    int j = perm[t][i];
                    int u = KN + j * GN + gf[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - KN;
                int j = w / GN, h = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int i = invp[t][j];
                    int e = t * kb + i;
                    int u = i * GN + gb[e][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Duplicate darts (same left vertex, same head, same voltage) make a multi-edge. */
static long dup_pen(void) {
    long pen = 0;
    for (int i = 0; i < kb; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = t + 1; t2 < d; t2++)
                if (perm[t][i] == perm[t2][i] && volt[t * kb + i] == volt[t2 * kb + i])
                    pen++;
    return pen;
}

static long full_cost(void) {
    long V = 2L * kb * GN;
    long c = 0;
    for (int i = 0; i < kb; i++) c += V - bfs_count(i * GN);
    for (int j = 0; j < kb; j++) c += V - bfs_count(kb * GN + j * GN);
    return c + dup_pen() * V;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < kb; i++) perm[t][i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = perm[t][i];
            perm[t][i] = perm[t][r];
            perm[t][r] = tmp;
        }
        for (int i = 0; i < kb; i++) invp[t][perm[t][i]] = i;
    }
    for (int e = 0; e < d * kb; e++) set_volt(e, rndint(GN));
}

static void save_best(void) {
    memcpy(bestPerm, perm, sizeof(perm));
    memcpy(bestVolt, volt, sizeof(volt));
}

/* Simulated annealing on the current group. Returns 1 when cost 0 is reached,
 * 0 on timeout. */
static int search_group(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_state();
        long cost = full_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            long c2;
            if (kb >= 2 && rndint(10) < 3) {
                int t = rndint(d);
                int i = rndint(kb);
                int i2 = rndint(kb - 1);
                if (i2 >= i) i2++;
                swap_heads(t, i, i2);
                c2 = full_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                    cost = c2;
                else
                    swap_heads(t, i, i2);
            } else {
                int e = rndint(d * kb);
                int old = volt[e];
                int x = rndint(GN);
                set_volt(e, x);
                c2 = full_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                    cost = c2;
                else
                    set_volt(e, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int KN = kb * GN;
    memcpy(perm, bestPerm, sizeof(perm));
    for (int t = 0; t < d; t++)
        for (int i = 0; i < kb; i++) invp[t][perm[t][i]] = i;
    for (int e = 0; e < d * kb; e++) set_volt(e, bestVolt[e]);
    printf("%d %d\n", 2 * KN, KN * d);
    for (int i = 0; i < kb; i++)
        for (int g = 0; g < GN; g++)
            for (int t = 0; t < d; t++) {
                int e = t * kb + i;
                int j = perm[t][i];
                printf("%d %d\n", i * GN + g, KN + j * GN + gf[e][g]);
            }
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
    kb = atoi(argv[5]);
    int lo = atoi(argv[6]), hi = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || kb < 1 || kb > MAXK) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2) lo = 2;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, kd;
        if (!factor_pp(q, &p, &kd)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, kd, c, (int)N};
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

    /* Phase 1: binary search over the group order. Each probe gets an equal share
     * of the remaining time over the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].kd, cand[mid].c);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                save_best();
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].kd, cand[idx].c);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            save_best();
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
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].kd, cand[best_idx].c);
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


def _run_lift(d, D, seed, budget, kb, lo, hi):
    """Run the C voltage-lift engine with kb base vertices per side; return (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), kb, lo, hi],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 4.0:
            # Stage 1: single-vertex-per-side Haar lift (the parent's construction),
            # kept as the fallback for the case.
            b1 = 0.45 * budget
            lo1 = max(best[0] // 2 + 1, mb // 8)
            hi1 = mb // 2
            if lo1 <= hi1:
                try:
                    consider(_run_lift(d, D, seed, b1, 1, lo1, hi1))
                except Exception:
                    pass

            # Stage 2: base graphs with 2 vertices per side (2 x 2 voltage structure),
            # using the remaining time. A graph on 4N vertices needs 4N <= Moore bound.
            b2 = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
            lo2 = max(best[0] // 4 + 1, mb // 16)
            hi2 = mb // 4
            if b2 > 4.0 and lo2 <= hi2:
                try:
                    consider(_run_lift(d, D, seed + 1, b2, 2, lo2, hi2))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
