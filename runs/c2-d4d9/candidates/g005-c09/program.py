"""Program: multi-orbit voltage lifts over metacyclic groups, with bi-Cayley as the t = 1 case.

Construction:
  * Base bipartite multigraph with BT vertices A_0..A_{BT-1} and BT vertices B_0..B_{BT-1},
    each of degree d. Dart s (block i = s // d) joins A_i to B_{bj[s]} with voltage vg[s].
  * Lift over a metacyclic group G = Z_m x|_r Z_k, order N: vertex (A_i, x) joins
    (B_j, x*g) for each dart (i, j, g). The lift has 2*BT*N vertices, is bipartite, and has
    max degree d. For BT = 1 this is the bi-Cayley family searched by the previous program.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from
    (A_i, e) and (B_j, e) for all base vertices reaches every vertex within D steps.
  * Search: hill climbing on the number of unreached (source, vertex) pairs. Moves swap the
    B-targets of two darts (keeping every B vertex at degree d) or change one voltage.
  * Candidates: for each BT in 1..8, group orders N just above ref/(2*BT) (beating the
    target), then orders just below (fallbacks, including exact ties). Scheduling is
    iterative deepening: each round gives every candidate that can still beat the best a
    slice, and slices double each round.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3300
#define MAXT 8
#define MAXD 8
#define MAXDARTS (MAXT * MAXD)
#define MAXV 12000
#define MAXCAND 256

typedef struct { int bt, m, k, r, N; } Cand;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */
/* Element (a,b) is coded as a*k+b; (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */

static int gm = 1, gk = 1, gN = 1;
static int gpw[MAXN];   /* gpw[b] = r^b mod m, b < k */

static int set_group(int m, int k, int r) {
    if (m < 2 || k < 1 || (long)m * k > MAXN) return 0;
    gm = m;
    gk = k;
    gN = m * k;
    gpw[0] = 1 % m;
    for (int b = 1; b < k; b++) gpw[b] = (int)((long)gpw[b - 1] * r % m);
    return 1;
}

static inline int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int aa = (int)(((long)gpw[b] * c + a) % gm);
    int bb = b + e;
    if (bb >= gk) bb -= gk;
    return aa * gk + bb;
}

static inline int ginv(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    int c = (int)(((long)gpw[nb] * a) % gm);
    c = (gm - c) % gm;
    return c * gk + nb;
}

/* ------------------------------------------------------------ lift state */

static int BT = 1, V = 2;
static int bj[MAXDARTS], vg[MAXDARTS], vgi[MAXDARTS];
static int Bd[MAXT][MAXD];   /* darts incident to B vertex j (exactly d of them) */
static int bk_bj[MAXDARTS], bk_vg[MAXDARTS], bk_vgi[MAXDARTS];
static int bestBJ[MAXDARTS], bestVG[MAXDARTS];
static Cand bestC;
static int have = 0;
static long bestV = 0;

static Cand cand[MAXCAND];
static int nc = 0;
static long gmoore = 0;

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static void rebuild_Bd(void) {
    int cnt[MAXT];
    memset(cnt, 0, sizeof cnt);
    int L = BT * d;
    for (int s = 0; s < L; s++) {
        int j = bj[s];
        Bd[j][cnt[j]++] = s;
    }
}

/* Number of vertices within distance dmax of src. */
static int reach(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int Aend = BT * gN;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < Aend) {
                int i = v / gN, x = v - i * gN;
                for (int k = 0; k < d; k++) {
                    int s = i * d + k;
                    int u = Aend + bj[s] * gN + gmul(x, vg[s]);
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - Aend;
                int j = w / gN, y = w - j * gN;
                for (int k = 0; k < d; k++) {
                    int s = Bd[j][k];
                    int i = s / d;
                    int u = i * gN + gmul(y, vgi[s]);
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sources (A_i, e) and (B_j, e) suffice by left-multiplication symmetry. */
static long cost_now(void) {
    long c = 0;
    int Bstart = BT * gN;
    for (int i = 0; i < BT; i++) c += (long)(V - reach(i * gN, D));
    for (int j = 0; j < BT; j++) c += (long)(V - reach(Bstart + j * gN, D));
    return c;
}

static void randomize_all(void) {
    int L = BT * d;
    int tmp[MAXDARTS];
    int idx = 0;
    for (int j = 0; j < BT; j++)
        for (int k = 0; k < d; k++) tmp[idx++] = j;
    for (int s = L - 1; s > 0; s--) {
        int r = rndint(s + 1);
        int t = tmp[s]; tmp[s] = tmp[r]; tmp[r] = t;
    }
    for (int s = 0; s < L; s++) {
        bj[s] = tmp[s];
        vg[s] = rndint(gN);
        vgi[s] = ginv(vg[s]);
    }
    rebuild_Bd();
}

static void save_state(void) {
    int L = BT * d;
    memcpy(bk_bj, bj, sizeof(int) * (size_t)L);
    memcpy(bk_vg, vg, sizeof(int) * (size_t)L);
    memcpy(bk_vgi, vgi, sizeof(int) * (size_t)L);
}

static void restore_state(void) {
    int L = BT * d;
    memcpy(bj, bk_bj, sizeof(int) * (size_t)L);
    memcpy(vg, bk_vg, sizeof(int) * (size_t)L);
    memcpy(vgi, bk_vgi, sizeof(int) * (size_t)L);
    rebuild_Bd();
}

static void mutate(void) {
    int L = BT * d;
    int done = 0;
    if (BT > 1 && rnd01() < 0.4) {
        int s1 = rndint(L), s2 = rndint(L);
        if (bj[s1] != bj[s2]) {
            int t = bj[s1]; bj[s1] = bj[s2]; bj[s2] = t;
            done = 1;
        }
    }
    if (!done) {
        int s = rndint(L);
        vg[s] = rndint(gN);
        vgi[s] = ginv(vg[s]);
    }
    rebuild_Bd();
}

static int climb(double until) {
    randomize_all();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > 3000) {
            randomize_all();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        save_state();
        mutate();
        long nc2 = cost_now();
        if (nc2 <= cur || rnd01() < 0.01) cur = nc2;
        else restore_state();
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

static int set_candidate(const Cand *c) {
    if (!set_group(c->m, c->k, c->r)) return 0;
    BT = c->bt;
    V = 2 * BT * gN;
    if (V > MAXV) return 0;
    return 1;
}

static void add_groups(int bt, long N, int maxg) {
    if (N < 2 || N > MAXN) return;
    long Vc = 2L * bt * N;
    if (Vc > gmoore || Vc > MAXV) return;
    int got = 0;
    for (long k = 1; k <= N / 2 && got < maxg && nc < MAXCAND; k++) {
        if (N % k) continue;
        long m = N / k;
        if (m < 2) continue;
        int g2 = 0;
        for (long r = 1; r < m && g2 < 2 && got < maxg && nc < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            Cand c;
            c.bt = bt;
            c.m = (int)m;
            c.k = (int)k;
            c.r = (int)r;
            c.N = (int)N;
            cand[nc++] = c;
            got++;
            g2++;
        }
    }
}

static void gen_cands(long target) {
    static const int bts[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    nc = 0;
    /* Pass 1: orders that beat the target (2*bt*N > target). */
    for (int b = 0; b < 8; b++) {
        long Nlo = target / (2L * bts[b]) + 1;
        add_groups(bts[b], Nlo, 4);
        add_groups(bts[b], Nlo + 1, 4);
    }
    /* Pass 2: fallbacks at or just below the target (ties and near-ties). */
    for (int b = 0; b < 8; b++) {
        long Nlo = target / (2L * bts[b]) + 1;
        add_groups(bts[b], Nlo - 1, 8);
        add_groups(bts[b], Nlo - 2, 3);
    }
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static int emit_best(void) {
    if (!set_group(bestC.m, bestC.k, bestC.r)) return 0;
    BT = bestC.bt;
    V = 2 * BT * gN;
    int L = BT * d;
    for (int s = 0; s < L; s++) {
        bj[s] = bestBJ[s];
        vg[s] = bestVG[s];
        vgi[s] = ginv(vg[s]);
    }
    rebuild_Bd();
    if (cost_now() != 0) return 0;

    int half = BT * gN;
    int cap = half * d;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    if (!eu || !ev) { free(eu); free(ev); return 0; }
    int m = 0;
    for (int i = 0; i < BT; i++) {
        for (int x = 0; x < gN; x++) {
            int A = i * gN + x;
            int nb[MAXD];
            int cntn = 0;
            for (int k = 0; k < d; k++) {
                int s = i * d + k;
                nb[cntn++] = half + bj[s] * gN + gmul(x, vg[s]);
            }
            for (int p = 1; p < cntn; p++) {
                int v = nb[p], q = p - 1;
                while (q >= 0 && nb[q] > v) { nb[q + 1] = nb[q]; q--; }
                nb[q + 1] = v;
            }
            for (int p = 0; p < cntn; p++) {
                if (p == 0 || nb[p] != nb[p - 1]) {
                    eu[m] = A;
                    ev[m] = nb[p];
                    m++;
                }
            }
        }
    }
    printf("%d %d\n", V, m);
    for (int p = 0; p < m; p++) printf("%d %d\n", eu[p], ev[p]);
    free(eu);
    free(ev);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    gmoore = moore_bound();
    gen_cands(ref);
    if (nc == 0) { print_complete(); return 0; }

    double budget0 = t_end - now();
    double base_slice = budget0 / (2.0 * (double)nc);
    if (base_slice < 0.12) base_slice = 0.12;

    for (int round = 0; round < 12; round++) {
        for (int i = 0; i < nc; i++) {
            double remaining = t_end - now();
            if (remaining < 0.1) break;
            const Cand *c = &cand[i];
            long Vc = 2L * c->bt * c->N;
            if (Vc <= bestV) continue;
            if (!set_candidate(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                int L = BT * d;
                memcpy(bestBJ, bj, sizeof(int) * (size_t)L);
                memcpy(bestVG, vg, sizeof(int) * (size_t)L);
                bestC = *c;
                have = 1;
                bestV = V;
            }
        }
        if (t_end - now() < 0.1) break;
    }

    if (!have || !emit_best()) print_complete();
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


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
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        ref = REF_VERTICES.get((d, D), best[0])
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
