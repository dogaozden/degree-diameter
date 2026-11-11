"""Program: multi-orbit voltage lifts over metacyclic groups (base graph with B vertices per side).

New construction (this island): a bipartite lift of a small base multigraph.
  * Base: B vertices A_0..A_{B-1} and B vertices B_0..B_{B-1}. Each base vertex has degree d.
    The base is a union of d random permutations (dart (p, i) joins A_i to B_{perm_p(i)}),
    kept only if the base is connected.
  * Voltages: each dart t gets a group element g_t of G (metacyclic Z_m x| Z_k, order N).
    The lift has vertices (A_i, x) and (B_j, y), with edge (A_i, x)-(B_j, x*g_t) for every dart.
    Distinct darts between the same pair must carry distinct voltages (no parallel edges).
  * Order = 2*B*N, degree = d, bipartite by construction.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from the
    2B representatives (A_i, e) and (B_j, e) reaches everything within D steps.
  * Search: simulated annealing over the voltages, with restarts that also redraw the base.

Target sizes: B=2 lifts with N just above record/4 (4 orbits, order 4N > 4970), then B=3, B=4,
and B=1 bi-Cayley graphs as the record-matching fallback (N = record/2). Iterative deepening
schedules the candidates. Safety: C prints K_{d,d} if nothing is found; Python validates the
output with lib.is_valid and keeps the best valid graph.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3000
#define MAXB 4
#define MAXD 8
#define MAXDART (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXC 160
#define STALL 30000

static int d, D;
static int B = 1;
static int N = 0;
static int OFF = 0, V = 0, E = 0;
static double t_end;

static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

/* Element (a,b) is coded a*k+b; (a,b)(c,d) = (a + r^b c, b + d). Identity is 0. */
static int build_group(int m, int k, int r) {
    int n = m * k;
    if (m < 2 || k < 1 || n > MAXN) return 0;
    static int pw[MAXN];
    free(T);
    free(INV);
    N = n;
    T = malloc(sizeof(uint16_t) * (size_t)N * (size_t)N);
    INV = malloc(sizeof(int) * (size_t)N);
    if (!T || !INV) exit(3);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (T[(size_t)x * N + y] == 0) { INV[x] = y; break; }
    }
    return 1;
}

/* ------------------------------------------------------------ lift structure */

static int perm[MAXD][MAXB];
static int bestperm[MAXD][MAXB];
static int fr[MAXDART], to[MAXDART];
static int gv[MAXDART], gi[MAXDART];
static int bestgv[MAXDART];
static int inl[MAXB][MAXD];          /* inl[j][p] = dart from perm p ending at B_j */
static int R[MAXDART][MAXN];         /* R[t][x]  = x * g_t */
static int RI[MAXDART][MAXN];        /* RI[t][y] = y * g_t^{-1} */

/* Dart t = p*B + i joins A_i to B_{perm[p][i]}. Each vertex then has exactly d darts. */
static void set_structure(void) {
    E = B * d;
    OFF = B * N;
    V = 2 * OFF;
    for (int p = 0; p < d; p++)
        for (int i = 0; i < B; i++) {
            int t = p * B + i;
            fr[t] = i;
            to[t] = perm[p][i];
            inl[perm[p][i]][p] = t;
        }
}

static int ufp[2 * MAXB];
static int uf_find(int x) {
    while (ufp[x] != x) { ufp[x] = ufp[ufp[x]]; x = ufp[x]; }
    return x;
}

/* Random base: d random permutations, resampled until the base is connected. */
static int random_structure(void) {
    for (int attempt = 0; attempt < 500; attempt++) {
        for (int p = 0; p < d; p++) {
            for (int i = 0; i < B; i++) perm[p][i] = i;
            for (int i = B - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = perm[p][i];
                perm[p][i] = perm[p][j];
                perm[p][j] = tmp;
            }
        }
        for (int i = 0; i < 2 * B; i++) ufp[i] = i;
        for (int p = 0; p < d; p++)
            for (int i = 0; i < B; i++) {
                int a = uf_find(i), b = uf_find(B + perm[p][i]);
                if (a != b) ufp[a] = b;
            }
        int root = uf_find(0), ok = 1;
        for (int i = 1; i < 2 * B; i++)
            if (uf_find(i) != root) { ok = 0; break; }
        if (ok) { set_structure(); return 1; }
    }
    return 0;
}

static void set_dart(int t, int g) {
    gv[t] = g;
    gi[t] = INV[g];
    for (int x = 0; x < N; x++) {
        R[t][x] = (int)T[(size_t)x * N + g];
        RI[t][x] = (int)T[(size_t)x * N + gi[t]];
    }
}

/* Two darts on the same base pair must differ, or the lift gets parallel edges. */
static int voltage_ok(int t, int g) {
    for (int s = 0; s < E; s++)
        if (s != t && fr[s] == fr[t] && to[s] == to[t] && gv[s] == g) return 0;
    return 1;
}

static void random_voltages(void) {
    for (int t = 0; t < E; t++) gv[t] = -1;
    for (int t = 0; t < E; t++) {
        int g;
        do g = rndint(N); while (!voltage_ok(t, g));
        set_dart(t, g);
    }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of vertices within distance D of src (src included). */
static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail && tail < V; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head], u;
            if (v < OFF) {
                int i = v / N, x = v - i * N;
                for (int p = 0; p < d; p++) {
                    int t = p * B + i;
                    u = OFF + to[t] * N + R[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - OFF, j = w / N, y = w - j * N;
                for (int p = 0; p < d; p++) {
                    int t = inl[j][p];
                    u = fr[t] * N + RI[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base representatives of the number of vertices they cannot reach within D. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < B; i++) {
        c += (long)(V - ball(i * N));
        c += (long)(V - ball(OFF + i * N));
    }
    return c;
}

/* ------------------------------------------------------------ annealing */

static int climb(double until) {
    if (!random_structure()) return 0;
    random_voltages();
    long cur = cost_now(), best = cur, stall = 0, it = 0;
    double Tm = 2.0;
    while (cur > 0) {
        if ((++it & 31) == 0 && now() > until) return 0;
        if (stall > STALL) {
            if (!random_structure()) return 0;
            random_voltages();
            cur = cost_now();
            best = cur;
            stall = 0;
            Tm = 2.0;
            continue;
        }
        int t = rndint(E);
        int g = rndint(N);
        if (g == gv[t] || !voltage_ok(t, g)) { stall++; continue; }
        int old = gv[t];
        set_dart(t, g);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / Tm)) cur = nc;
        else set_dart(t, old);
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
        Tm *= 0.9998;
        if (Tm < 0.25) Tm = 0.25;
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int B, N, m, k, r, weight; } Cand;
static Cand cands[MAXC];
static int ncand = 0;

/* Metacyclic groups of order Nv: k = 1 gives cyclic, k > 1 needs r != 1 (nonabelian). */
static void add_groups(int Bv, int Nv, int weight, int cap) {
    int got = 0;
    for (int k = 1; k <= Nv && got < cap && ncand < MAXC; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 2) continue;
        for (int r = 1; r < m && got < cap && ncand < MAXC; r++) {
            if (k > 1 && r == 1) continue;
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            Cand c;
            c.B = Bv; c.N = Nv; c.m = m; c.k = k; c.r = r; c.weight = weight;
            cands[ncand++] = c;
            got++;
        }
    }
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    printf("%d %d\n", V, E * N);
    for (int t = 0; t < E; t++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", fr[t] * N + x, OFF + to[t] * N + R[t][x]);
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

    long moore = moore_bound();

    /* Fallback first: B=1 bi-Cayley at the record half (ties the record if found). */
    if (ref % 2 == 0 && ref / 2 >= 3 && ref / 2 <= MAXN)
        add_groups(1, (int)(ref / 2), 8, 2);

    /* Main targets: B=2, then B=3, B=4, each just above the record vertex count. */
    for (int Bv = 2; Bv <= MAXB; Bv++) {
        long lo = ref / (2L * Bv) + 1;
        long span = (Bv == 2) ? 6 : (Bv == 3 ? 3 : 2);
        for (long Nv = lo; Nv < lo + span && Nv <= MAXN; Nv++) {
            if (2L * Bv * Nv > moore) break;
            add_groups(Bv, (int)Nv, 1, 2);
        }
    }
    /* Extra B=1 bi-Cayley graphs above the record. */
    long lo1 = ref / 2 + 1;
    for (long Nv = lo1; Nv < lo1 + 2 && Nv <= MAXN; Nv++) {
        if (2L * Nv > moore) break;
        add_groups(1, (int)Nv, 1, 2);
    }

    double budget0 = t_end - now();
    if (budget0 < 0.5 || ncand == 0) { print_complete(); return 0; }
    double base = budget0 / (4.0 * (double)ncand);
    if (base < 0.25) base = 0.25;

    int have = 0;
    long bV = 0;
    Cand bc;
    memset(&bc, 0, sizeof bc);

    /* Iterative deepening: each round gives every candidate that can still beat the
       current best a slice; slices double per round. */
    for (int rd = 0; rd < 12; rd++) {
        for (int i = 0; i < ncand; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &cands[i];
            long V2 = 2L * c->B * c->N;
            if (V2 <= bV || V2 > moore) continue;
            if (!build_group(c->m, c->k, c->r)) continue;
            B = c->B;
            double slice = base * (double)(1L << rd) * (double)c->weight;
            if (slice > rem) slice = rem;
            if (climb(now() + slice)) {
                have = 1;
                bV = V2;
                bc = *c;
                memcpy(bestperm, perm, sizeof perm);
                memcpy(bestgv, gv, sizeof(int) * (size_t)E);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!build_group(bc.m, bc.k, bc.r)) { print_complete(); return 0; }
    B = bc.B;
    memcpy(perm, bestperm, sizeof perm);
    set_structure();
    for (int t = 0; t < E; t++) set_dart(t, bestgv[t]);
    if (cost_now() != 0) { print_complete(); return 0; }
    print_graph();
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), max(best[0], 2 * d))
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
