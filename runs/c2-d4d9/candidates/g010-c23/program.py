"""Program: multi-orbit voltage lifts with resumable simulated annealing.

New in this version (the parent used only one orbit per side):
  * Base graph with P <= 4 vertices A_0..A_{P-1} and B_0..B_{P-1}. Each A_i has d darts. Dart (i,k)
    goes to B_{t(i,k)} with voltage g(i,k) in a metacyclic group G of order N. Lift: A_i x ~ B_t(x*g).
    That gives 2PN vertices and degree d. Each B_j receives exactly d darts (balance is kept by moves).
  * Left multiplication by G is an automorphism with 2P orbits, so the diameter condition reduces to
    BFS from A_i e and B_i e (2P sources), checked with the on-the-fly neighbour rule (no edge list).
  * Moves: change one voltage, or swap the targets of two darts. Duplicate darts are rejected.
    Cost = number of unreached pairs within D from the 2P sources. Annealing uses an adaptive temperature.
  * Each candidate (P, N, group) keeps its annealing state between rounds, so no time is wasted on restarts.
    Candidates: a few sizes at or just below the record (fallback), then evenly spaced sizes just above it.
    Round-robin with doubling slices; a candidate is skipped once it cannot beat the current best.
  * The C engine verifies the final graph fully before printing. Python validates again with lib.is_valid
    and keeps the best valid graph.
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

#define MAXN 3072
#define MAXP 4
#define MAXD 8
#define MAXV (2 * MAXP * MAXN)
#define MAXC 40
#define MAXPAIRS 4096
#define STALL 30000

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

/* ------------------------------------------------------------ group
   Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static int N = 0;
static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y */
static int INV[MAXN];
static int EA[MAXN], EB[MAXN], PW[MAXN];

static void build_group(int m, int k, int r) {
    int n = m * k;
    N = n;
    for (int x = 0; x < n; x++) { EA[x] = x / k; EB[x] = x % k; }
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = EA[x], b = EB[x];
        uint16_t *row = T + (size_t)x * n;
        for (int y = 0; y < n; y++) {
            int c = EA[y], e = EB[y];
            int aa = (a + PW[b] * c) % m;
            int bb = b + e;
            if (bb >= k) bb -= k;
            row[y] = (uint16_t)(aa * k + bb);
        }
    }
    for (int x = 0; x < n; x++) {
        INV[x] = 0;
        const uint16_t *row = T + (size_t)x * n;
        for (int y = 0; y < n; y++) if (row[y] == 0) { INV[x] = y; break; }
    }
}

/* ------------------------------------------------------------ lift state
   A_i x -> index i*N+x, B_j y -> index (P+j)*N+y. Dart (i,k): B_{tg[i][k]}, voltage vl[i][k]. */
static int P = 1;
static int V = 0;
static int tg[MAXP][MAXD], vl[MAXP][MAXD];
static int incD[MAXP][MAXD];     /* incoming darts of B_j, code i*MAXD+k */
static int stamp[MAXV];
static int tick_ = 0;
static int qv[MAXV];

static void rebuild_inc(void) {
    int cnt[MAXP];
    for (int j = 0; j < P; j++) cnt[j] = 0;
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) {
            int j = tg[i][k];
            incD[j][cnt[j]++] = i * MAXD + k;
        }
}

static int ball(int src) {
    if (++tick_ == 0x7fffffff) { memset(stamp, 0, sizeof stamp); tick_ = 1; }
    const int PN = P * N;
    int head = 0, tail = 0;
    stamp[src] = tick_;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                const uint16_t *row = T + (size_t)x * N;
                for (int k = 0; k < d; k++) {
                    int u = (P + tg[i][k]) * N + row[vl[i][k]];
                    if (stamp[u] != tick_) { stamp[u] = tick_; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                const uint16_t *row = T + (size_t)y * N;
                for (int c = 0; c < d; c++) {
                    int dc = incD[j][c];
                    int i = dc / MAXD, k = dc % MAXD;
                    int u = i * N + row[INV[vl[i][k]]];
                    if (stamp[u] != tick_) { stamp[u] = tick_; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sources A_i e and B_i e cover all orbit representatives (G acts by left multiplication). */
static long eval_cost(void) {
    long Vn = 2L * P * N, tot = 0;
    for (int i = 0; i < P; i++) {
        tot += Vn - ball(i * N);
        tot += Vn - ball((P + i) * N);
    }
    return tot;
}

static int dup_row(int i) {
    for (int a = 0; a < d; a++)
        for (int b = a + 1; b < d; b++)
            if (tg[i][a] == tg[i][b] && vl[i][a] == vl[i][b]) return 1;
    return 0;
}

static void random_init(void) {
    int slots[MAXP * MAXD];
    int ns = P * d, t = 0;
    for (int j = 0; j < P; j++)
        for (int r = 0; r < d; r++) slots[t++] = j;
    for (int a = ns - 1; a > 0; a--) {
        int b = rndint(a + 1);
        int tmp = slots[a]; slots[a] = slots[b]; slots[b] = tmp;
    }
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) {
            tg[i][k] = slots[i * d + k];
            vl[i][k] = rndint(N);
        }
    for (int i = 0; i < P; i++)
        while (dup_row(i)) {
            int k = rndint(d);
            vl[i][k] = rndint(N);
        }
    rebuild_inc();
}

static void swap_int(int *a, int *b) { int t = *a; *a = *b; *b = t; }

/* Simulated annealing from the current state; returns 1 if a valid lift was found (state restored to best). */
static long climb(double until) {
    int btg[MAXP][MAXD], bvl[MAXP][MAXD];
    rebuild_inc();
    long cur = eval_cost();
    long bestc = cur;
    memcpy(btg, tg, sizeof tg);
    memcpy(bvl, vl, sizeof vl);
    long stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) break;
        if (stall > STALL) {
            random_init();
            cur = eval_cost();
            stall = 0;
            continue;
        }
        int type = (P > 1 && rndint(2) == 0) ? 1 : 0;
        int i1 = 0, k1 = 0, i2 = 0, k2 = 0, oldv = 0;
        if (type == 0) {
            i1 = rndint(P);
            k1 = rndint(d);
            oldv = vl[i1][k1];
            int g = rndint(N);
            if (g == oldv) continue;
            vl[i1][k1] = g;
            if (dup_row(i1)) { vl[i1][k1] = oldv; continue; }
        } else {
            int t1 = rndint(P * d), t2 = rndint(P * d);
            i1 = t1 / d; k1 = t1 % d;
            i2 = t2 / d; k2 = t2 % d;
            if (tg[i1][k1] == tg[i2][k2]) continue;
            swap_int(&tg[i1][k1], &tg[i2][k2]);
            if (dup_row(i1) || (i2 != i1 && dup_row(i2))) {
                swap_int(&tg[i1][k1], &tg[i2][k2]);
                continue;
            }
        }
        rebuild_inc();
        long nw = eval_cost();
        long delta = nw - cur;
        double temp = 0.3 + 0.01 * (double)cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nw;
            if (cur < bestc) {
                bestc = cur;
                stall = 0;
                memcpy(btg, tg, sizeof tg);
                memcpy(bvl, vl, sizeof vl);
            } else {
                stall++;
            }
        } else {
            if (type == 0) vl[i1][k1] = oldv;
            else swap_int(&tg[i1][k1], &tg[i2][k2]);
            rebuild_inc();
            stall++;
        }
    }
    memcpy(tg, btg, sizeof tg);
    memcpy(vl, bvl, sizeof vl);
    rebuild_inc();
    return bestc == 0;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int V, P, N; } Pair;

static int cmp_pair(const void *a, const void *b) {
    const Pair *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->P - y->P;
}

typedef struct {
    int V, P, N, m, k, r, inited;
    int tg[MAXP][MAXD], vl[MAXP][MAXD];
} Cand;

static Cand cands[MAXC];
static int nc = 0;
static int cur_cand = -1;

static void pick_group(Cand *c) {
    static int om[512], ok_[512], orr[512];
    int Nv = c->N, no = 0;
    for (int k = 2; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        for (int r = 2; r < m; r++) {
            if (no >= 512) break;
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            om[no] = m; ok_[no] = k; orr[no] = r;
            no++;
        }
    }
    if (no == 0) { c->m = Nv; c->k = 1; c->r = 1; return; }
    int t = rndint(no);
    c->m = om[t];
    c->k = ok_[t];
    c->r = orr[t];
}

static void add_even(const Pair *L, int n, int K) {
    int kk = n < K ? n : K;
    if (kk <= 0) return;
    for (int t = 0; t < kk && nc < MAXC; t++) {
        int idx = (kk == 1) ? 0 : (int)((long)t * (n - 1) / (kk - 1));
        Cand *c = &cands[nc++];
        memset(c, 0, sizeof *c);
        c->V = L[idx].V;
        c->P = L[idx].P;
        c->N = L[idx].N;
        pick_group(c);
    }
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    double usable = limit - 3.0;
    if (usable < 0.5 * limit) usable = 0.5 * limit;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }
    long moore = moore_bound();

    double lowD = 0.90 * (double)ref;
    double highD = 1.12 * (double)ref;
    if (highD > (double)moore) highD = (double)moore;

    static Pair pairs[MAXPAIRS];
    static Pair LA[MAXPAIRS], LB[MAXPAIRS];
    int np = 0;
    for (int p = 1; p <= MAXP; p++) {
        long nlo = ((long)lowD + 2L * p - 1) / (2L * p);
        long nhi = (long)highD / (2L * p);
        for (long Nv = nlo; Nv <= nhi && np < MAXPAIRS; Nv++) {
            long Vv = 2L * p * Nv;
            if (Nv < 3 || Nv > MAXN || Vv > moore) continue;
            pairs[np].V = (int)Vv;
            pairs[np].P = p;
            pairs[np].N = (int)Nv;
            np++;
        }
    }
    qsort(pairs, (size_t)np, sizeof(Pair), cmp_pair);
    int na = 0, nb = 0;
    for (int i = 0; i < np; i++) {
        if (pairs[i].V <= ref) LA[na++] = pairs[i];
        else LB[nb++] = pairs[i];
    }
    nc = 0;
    add_even(LA, na, 5);            /* fallbacks at or below the reference, last one = largest */
    add_even(LB, nb, MAXC - 5);     /* targets just above the reference */
    if (nc == 0) { print_complete(); return 0; }

    int bestV = 0, bestI = -1;
    double budget = t_end - now();
    double base = budget / (3.0 * (double)nc);
    if (base < 0.1) base = 0.1;

    int stop = 0;
    for (int round = 0; round < 40 && !stop; round++) {
        int any = 0;
        for (int i = 0; i < nc && !stop; i++) {
            Cand *c = &cands[i];
            if (c->V <= bestV) continue;
            double remaining = t_end - now();
            if (remaining < 0.1) { stop = 1; break; }
            double slice = base * (double)(1L << (round < 20 ? round : 20));
            if (slice > remaining) slice = remaining;
            if (cur_cand != i) {
                build_group(c->m, c->k, c->r);
                cur_cand = i;
            }
            P = c->P;
            V = 2 * P * N;
            if (!c->inited) {
                random_init();
                c->inited = 1;
            } else {
                memcpy(tg, c->tg, sizeof tg);
                memcpy(vl, c->vl, sizeof vl);
                rebuild_inc();
            }
            any = 1;
            int ok = (int)climb(now() + slice);
            memcpy(c->tg, tg, sizeof tg);
            memcpy(c->vl, vl, sizeof vl);
            if (ok) {
                bestV = V;
                bestI = i;
            }
        }
        if (!any) break;
    }

    if (bestI < 0) { print_complete(); return 0; }

    {
        Cand *c = &cands[bestI];
        build_group(c->m, c->k, c->r);
        cur_cand = bestI;
        P = c->P;
        V = 2 * P * N;
        memcpy(tg, c->tg, sizeof tg);
        memcpy(vl, c->vl, sizeof vl);
        rebuild_inc();
    }
    for (int v = 0; v < V; v++) {
        if (ball(v) != V) { print_complete(); return 0; }
    }

    int E = P * d * N;
    printf("%d %d\n", V, E);
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) {
            int j = tg[i][k], g = vl[i][k];
            for (int x = 0; x < N; x++)
                printf("%d %d\n", i * N + x, (P + j) * N + T[(size_t)x * N + g]);
        }
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
    ref = REF_VERTICES.get((d, D))
    if ref is None:
        return best
    # Leave room for the C compile, the C-side verification, parsing and lib.is_valid.
    budget = 0.88 * time_limit - 1.0 - (time.monotonic() - t0)
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 10)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
