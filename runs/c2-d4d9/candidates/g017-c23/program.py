"""Program: multi-orbit bi-voltage lifts over small groups, plus cyclic, abelian and metacyclic groups.

New construction in this version:
  * t-orbit bi-lift. There are t orbits A_0..A_{t-1} and t orbits B_0..B_{t-1}, each of size N
    (the group order). Each A-orbit has d darts. Dart q = (i, k) goes to B-orbit tgt[q] with
    voltage gv[q]: A_{i,x} is joined to B_{tgt[q], x*g_q}. The base multigraph is d-regular, so
    every B vertex also gets exactly d edges. The graph has 2*t*N vertices.
  * Left multiplication by any h in G is an automorphism, so diameter <= D holds iff BFS from
    A_{i,e} and B_{j,e} (for all i, j) reaches all 2P vertices, where P = t*N.
  * This gives per-side sizes P = t*N for every t <= 6 that divides P, not only one group order per
    side. Groups are cyclic Z_N, abelian Z_m x Z_k, and metacyclic Z_m x|_r Z_k.
  * Moves: change one voltage, or swap the targets of two darts (keeps d-regularity).
  * Candidates are ordered by P from 2485 (record level) upward. Once a graph beats the best,
    only larger candidates are tried. Iterative deepening gives every candidate a slice.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXT 6
#define MAXD 8
#define MAXDART (MAXT * MAXD)
#define MAXP 4096
#define MAXV (2 * MAXP)
#define MAXCAND 40
#define STALL_LIMIT 4000

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

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ------------------------------------------------------------------ group */

static int N = 0;            /* group order */
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;
static int e_id = 0;

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
    if (!T || !INV) exit(1);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). r = 1 gives Z_m x Z_k. */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 3) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
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
    e_id = 0;
    finish_inv();
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int nt, m, k, r; } Cand;

static Cand bestC;
static int bestV = 0;
static int bestTgt[MAXDART], bestGv[MAXDART];

/* ------------------------------------------------------------------ lift state */

static int nt = 1;                 /* orbits per side */
static int P = 0, V = 0, ndart = 0;
static int tgt[MAXDART];           /* target orbit of dart q (dart q leaves A-orbit q/d) */
static int gv[MAXDART];            /* voltage of dart q */
static int Rr[MAXDART][MAXN];      /* Rr[q][x] = x * g_q */
static int Ri[MAXDART][MAXN];      /* Ri[q][y] = y * g_q^{-1} */
static int inc[MAXDART];           /* inc[j*d + r] = r-th dart with target j */

static void set_dart(int q) {
    int g = gv[q], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rr[q][x] = (int)T[(size_t)x * N + g];
        Ri[q][x] = (int)T[(size_t)x * N + gi];
    }
}

static void rebuild_inc(void) {
    int cnt[MAXT];
    memset(cnt, 0, sizeof cnt);
    for (int q = 0; q < ndart; q++) {
        int j = tgt[q];
        inc[j * d + cnt[j]++] = q;
    }
}

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int root, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[root] = tick;
    qv[tail++] = root;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < P) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int q = i * d + k;
                    int u = P + tgt[q] * N + Rr[q][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - P, j = w / N, y = w - j * N;
                for (int r = 0; r < d; r++) {
                    int q = inc[j * d + r];
                    int u = (q / d) * N + Ri[q][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices summed over the roots A_{i,e} and B_{i,e} for all orbits i. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < nt; i++) {
        c += (long)(V - ball(i * N, D));
        c += (long)(V - ball(P + i * N, D));
    }
    return c;
}

static void randomize_all(void) {
    static int tmpt[MAXDART];
    int idx = 0;
    for (int j = 0; j < nt; j++)
        for (int r = 0; r < d; r++) tmpt[idx++] = j;
    for (int i = ndart - 1; i > 0; i--) {
        int k = rndint(i + 1);
        int t = tmpt[i];
        tmpt[i] = tmpt[k];
        tmpt[k] = t;
    }
    for (int q = 0; q < ndart; q++) {
        tgt[q] = tmpt[q];
        gv[q] = rndint(N);
        set_dart(q);
    }
    rebuild_inc();
}

static int climb(double until) {
    randomize_all();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL_LIMIT) {
            randomize_all();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        if (nt > 1 && rnd01() < 0.3) {
            int q1 = rndint(ndart), q2 = rndint(ndart);
            if (tgt[q1] == tgt[q2]) { stall++; continue; }
            int a = tgt[q1], b = tgt[q2];
            tgt[q1] = b;
            tgt[q2] = a;
            rebuild_inc();
            long nc = cost_now();
            if (nc <= cur || rnd01() < 0.02) {
                cur = nc;
            } else {
                tgt[q1] = a;
                tgt[q2] = b;
                rebuild_inc();
            }
        } else {
            int q = rndint(ndart), old = gv[q];
            gv[q] = rndint(N);
            set_dart(q);
            long nc = cost_now();
            if (nc <= cur || rnd01() < 0.02) {
                cur = nc;
            } else {
                gv[q] = old;
                set_dart(q);
            }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

static int apply_cand(const Cand *c) {
    if (c->m * c->k > MAXN) return 0;
    if (!build_meta(c->m, c->k, c->r)) return 0;
    nt = c->nt;
    P = nt * N;
    if (P > MAXP) return 0;
    V = 2 * P;
    ndart = nt * d;
    return 1;
}

static void push_cand(Cand *arr, int *cnt, int tt, int m, int k, int r) {
    if (*cnt >= MAXCAND) return;
    arr[*cnt].nt = tt;
    arr[*cnt].m = m;
    arr[*cnt].k = k;
    arr[*cnt].r = r;
    (*cnt)++;
}

/* Groups of order Nv for a t-orbit lift: metacyclic (2 per k), cyclic, then abelian. */
static void add_groups(int tt, int Nv, Cand *arr, int *cnt) {
    int cap = (tt == 1) ? 6 : 3;
    int got = 0;
    for (int k = 2; k <= Nv / 3 && got < cap; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int g2 = 0;
        for (int r = 2; r < m && got < cap && g2 < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            push_cand(arr, cnt, tt, m, k, r);
            got++;
            g2++;
        }
    }
    if (got < cap) { push_cand(arr, cnt, tt, Nv, 1, 1); got++; }
    for (int k = 2; k <= Nv / 3 && got < cap; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        push_cand(arr, cnt, tt, m, k, 1);   /* abelian Z_m x Z_k */
        got++;
        break;
    }
}

/* ------------------------------------------------------------------ main */

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
    double usable = limit - 0.8;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    int Pmin = (int)(ref / 2);
    if (Pmin < 3) Pmin = 3;
    int Pmax = Pmin + Pmin / 10 + 1;
    if (Pmax > MAXP) Pmax = MAXP;

    static Cand cand[MAXCAND];
    int ncand = 0;
    for (int Pv = Pmin; Pv <= Pmax && ncand < MAXCAND; Pv++) {
        if (2L * Pv > moore) break;
        for (int tt = 1; tt <= MAXT && ncand < MAXCAND; tt++) {
            if (Pv % tt) continue;
            int Nv = Pv / tt;
            if (Nv < 3 || Nv > MAXN) continue;
            add_groups(tt, Nv, cand, &ncand);
        }
    }

    double budget0 = t_end - now();
    if (budget0 < 0.5 || ncand == 0) { print_complete(); return 0; }
    double base = budget0 / (3.0 * (double)ncand);
    if (base < 0.4) base = 0.4;

    /* Iterative deepening: each round gives every still-improving candidate a slice, doubling per round. */
    for (int round = 0; round < 10; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cand[i];
            long cV = 2L * c->nt * c->m * c->k;
            if (cV <= bestV) continue;
            if (!apply_cand(c)) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                bestV = V;
                bestC = *c;
                memcpy(bestTgt, tgt, sizeof(int) * (size_t)ndart);
                memcpy(bestGv, gv, sizeof(int) * (size_t)ndart);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (bestV == 0) { print_complete(); return 0; }
    if (!apply_cand(&bestC)) { print_complete(); return 0; }
    memcpy(tgt, bestTgt, sizeof(int) * (size_t)ndart);
    memcpy(gv, bestGv, sizeof(int) * (size_t)ndart);
    for (int q = 0; q < ndart; q++) set_dart(q);
    rebuild_inc();
    if (cost_now() != 0) { print_complete(); return 0; }

    static int EU[MAXP * MAXD], EV[MAXP * MAXD];
    int ne = 0;
    for (int v = 0; v < P; v++) {
        int i = v / N, x = v - i * N;
        int nb[MAXD];
        for (int k = 0; k < d; k++) {
            int q = i * d + k;
            nb[k] = P + tgt[q] * N + Rr[q][x];
        }
        for (int k = 0; k < d; k++) {
            int dup = 0;
            for (int k2 = 0; k2 < k; k2++)
                if (nb[k2] == nb[k]) { dup = 1; break; }
            if (!dup) {
                EU[ne] = v;
                EV[ne] = nb[k];
                ne++;
            }
        }
    }
    printf("%d %d\n", V, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", EU[e], EV[e]);
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
    if ref is None or best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
