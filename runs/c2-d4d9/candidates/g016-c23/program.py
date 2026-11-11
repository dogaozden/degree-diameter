"""Program: multi-orbit bi-Cayley lifts with simulated annealing over darts.

New construction (not in the parent):
  * A "k-orbit lift" of a group G of order N. Take k orbits A_0..A_{k-1} and k orbits
    B_0..B_{k-1}, each a copy of G, so there are 2kN vertices. A d-regular bipartite
    base multigraph on k+k vertices is given by E = d*k darts (a, b, g): the lift joins
    (A_a, x) to (B_b, x*g) for every x in G. Degrees are exactly d when the darts give d
    darts per a and d darts per b, and the graph is simple when no two darts share (a, b, g).
  * Left multiplication is an automorphism, so diameter <= D is checked by BFS from
    (A_a, e) and (B_b, e) only: 2k BFS runs.
  * Moves: change one voltage, or swap the B-end (or A-end) of two darts. Both keep the
    degree counts. Duplicate darts are penalised.

Scheduling:
  * Phase 1: single-orbit candidates near the record (the parent's window), stopping at the
    first valid graph. This secures the record vertex count.
  * Phase 2: k = 2, 3, 4 orbits per side with group order just large enough to beat the
    record vertex count, smallest vertex count first. Iterative deepening gives each
    candidate a doubling slice.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start.
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

#define MAXN 3200
#define MAXK 4
#define MAXDEG 8
#define MAXE (MAXDEG * MAXK)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 2048
#define P2MAX 24
#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0
#define DUPW 1000000L

static int d, D;
static double t_end;
static long moore;

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

/* ------------------------------------------------------------------ groups */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_kz, element (a,b) coded as a*kz+b. */
static int build_meta(int m, int kz, int r) {
    int n = m * kz;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < kz; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / kz, b = x % kz;
        for (int y = 0; y < N; y++) {
            int c = y / kz, dd = y % kz;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % kz;
            T[(size_t)x * N + y] = (uint16_t)(aa * kz + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;     /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, kz, r, N;
    int ko;       /* orbits per side */
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->kz, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta(int Nval, int ko, Cand *arr, int *cnt, int cap) {
    for (int kz = 2; kz <= Nval / 3 && *cnt < cap; kz++) {
        if (Nval % kz) continue;
        int m = Nval / kz;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < cap; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, kz, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.kz = kz;
            c.r = r;
            c.N = Nval;
            c.ko = ko;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

static void add_matrix(int ko, long lo, long hi, Cand *arr, int *cnt, int cap) {
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lo || o > hi || o > MAXN || *cnt >= cap) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            c.ko = ko;
            arr[(*cnt)++] = c;
        }
    }
}

/* ------------------------------------------------------------------ dart lift state */

/* Dart s joins (A_{ea[s]}, x) to (B_{eb[s]}, x*g_s) for all x in G, g_s = eg[s]. */
static int KO = 1, E = 0;
static int ea[MAXE], eb[MAXE], eg[MAXE];
static int Rm[MAXE][MAXN];   /* Rm[s][x] = x * g_s */
static int Ri[MAXE][MAXN];   /* Ri[s][y] = y * g_s^{-1} */
static int dA[MAXK][MAXDEG], dB[MAXK][MAXDEG];

static void rebuild_lists(void) {
    for (int a = 0; a < KO; a++) {
        int n = 0, m = 0;
        for (int s = 0; s < E; s++) {
            if (ea[s] == a && n < MAXDEG) dA[a][n++] = s;
            if (eb[s] == a && m < MAXDEG) dB[a][m++] = s;
        }
    }
}

static void set_dart(int s) {
    int g = eg[s], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rm[s][x] = (int)T[(size_t)x * N + g];
        Ri[s][x] = (int)T[(size_t)x * N + gi];
    }
}

static void set_all(void) {
    for (int s = 0; s < E; s++) set_dart(s);
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of vertices reached from src within dmax steps. */
static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int BN = KO * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < BN) {
                int a = v / N, x = v - a * N;
                for (int i = 0; i < d; i++) {
                    int s = dA[a][i];
                    int u = BN + eb[s] * N + Rm[s][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - BN, b = w / N, y = w - b * N;
                for (int i = 0; i < d; i++) {
                    int s = dB[b][i];
                    int u = ea[s] * N + Ri[s][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the 2k orbit representatives, plus a penalty per duplicate dart. */
static long cost_now(void) {
    long dup = 0;
    for (int s = 0; s < E; s++)
        for (int t = s + 1; t < E; t++)
            if (ea[s] == ea[t] && eb[s] == eb[t] && eg[s] == eg[t]) dup++;
    int BN = KO * N;
    long V = 2L * BN;
    long un = 0;
    for (int a = 0; a < KO; a++) un += V - ball(a * N + e_id, D);
    for (int b = 0; b < KO; b++) un += V - ball(BN + b * N + e_id, D);
    return un + dup * DUPW;
}

/* ------------------------------------------------------------------ moves */

typedef struct { int kind, s, t, old; } Undo;

static void do_move(Undo *u) {
    int r = rndint(10);
    u->kind = r < 6 ? 0 : (r < 8 ? 1 : 2);
    u->s = rndint(E);
    if (u->kind == 0) {
        u->old = eg[u->s];
        eg[u->s] = rndint(N);
        set_dart(u->s);
        return;
    }
    u->t = rndint(E);
    if (u->t == u->s) { u->kind = -1; return; }
    if (u->kind == 1) {
        int tmp = eb[u->s]; eb[u->s] = eb[u->t]; eb[u->t] = tmp;
    } else {
        int tmp = ea[u->s]; ea[u->s] = ea[u->t]; ea[u->t] = tmp;
    }
    rebuild_lists();
}

static void undo_move(const Undo *u) {
    if (u->kind == 0) {
        eg[u->s] = u->old;
        set_dart(u->s);
    } else if (u->kind == 1) {
        int tmp = eb[u->s]; eb[u->s] = eb[u->t]; eb[u->t] = tmp;
        rebuild_lists();
    } else if (u->kind == 2) {
        int tmp = ea[u->s]; ea[u->s] = ea[u->t]; ea[u->t] = tmp;
        rebuild_lists();
    }
}

static void randomize_state(void) {
    E = d * KO;
    static int bl[MAXE];
    for (int s = 0; s < E; s++) {
        ea[s] = s / d;
        bl[s] = s / d;
    }
    for (int i = E - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = bl[i]; bl[i] = bl[j]; bl[j] = tmp;
    }
    for (int s = 0; s < E; s++) {
        eb[s] = bl[s];
        eg[s] = rndint(N);
    }
    rebuild_lists();
    set_all();
}

static int bea[MAXE], beb[MAXE], beg[MAXE];

static void save_best(void) {
    memcpy(bea, ea, sizeof(int) * (size_t)E);
    memcpy(beb, eb, sizeof(int) * (size_t)E);
    memcpy(beg, eg, sizeof(int) * (size_t)E);
}

static void restore_best(void) {
    memcpy(ea, bea, sizeof(int) * (size_t)E);
    memcpy(eb, beb, sizeof(int) * (size_t)E);
    memcpy(eg, beg, sizeof(int) * (size_t)E);
    rebuild_lists();
    set_all();
}

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves the valid state in place. */
static int climb(double until) {
    if (N < 3) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_state();
    long cur = cost_now();
    long bestc = cur;
    save_best();
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        Undo u;
        do_move(&u);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                save_best();
            }
        } else {
            undo_move(&u);
        }
    }
    if (bestc != 0) return 0;
    restore_best();
    return 1;
}

/* ------------------------------------------------------------------ search */

static long bestV = 0;
static Cand bestC;
static int have = 0;
static int fea[MAXE], feb[MAXE], feg[MAXE];

/* Iterative deepening over candidates. Only candidates with more vertices than the best are tried. */
static int search_phase(Cand *arr, int n, double phase_end, double base, int stop_first) {
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < n; i++) {
            double lim = phase_end < t_end ? phase_end : t_end;
            if (now() >= lim) return have;
            Cand *c = &arr[i];
            long V = 2L * c->ko * c->N;
            if (V <= bestV || V > moore) continue;
            if (!apply_cand(c)) continue;
            KO = c->ko;
            E = d * KO;
            double slice = base * (double)(1 << round);
            double rem = lim - now();
            if (slice > rem) slice = rem;
            if (slice < 0.05) return have;
            if (climb(now() + slice)) {
                have = 1;
                bestV = V;
                bestC = *c;
                memcpy(fea, ea, sizeof(int) * (size_t)E);
                memcpy(feb, eb, sizeof(int) * (size_t)E);
                memcpy(feg, eg, sizeof(int) * (size_t)E);
                if (stop_first) return 1;
            }
        }
    }
    return have;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_state(void) {
    int BN = KO * N;
    long M = (long)E * N;
    printf("%d %ld\n", 2 * BN, M);
    for (int s = 0; s < E; s++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", ea[s] * N + x, BN + eb[s] * N + Rm[s][x]);
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }
    moore = moore_bound();

    static Cand c1[MAXCAND], p2[MAXCAND];
    int n1 = 0, n2 = 0;

    /* Phase 1: single-orbit candidates near the record (parent's window). */
    long recHalf = ref / 2;
    long lowN = (long)(0.87 * (double)recHalf);
    long hiN = (long)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2 * hiN > moore) hiN = moore / 2;
    if (lowN < 3) lowN = 3;
    add_matrix(1, lowN, hiN, c1, &n1, MAXCAND);
    for (long Nv = recHalf; Nv >= lowN; Nv--) add_meta((int)Nv, 1, c1, &n1, MAXCAND);
    for (long Nv = recHalf + 1; Nv <= hiN; Nv++) add_meta((int)Nv, 1, c1, &n1, MAXCAND);

    double base1 = 0.04 * usable;
    if (base1 < 0.3) base1 = 0.3;
    search_phase(c1, n1, t0 + 0.35 * usable, base1, 1);

    /* Phase 2: multi-orbit lifts (k orbits per side) with more than the record vertices. */
    for (int ko = 2; ko <= MAXK; ko++) {
        long lo = ref / (2L * ko) + 1;
        long hi = lo * 3 / 2;
        if (hi > MAXN) hi = MAXN;
        if (2L * ko * hi > moore) hi = moore / (2L * ko);
        if (hi < lo) continue;
        add_matrix(ko, lo, hi, p2, &n2, MAXCAND);
        for (long Nv = lo; Nv <= hi; Nv++) add_meta((int)Nv, ko, p2, &n2, MAXCAND);
    }
    /* Smallest vertex count first. */
    for (int i = 1; i < n2; i++) {
        Cand x = p2[i];
        long kx = 2L * x.ko * x.N;
        int j = i - 1;
        while (j >= 0 && 2L * p2[j].ko * p2[j].N > kx) {
            p2[j + 1] = p2[j];
            j--;
        }
        p2[j + 1] = x;
    }
    if (n2 > P2MAX) n2 = P2MAX;
    if (n2 > 0) {
        double budget2 = t_end - now();
        double base2 = budget2 / (n2 * 4.0);
        if (base2 < 0.25) base2 = 0.25;
        search_phase(p2, n2, t_end, base2, 0);
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&bestC)) { print_complete(); return 0; }
    KO = bestC.ko;
    E = d * KO;
    memcpy(ea, fea, sizeof(int) * (size_t)E);
    memcpy(eb, feb, sizeof(int) * (size_t)E);
    memcpy(eg, feg, sizeof(int) * (size_t)E);
    rebuild_lists();
    set_all();
    if (cost_now() != 0) { print_complete(); return 0; }
    print_state();
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
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
