"""Program: two-orbit ("block") bi-Cayley search, plus single bi-Cayley and PSL/SL(2,q) fallbacks.

New idea (block bi-Cayley graphs):
  * Vertex set A_0, A_1, B_0, B_1, each a copy of a group G of order N, so 4N vertices.
  * Each connection (i, j, s) joins (i, x) to (j, x*s). The count matrix is
    [[a, d-a], [d-a, a]] with 1 <= a <= d-1, so every vertex has degree exactly d.
  * Left multiplication by G is an automorphism, so the graph has 4 orbits and only
    4 BFS sources are needed: (i, e) for each A-block and (j, e) for each B-block.
  * This gives 4N vertices with N >= record/4 + 1, a family that the single
    bi-Cayley search (2N vertices) does not cover.

Scheduling: candidates are tried in phases (matrix and metacyclic fallbacks near the
reference, then block candidates in ascending order, then single bi-Cayley candidates
above the reference). Each candidate only runs if it could beat the current best.
Iterative deepening doubles each round's slice.

Safety: Python checks the C output with lib.is_valid and keeps the best valid graph,
falling back to the known start or K_{d,d}.
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
#define MAXV (4 * MAXN)
#define MAXDEG 8
#define MAXM (2 * MAXDEG)
#define MAXCAND 160

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

/* ------------------------------------------------------------------ group */

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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
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
    return N;
}

/* PSL(2,q) or SL(2,q), q prime. */
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
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    int nbk;    /* blocks per side: 1 = single bi-Cayley, 2 = two-orbit block graph */
} Cand;

static const int QS[6] = {5, 7, 11, 13, 17, 19};

static long mat_order(int qi, int psl) {
    long q = QS[qi];
    long o = q * (q * q - 1);
    if (psl) o /= 2;
    return o;
}

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void push_matrix(Cand *arr, int *cnt, int qi, int psl, int nbk) {
    if (*cnt >= MAXCAND) return;
    long o = mat_order(qi, psl);
    if (o > MAXN) return;
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 1;
    c.q = QS[qi];
    c.psl = psl;
    c.N = (int)o;
    c.nbk = nbk;
    arr[(*cnt)++] = c;
}

/* Adds up to one metacyclic candidate per divisor k of Nval (nontrivial r preferred). */
static void add_meta(int Nval, int nbk, Cand *arr, int *cnt, int per) {
    int got = 0;
    for (int k = 1; k <= Nval && got < per && *cnt < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int chosen = -1;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            chosen = r;
            break;
        }
        if (chosen < 0) chosen = 1;   /* abelian / cyclic representative */
        Cand c;
        memset(&c, 0, sizeof c);
        c.type = 0;
        c.m = m;
        c.k = k;
        c.r = chosen;
        c.N = Nval;
        c.nbk = nbk;
        arr[(*cnt)++] = c;
        got++;
    }
}

/* ------------------------------------------------------------------ connection state */

static int nbk = 1;          /* blocks per side */
static int M = 0;            /* number of connections = nbk*d */
static int cnt_a = 1;        /* for nbk==2: count matrix [[a, d-a],[d-a, a]] */
static int Ib[MAXM], Jb[MAXM], Sx[MAXM];
static int Rr[MAXM][MAXN];   /* Rr[t][x] = x * s_t */
static int Ri[MAXM][MAXN];   /* Ri[t][y] = y * s_t^{-1} */

static void set_pattern(void) {
    if (nbk == 1) {
        for (int t = 0; t < d; t++) { Ib[t] = 0; Jb[t] = 0; }
        M = d;
        return;
    }
    int C[2][2] = {{cnt_a, d - cnt_a}, {d - cnt_a, cnt_a}};
    int t = 0;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++)
            for (int c = 0; c < C[i][j]; c++) {
                Ib[t] = i;
                Jb[t] = j;
                t++;
            }
    M = t;   /* = 2d */
}

static void set_col(int t) {
    int s = Sx[t], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[t][x] = (int)T[(size_t)x * N + s];
        Ri[t][x] = (int)T[(size_t)x * N + si];
    }
}

/* True if element x is already used by another connection in the same block pair. */
static int conflict(int t, int x) {
    for (int u = 0; u < M; u++)
        if (u != t && Ib[u] == Ib[t] && Jb[u] == Jb[t] && Sx[u] == x) return 1;
    return 0;
}

static void randomize_all(void) {
    if (nbk == 2) cnt_a = 1 + rndint(d - 1);
    set_pattern();
    for (int t = 0; t < M; t++) Sx[t] = -1;
    for (int t = 0; t < M; t++) {
        int x;
        do x = rndint(N); while (conflict(t, x));
        Sx[t] = x;
    }
    for (int t = 0; t < M; t++) set_col(t);
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Vertices: A-block i element x has id i*N+x; B-block j element y has id nbk*N + j*N + y. */
static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int off = nbk * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < off) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < M; t++) {
                    if (Ib[t] != i) continue;
                    int u = off + Jb[t] * N + Rr[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - off;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < M; t++) {
                    if (Jb[t] != j) continue;
                    int u = Ib[t] * N + Ri[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over block sources (i,e) and (j,e) of the number of vertices not reached within D. */
static long cost_now(void) {
    long V = 2L * nbk * N;
    long c = 0;
    for (int i = 0; i < nbk; i++) {
        c += V - ball(i * N + e_id, D);
        c += V - ball(nbk * N + i * N + e_id, D);
    }
    return c;
}

static int climb(double until) {
    randomize_all();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 4000) {
            randomize_all();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int t = rndint(M);
        int x = rndint(N);
        if (conflict(t, x)) { stall++; continue; }
        int old = Sx[t];
        Sx[t] = x;
        set_col(t);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            Sx[t] = old;
            set_col(t);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    int off = nbk * N;
    long E = (long)nbk * N * d;
    printf("%d %ld\n", 2 * off, E);
    for (int i = 0; i < nbk; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < M; t++)
                if (Ib[t] == i)
                    printf("%d %d\n", i * N + x, off + Jb[t] * N + Rr[t][x]);
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

    long moore = moore_bound();
    int canBlock = d >= 2;

    static Cand all[MAXCAND];
    int na = 0;
    double lo_bound = 0.8 * (double)ref;
    long Nlo1 = ref / 2 + 1;   /* smallest single-family N with 2N > ref */
    long Nlo2 = ref / 4 + 1;   /* smallest block-family N with 4N > ref */

    /* A. matrix singles just below the reference (safety net) */
    for (int qi = 0; qi < 6; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long o = mat_order(qi, psl);
            if (2 * o > ref || 2.0 * (double)o < lo_bound) continue;
            push_matrix(all, &na, qi, psl, 1);
        }

    /* B. metacyclic singles just below the reference, descending */
    {
        int startB = na;
        long top = Nlo1 - 1;
        if (top > MAXN) top = MAXN;
        for (long Nv = top; Nv >= 3 && 2.0 * (double)Nv >= lo_bound && na - startB < 12; Nv--)
            add_meta((int)Nv, 1, all, &na, 2);
    }

    /* C. two-orbit block graphs (new family), ascending N, so 4N > ref from the start */
    {
        int startC = na;
        if (canBlock) {
            for (long Nv = Nlo2; Nv <= MAXN && 4 * Nv <= moore && Nv < Nlo2 + 200 && na - startC < 48; Nv++) {
                if (Nv < d + 1) continue;
                add_meta((int)Nv, 2, all, &na, 2);
                for (int qi = 0; qi < 6; qi++)
                    for (int psl = 0; psl < 2; psl++)
                        if (mat_order(qi, psl) == Nv) push_matrix(all, &na, qi, psl, 2);
            }
        }
    }

    /* D. single bi-Cayley graphs above the reference, ascending */
    {
        int startD = na;
        for (long Nv = Nlo1; Nv <= MAXN && 2 * Nv <= moore && Nv < Nlo1 + 200 && na - startD < 48; Nv++) {
            if (Nv < d + 1) continue;
            add_meta((int)Nv, 1, all, &na, 2);
            for (int qi = 0; qi < 6; qi++)
                for (int psl = 0; psl < 2; psl++)
                    if (mat_order(qi, psl) == Nv) push_matrix(all, &na, qi, psl, 1);
        }
    }

    long bestV = 0;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    int bestA = 1, bestNbk = 1;
    static int bestSx[MAXM];

    double budget0 = t_end - now();
    double base = budget0 * 0.01;
    if (base < 0.15) base = 0.15;

    /* Iterative deepening: each round gives every still-improving candidate a slice,
       and the slice doubles per round. */
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < na; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &all[i];
            long V = 2L * c->nbk * c->N;
            if (V <= bestV || V > moore) continue;
            if (apply_cand(c) != c->N) continue;
            nbk = c->nbk;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV = V;
                best = *c;
                bestA = cnt_a;
                bestNbk = nbk;
                memcpy(bestSx, Sx, sizeof(int) * MAXM);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (apply_cand(&best) != best.N) { print_complete(); return 0; }
    nbk = bestNbk;
    cnt_a = bestA;
    set_pattern();
    for (int t = 0; t < M; t++) Sx[t] = bestSx[t];
    for (int t = 0; t < M; t++) set_col(t);
    if (cost_now() != 0) { print_complete(); return 0; }
    print_graph();
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970, (3, 3): 14}


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
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
