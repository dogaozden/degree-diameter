"""Program: normalized tabu search for bi-Cayley graphs over metacyclic and PSL/SL(2,q) groups.

New in this version:
  * Normalization: right-multiplying S by g gives an isomorphic bi-Cayley graph, so we fix
    S[0] = e and search only the other d-1 connection elements.
  * Tabu search: each step samples SAMPLE random single-slot moves and takes the best
    non-tabu one (aspiration allows tabu moves that beat the run's best cost). A full
    exhaustive neighbourhood scan runs when the cost is at most 2.
  * Resumable slices: each candidate keeps its connection set between time slices.
  * Sliding-window scheduler: a window of WINDOW candidates is served round-robin with
    growing quanta. The N = ref/2 candidates (exact record match) get double quanta. When a
    candidate succeeds, every candidate that cannot beat the new best is dropped, and the
    queue refills the window.
  * Transposed multiplication table, so connection-column rebuilds are contiguous.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 160
#define WINDOW 8
#define SAMPLE 16
#define RESTART_IT 800
#define QUANT 0.35

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
static uint16_t *T = NULL;    /* T[x*N+y] = x*y */
static uint16_t *TR = NULL;   /* TR[y*N+x] = x*y (transpose, contiguous columns) */
static int *INV = NULL;
static int cap_T = 0;

static void alloc_group(int n) {
    if (n * n > cap_T) {
        free(T);
        free(TR);
        T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
        TR = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
        cap_T = n * n;
    }
    free(INV);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_group(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            TR[(size_t)y * N + x] = T[(size_t)x * N + y];
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
    finish_group();
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
    finish_group();
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;            /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    int have_S, dead, prio;
    int Ssave[MAXDEG];
} Cand;

static Cand cand[MAXCAND];
static int ncand = 0;

static int apply_cand(const Cand *c) {
    int n;
    if (c->type == 0) n = build_meta(c->m, c->k, c->r);
    else n = build_matrix(c->q, c->psl);
    if (n <= d + 2 || n != c->N) return 0;
    return 1;
}

static void add_meta_cands(int Nv, int prio) {
    for (int k = 2; k <= Nv / 3 && ncand < MAXCAND; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 3 && ncand < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            c.prio = prio;
            cand[ncand++] = c;
            got++;
        }
    }
}

static void add_matrix_cands(int lowN, int hiN) {
    static const int qs[] = {5, 7, 11, 13, 17, 19, 23};
    for (unsigned i = 0; i < sizeof qs / sizeof qs[0]; i++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[i];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN || ncand >= MAXCAND) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            cand[ncand++] = c;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];          /* S[0] is always the identity */
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)TR[(size_t)s * N + x];
        Ri[k][x] = (int)TR[(size_t)si * N + x];
    }
}

static int in_S(int x) {
    for (int j = 0; j < d; j++)
        if (S[j] == x) return 1;
    return 0;
}

static int in_S_upto(int x, int m) {
    for (int j = 0; j < m; j++)
        if (S[j] == x) return 1;
    return 0;
}

static void randomize_S(void) {
    S[0] = e_id;
    for (int k = 1; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S_upto(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

static void apply_move(int k, int x) {
    S[k] = x;
    set_col(k);
}

/* ------------------------------------------------------------------ cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of vertices not within D of A_e plus those not within D of B_e. Zero iff valid. */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

/* ------------------------------------------------------------------ search */

static long tabu_until[MAXDEG][MAXN];
static long g_iter = 0;

static long eval_move(int k, int x) {
    int old = S[k];
    apply_move(k, x);
    long c = cost_now();
    apply_move(k, old);
    return c;
}

/* Exhaustive scan of all single-slot moves; applies the best strict improvement. */
static long full_scan(long cur) {
    long bc = cur;
    int bk = -1, bx = -1;
    for (int k = 1; k < d; k++) {
        for (int x = 0; x < N; x++) {
            if (in_S(x)) continue;
            long c = eval_move(k, x);
            if (c < bc) { bc = c; bk = k; bx = x; }
        }
    }
    if (bk >= 0) apply_move(bk, bx);
    return bc;
}

/* Tabu search from the current S. Returns 1 with S valid, or 0 when time runs out. */
static int tabu_search(double until) {
    memset(tabu_until, 0, sizeof tabu_until);
    long cur = cost_now();
    long best_c = cur;
    long since = 0, full_gap = 0;
    while (cur > 0) {
        if (now() > until) return 0;
        g_iter++;
        if (since > RESTART_IT) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
            since = 0;
            continue;
        }
        if (cur <= 2 && full_gap > 400) {
            full_gap = 0;
            cur = full_scan(cur);
            if (cur < best_c) { best_c = cur; since = 0; }
            else since++;
            continue;
        }
        long bc = LONG_MAX;
        int bk = -1, bx = -1, nb = 0;
        for (int t = 0; t < SAMPLE; t++) {
            int k = 1 + rndint(d - 1);
            int x;
            do x = rndint(N); while (in_S(x));
            long c = eval_move(k, x);
            if (tabu_until[k][x] > g_iter && c >= best_c) continue;
            if (c < bc) { bc = c; bk = k; bx = x; nb = 1; }
            else if (c == bc) { nb++; if (rndint(nb) == 0) { bk = k; bx = x; } }
        }
        full_gap++;
        if (bk < 0) { since++; continue; }
        int old = S[bk];
        apply_move(bk, bx);
        tabu_until[bk][old] = g_iter + 3 + rndint(7);
        cur = bc;
        if (cur < best_c) { best_c = cur; since = 0; }
        else since++;
    }
    return 1;
}

/* Run one slice of a candidate, resuming its saved connection set. */
static int run_slice(Cand *c, double until) {
    if (!apply_cand(c)) { c->dead = 1; return 0; }
    if (c->have_S) {
        memcpy(S, c->Ssave, sizeof(int) * (size_t)d);
        for (int k = 0; k < d; k++) set_col(k);
    } else {
        randomize_S();
    }
    if (tabu_search(until) && cost_now() == 0) return 1;
    memcpy(c->Ssave, S, sizeof(int) * (size_t)d);
    c->have_S = 1;
    return 0;
}

/* ------------------------------------------------------------------ output */

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
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    int bestN = d;

    long recHalf = ref / 2;
    long lowL = (long)(0.87 * (double)recHalf);
    long hiL = (long)(1.13 * (double)recHalf);
    long capN = (moore / 2 < MAXN) ? moore / 2 : MAXN;
    if (hiL > capN) hiL = capN;
    if (lowL < d + 3) lowL = d + 3;
    int lowN = (int)lowL, hiN = (int)hiL;

    /* Queue order: exact record-matching orders first (prio), then orders beating the
       record in ascending order, then fallbacks below the record, then matrix groups. */
    if (recHalf >= lowN && recHalf <= hiN) add_meta_cands((int)recHalf, 1);
    for (int Nv = (int)recHalf + 1; Nv <= hiN; Nv++) add_meta_cands(Nv, 0);
    for (int Nv = (int)recHalf - 1; Nv >= lowN; Nv--) add_meta_cands(Nv, 0);
    add_matrix_cands(lowN, hiN);

    static int active[WINDOW];
    static int bS[MAXDEG];
    int nact = 0, qnext = 0;
    int have = 0, best_idx = -1;
    long cycle = 0;

    while (t_end - now() > 0.3) {
        /* drop candidates that cannot beat the current best, or are dead */
        int w = 0;
        for (int a = 0; a < nact; a++) {
            Cand *c = &cand[active[a]];
            if (!c->dead && c->N > bestN) active[w++] = active[a];
        }
        nact = w;
        /* refill the window from the queue */
        while (nact < WINDOW && qnext < ncand) {
            Cand *c = &cand[qnext];
            if (!c->dead && c->N > bestN && 2L * c->N <= moore) active[nact++] = qnext;
            qnext++;
        }
        if (nact == 0) break;

        double quant = QUANT * (1.0 + 0.2 * (double)cycle);
        if (quant > 5.0) quant = 5.0;

        for (int a = 0; a < nact; a++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &cand[active[a]];
            if (c->dead || c->N <= bestN) continue;
            double sl = (c->prio ? 2.0 : 1.0) * quant;
            if (sl > rem) sl = rem;
            if (run_slice(c, now() + sl)) {
                bestN = c->N;
                best_idx = active[a];
                memcpy(bS, S, sizeof(int) * (size_t)d);
                have = 1;
            }
        }
        cycle++;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&cand[best_idx])) { print_complete(); return 0; }
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
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
        start = lib.haar_graph(d, range(d))            # K_{d,d}: valid for D >= 2
    best = start
    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best                                    # Moore graph: nothing to search
    # Leave margin for the one-off C compile, output parsing and lib.is_valid.
    budget = 0.88 * time_limit - 3.5 - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    ref = REF_VERTICES.get((d, D), max(best[0], int(0.25 * moore)))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                         timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
