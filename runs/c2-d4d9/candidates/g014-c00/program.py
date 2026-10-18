"""Program: bi-Cayley search over metacyclic groups Z_m x| Z_k, plus PSL/SL(2,q).

Construction:
  * Group G of order N, given by a full multiplication table (N <= 3200).
  * Bi-Cayley graph: A_x is joined to B_{x*s_k} for k < d. This is d-regular, bipartite,
    and has 2N vertices.
  * Left multiplication by any h in G is an automorphism, so diameter <= D holds iff
    BFS from A_e and from B_e both reach all 2N vertices within D steps.

Scheduling (successive halving over resumable hill climbs):
  * Every candidate group owns a slot that keeps its connection set and its best cost.
  * Each round gives every alive candidate a slice of about 35% of the remaining time,
    split evenly. A candidate that reaches cost 0 is a valid graph, and bestN rises.
  * After each round the worse half (by best cost relative to 2N) is dropped, and the
    survivors resume their own climbs in the next round instead of restarting.
  * The last survivor gets all remaining time.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 48
#define MAXSLOT 96

static int d, D;
static double t_end;
static long moore_g;

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
    double frac;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta(int Nval, Cand *arr, int *cnt) {
    for (int k = 2; k <= Nval / 3 && *cnt < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            c.frac = 0.06;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

/* ------------------------------------------------------------------ slots */

typedef struct {
    Cand c;
    int fresh;            /* 1 = connection set not yet drawn */
    int dead;             /* 1 = never tried again */
    int S[MAXDEG];        /* current connection set (resume point) */
    int bestS[MAXDEG];    /* connection set with the lowest cost seen */
    long best_c;          /* lowest cost seen */
    double score;         /* best_c / (2N), used for halving */
} Slot;

static Slot slots[MAXSLOT];
static int ns = 0;

static void add_slot(const Cand *c) {
    if (ns >= MAXSLOT) return;
    Slot *s = &slots[ns++];
    memset(s, 0, sizeof *s);
    s->c = *c;
    s->fresh = 1;
    s->dead = (2L * c->N > moore_g) ? 1 : 0;
    s->best_c = (long)1 << 40;
    s->score = 1e300;
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + s];
        Ri[k][x] = (int)T[(size_t)x * N + si];
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------------ BFS cost */

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

static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

/* Resumable hill climb on slot s (its group must already be applied).
   Returns 1 if a valid connection set was found (cost 0). */
static int climb(Slot *s, double until) {
    if (s->fresh) {
        randomize_S();
        s->fresh = 0;
    } else {
        memcpy(S, s->S, sizeof(int) * (size_t)d);
        for (int k = 0; k < d; k++) set_col(k);
    }
    long cur = cost_now();
    long lbest = cur, stall = 0, it = 0;
    if (cur < s->best_c) {
        s->best_c = cur;
        memcpy(s->bestS, S, sizeof(int) * (size_t)d);
    }
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) break;
        if (stall > 4000) {
            randomize_S();
            cur = cost_now();
            lbest = cur;
            stall = 0;
            if (cur < s->best_c) {
                s->best_c = cur;
                memcpy(s->bestS, S, sizeof(int) * (size_t)d);
            }
            continue;
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < lbest) { lbest = cur; stall = 0; }
        else stall++;
        if (cur < s->best_c) {
            s->best_c = cur;
            memcpy(s->bestS, S, sizeof(int) * (size_t)d);
        }
    }
    memcpy(s->S, S, sizeof(int) * (size_t)d);
    return cur == 0;
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    moore_g = moore;
    long bestN = d;

    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;   /* smallest N that beats the record vertex count */

    static Cand all_m[16], lo[MAXCAND], hi[MAXCAND];
    int nm = 0, nl = 0, nh = 0;

    /* 1. matrix groups in the window */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (nm >= 16) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            c.frac = 0.25;
            all_m[nm++] = c;
        }
    }

    /* 2. metacyclic groups just below the record (largest first) */
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo, &nl);
    /* 3. metacyclic groups beating the record (smallest first) */
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, hi, &nh);

    for (int i = 0; i < nm; i++) add_slot(&all_m[i]);
    for (int i = 0; i < nl && i < 12; i++) add_slot(&lo[i]);
    for (int i = 0; i < nh; i++) add_slot(&hi[i]);

    int have = 0, bi = -1;
    static int alive[MAXSLOT];

    for (int round = 0; round < 200; round++) {
        int A = 0;
        for (int i = 0; i < ns; i++) {
            Slot *s = &slots[i];
            if (s->dead) continue;
            if ((long)s->c.N <= bestN) { s->dead = 1; continue; }
            alive[A++] = i;
        }
        double R = t_end - now();
        if (A == 0 || R < 0.2) break;

        double slice = (A == 1) ? R : 0.35 * R / (double)A;
        if (slice < 0.15) slice = 0.15;
        if (slice > R) slice = R;

        for (int a = 0; a < A; a++) {
            if (t_end - now() < 0.1) break;
            Slot *s = &slots[alive[a]];
            if (s->dead || (long)s->c.N <= bestN) continue;
            if (!apply_cand(&s->c) || N != s->c.N) { s->dead = 1; continue; }
            if (climb(s, now() + slice)) {
                have = 1;
                bi = alive[a];
                bestN = s->c.N;
                s->dead = 1;
            }
            s->score = (double)s->best_c / (2.0 * (double)s->c.N);
        }

        /* Successive halving: keep the better half (by relative cost). */
        int B = 0;
        for (int a = 0; a < A; a++) {
            Slot *s = &slots[alive[a]];
            if (!s->dead && (long)s->c.N > bestN) alive[B++] = alive[a];
        }
        for (int i = 1; i < B; i++) {
            int v = alive[i];
            int j = i - 1;
            while (j >= 0 && slots[alive[j]].score > slots[v].score) {
                alive[j + 1] = alive[j];
                j--;
            }
            alive[j + 1] = v;
        }
        int keep = (B + 1) / 2;
        for (int a = keep; a < B; a++) slots[alive[a]].dead = 1;
    }

    if (!have || bi < 0) { print_complete(); return 0; }
    Slot *b = &slots[bi];
    if (!apply_cand(&b->c)) { print_complete(); return 0; }
    memcpy(S, b->bestS, sizeof(int) * (size_t)d);
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
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    # Use most of the case's time for the C search; keep a margin for compile, I/O and checks.
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
