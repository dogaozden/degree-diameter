"""Program: multi-orbit voltage lifts over small groups, with the parent's bi-Cayley search as a baseline.

Phase A (baseline): bi-Cayley graphs over metacyclic groups just below the record (as the parent did).
Phase B (bold): voltage lifts of a random d-regular bipartite base multigraph with t A-orbits and
  t B-orbits (t = 2, 3, 4), so the order is 2tN. Also t = 1 just above the record, and SL/PSL(2,q).
  The lift is a graph on 2tN vertices. Left multiplication by G is an automorphism, so the diameter
  holds iff BFS from the identity copy of each of the 2t orbits reaches everything within D.
Phase C: if nothing has been found, retry the baseline with the remaining time.

Safety: C prints K_{d,d} if nothing is found and verifies its cost before printing. Python checks
the output with lib.is_valid and keeps the larger valid graph, falling back to the known start or K_{d,d}.
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
#define MAXT 4
#define MAXDEG 8
#define MAXK (MAXT * MAXDEG)
#define MAXV (2 * MAXT * MAXN)
#define MAXCAND 1200
#define STALL 4000

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
    if (n > MAXN || n < 2 || m < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + (int)((long)pw[b] * c % m)) % m;
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
    int type;     /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, t;
} Cand;

static int t_orb = 1;   /* number of A-orbits (= number of B-orbits) */

static int apply_cand(const Cand *c) {
    int ok;
    if (c->type == 0) ok = build_meta(c->m, c->k, c->r);
    else ok = build_matrix(c->q, c->psl);
    if (!ok || N != c->N) return 0;
    t_orb = c->t;
    return 1;
}

static void push_meta(Cand *arr, int *cnt, long Nv, int t) {
    for (long k = 1; k <= Nv / 2 && *cnt < MAXCAND; k++) {
        if (Nv % k) continue;
        long m = Nv / k;
        if (m < 2) continue;
        long r_found = -1;
        for (long r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            r_found = r;
            break;
        }
        if (r_found < 0) r_found = 1;
        Cand c;
        memset(&c, 0, sizeof c);
        c.type = 0;
        c.m = (int)m;
        c.k = (int)k;
        c.r = (int)r_found;
        c.N = (int)Nv;
        c.t = t;
        arr[(*cnt)++] = c;
    }
}

static void push_matrix(Cand *arr, int *cnt, int q, int psl, int t) {
    long o = (long)q * ((long)q * q - 1);
    if (psl) o /= 2;
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 1;
    c.q = q;
    c.psl = psl;
    c.N = (int)o;
    c.t = t;
    arr[(*cnt)++] = c;
}

static int cmpV(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    long vx = 2L * x->t * x->N, vy = 2L * y->t * y->N;
    return (vx > vy) - (vx < vy);
}

static Cand lo_list[MAXCAND];
static int n_lo = 0;
static Cand hi_list[MAXCAND];
static int n_hi = 0;

static void build_lists(long ref, long mo) {
    long rh = ref / 2;
    long lowN = (long)(0.87 * (double)rh);
    if (lowN < 3) lowN = 3;
    n_lo = 0;
    for (long Nv = rh; Nv >= lowN && n_lo < MAXCAND; Nv--) {
        if (2 * Nv > mo || Nv > MAXN) continue;
        push_meta(lo_list, &n_lo, Nv, 1);
    }
    n_hi = 0;
    for (int t = 2; t <= MAXT; t++) {
        long Nmin = ref / (2L * t) + 1;
        for (long Nv = Nmin; Nv <= Nmin + 10 && n_hi < MAXCAND; Nv++) {
            if (2L * t * Nv > mo || Nv > MAXN) continue;
            push_meta(hi_list, &n_hi, Nv, t);
        }
    }
    static const int qs[] = {5, 7, 11, 13};
    for (int t = 2; t <= MAXT; t++) {
        for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
            for (int psl = 0; psl < 2; psl++) {
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                long V = 2L * t * o;
                if (V <= ref || V > mo || V > 2 * ref || o > MAXN) continue;
                if (n_hi >= MAXCAND) continue;
                push_matrix(hi_list, &n_hi, (int)q, psl, t);
            }
        }
    }
    for (long Nv = rh + 1; Nv <= rh + 8 && n_hi < MAXCAND; Nv++) {
        if (2 * Nv > mo || Nv > MAXN) continue;
        push_meta(hi_list, &n_hi, Nv, 1);
    }
    qsort(hi_list, (size_t)n_hi, sizeof(Cand), cmpV);
}

/* ------------------------------------------------------------------ lift state */

static int K = 0;                  /* darts = t_orb * d */
static int dA[MAXK], dB[MAXK], GV[MAXK];
static int adjA[MAXT][MAXDEG];     /* adjA[i][j] = dart index at A_i */
static int adjB[MAXT][MAXDEG];     /* adjB[b][j] = dart index at B_b */
static int Rr[MAXK][MAXN];         /* Rr[k][x] = x * g_k */
static int Ri[MAXK][MAXN];         /* Ri[k][y] = y * g_k^{-1} */

static void set_col(int k) {
    int g = GV[k], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + g];
        Ri[k][x] = (int)T[(size_t)x * N + gi];
    }
}

static void finish_structure(void) {
    int cntA[MAXT], cntB[MAXT];
    for (int i = 0; i < MAXT; i++) { cntA[i] = 0; cntB[i] = 0; }
    for (int k = 0; k < K; k++) {
        adjA[dA[k]][cntA[dA[k]]++] = k;
        adjB[dB[k]][cntB[dB[k]]++] = k;
        set_col(k);
    }
}

/* Is the base multigraph (2*t_orb vertices, K darts) connected? */
static int base_connected(void) {
    int vis[2 * MAXT];
    int stack[2 * MAXT];
    int sp = 0, cnt = 0;
    for (int i = 0; i < 2 * MAXT; i++) vis[i] = 0;
    vis[0] = 1;
    stack[sp++] = 0;
    while (sp > 0) {
        int v = stack[--sp];
        cnt++;
        for (int k = 0; k < K; k++) {
            int a = dA[k], b = t_orb + dB[k];
            int nb = -1;
            if (v == a) nb = b;
            else if (v == b) nb = a;
            if (nb >= 0 && !vis[nb]) { vis[nb] = 1; stack[sp++] = nb; }
        }
    }
    return cnt == 2 * t_orb;
}

static void randomize_lift(void) {
    K = t_orb * d;
    int perm[MAXT];
    for (int tries = 0; tries < 200; tries++) {
        for (int j = 0; j < d; j++) {
            for (int i = 0; i < t_orb; i++) perm[i] = i;
            for (int i = t_orb - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = perm[i]; perm[i] = perm[r]; perm[r] = tmp;
            }
            for (int i = 0; i < t_orb; i++) {
                int k = j * t_orb + i;
                dA[k] = i;
                dB[k] = perm[i];
            }
        }
        if (t_orb == 1 || base_connected()) break;
    }
    for (int k = 0; k < K; k++) GV[k] = rndint(N);
    finish_structure();
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of vertices within distance D of src. */
static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int nA = t_orb * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < nA) {
                int i = v / N, x = v - i * N;
                for (int j = 0; j < d; j++) {
                    int k = adjA[i][j];
                    int u = (t_orb + dB[k]) * N + Rr[k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - nA;
                int b = w / N, y = w - b * N;
                for (int j = 0; j < d; j++) {
                    int k = adjB[b][j];
                    int u = dA[k] * N + Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    long V = 2L * t_orb * N;
    long c = 0;
    int nS = 2 * t_orb;
    for (int s = 0; s < nS; s++) c += V - ball(s * N + e_id);
    long dup = 0;
    for (int a = 0; a < K; a++)
        for (int b2 = a + 1; b2 < K; b2++)
            if (dA[a] == dA[b2] && dB[a] == dB[b2] && GV[a] == GV[b2]) dup++;
    return c + dup * V;
}

static int climb(double until) {
    randomize_lift();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > STALL) {
            randomize_lift();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int k = rndint(K);
        int old = GV[k];
        GV[k] = rndint(N);
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            GV[k] = old;
            set_col(k);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ search */

static int have = 0;
static long bestV = 0;
static Cand bestC;
static int bDA[MAXK], bDB[MAXK], bG[MAXK];

static void try_cand(const Cand *c, double until) {
    if (!apply_cand(c)) return;
    if (!climb(until)) return;
    have = 1;
    bestV = 2L * t_orb * N;
    bestC = *c;
    memcpy(bDA, dA, sizeof dA);
    memcpy(bDB, dB, sizeof dB);
    memcpy(bG, GV, sizeof GV);
}

/* Iterative deepening: every candidate that could still beat bestV gets a slice; slices double per round. */
static void search(Cand *list, int n, double until, double base_slice) {
    for (int round = 0; round < 10; round++) {
        int any = 0;
        for (int i = 0; i < n; i++) {
            double remaining = until - now();
            if (remaining < 0.1) return;
            Cand *c = &list[i];
            long V = 2L * c->t * c->N;
            if (V <= bestV) continue;
            if (V > moore) continue;
            any = 1;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            try_cand(c, now() + slice);
        }
        if (!any) return;
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
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    moore = moore_bound();
    build_lists(ref, moore);

    /* Phase A: baseline bi-Cayley just below the record (cheap, secures the parent's level). */
    search(lo_list, n_lo, t0 + 0.30 * usable, 0.3);

    /* Phase B: bold multi-orbit lifts and bi-Cayley just above the record. */
    double budgetB = 0.6 * usable;
    double baseB = budgetB * 0.004;
    if (baseB < 0.2) baseB = 0.2;
    search(hi_list, n_hi, t0 + 0.90 * usable, baseB);

    /* Phase C: if nothing at all was found, retry the baseline with the remaining time. */
    if (!have) search(lo_list, n_lo, t_end, 0.3);

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&bestC)) { print_complete(); return 0; }
    K = t_orb * d;
    memcpy(dA, bDA, sizeof dA);
    memcpy(dB, bDB, sizeof dB);
    memcpy(GV, bG, sizeof GV);
    finish_structure();
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * t_orb * N, (long)K * N);
    for (int k = 0; k < K; k++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", dA[k] * N + x, (t_orb + dB[k]) * N + Rr[k][x]);
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
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
