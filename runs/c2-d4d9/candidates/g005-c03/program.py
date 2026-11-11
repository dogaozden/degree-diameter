"""Program: voltage lifts of small bipartite base graphs over finite groups.

Construction (bold change from bi-Cayley search):
  * Base graph: P A-vertices and P B-vertices, with M = d/P parallel darts per (A_i, B_j) pair.
    Every base vertex has degree d. Requires P | d, P in {1, 2, 4}.
  * Group G of order N (metacyclic Z_m x| Z_k, or SL/PSL(2,q)), given by a multiplication table.
    Dart (A_i, B_j, s) joins (A_i, x) to (B_j, x*s). The lift has 2PN vertices, is d-regular,
    bipartite, and simple when the M voltages of each pair are distinct.
  * Left multiplication by G is an automorphism, so diameter <= D holds iff BFS from (u, e)
    reaches all vertices within D steps for each of the 2P base vertices u.
  * C engine: hill-climbs voltages to minimise unreached (source, vertex) pairs.
    Candidates: SL(2,13) with P=1 as a safe fallback (4368 vertices), then SL(2,11) with P=2,
    PSL(2,11) with P=4, and metacyclic groups with P=2 and P=4 just above the record vertex
    count, interleaved, then P=1 metacyclic groups.

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
#define MAXP 4
#define MAXD 8
#define MAXNT 32
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 64
#define STALL_LIMIT 3000

static int d, D;
static int P, M, NT;            /* base vertices per side, darts per pair, total darts */
static int N = 0, e_id = 0;     /* group order and identity */
static uint16_t *T = NULL;      /* T[x*N+y] = x*y */
static int *INV = NULL;         /* inverses */
static int VV[MAXNT], VI[MAXNT];/* dart voltages and their inverses */
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

/* ------------------------------------------------------------------ groups */

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
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r;
    int P, N;
    double frac;
} Cand;

static int apply_cand(const Cand *c) {
    int n = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (n < 2) return 0;
    P = c->P;
    M = d / P;
    NT = P * d;
    return n;
}

static Cand mk_mat(int q, int psl, int P_) {
    Cand c;
    memset(&c, 0, sizeof c);
    long o = (long)q * ((long)q * q - 1);
    if (psl) o /= 2;
    c.type = 1;
    c.q = q;
    c.psl = psl;
    c.P = P_;
    c.N = (int)o;
    c.frac = 0.1;
    return c;
}

static Cand mk_meta(int P_, int m, int k, int r) {
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 0;
    c.m = m;
    c.k = k;
    c.r = r;
    c.P = P_;
    c.N = m * k;
    c.frac = 0.1;
    return c;
}

static void push(Cand *list, int *n, Cand c) {
    if (*n < MAXCAND) list[(*n)++] = c;
}

static void gen_meta(int P_, int Nlo, int Nhi, Cand *list, int *n) {
    for (int Nv = Nlo; Nv <= Nhi && *n < MAXCAND; Nv++) {
        int got = 0;
        for (int k = 2; k <= Nv / 3 && got < 2 && *n < MAXCAND; k++) {
            if (Nv % k) continue;
            int m = Nv / k;
            if (m < 3) continue;
            for (int r = 2; r < m; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1 % m) continue;
                push(list, n, mk_meta(P_, m, k, r));
                got++;
                break;
            }
        }
    }
}

static Cand all[4 * MAXCAND];
static int nall = 0;

static void build_order(long ref) {
    static Cand L2[MAXCAND], L4[MAXCAND], L1[MAXCAND];
    int n2 = 0, n4 = 0, n1 = 0;
    nall = 0;
    /* fallback: SL(2,13) bi-Cayley, order 2184 with P=1, 4368 vertices */
    all[nall] = mk_mat(13, 0, 1);
    all[nall].frac = 0.25;
    nall++;

    if (d % 2 == 0) {
        push(L2, &n2, mk_mat(11, 0, 2));  /* SL(2,11): 5280 vertices if it works */
        long Nlo = ref > 0 ? ref / 4 + 1 : 3;
        gen_meta(2, (int)Nlo, (int)Nlo + 24, L2, &n2);
    }
    if (d % 4 == 0) {
        push(L4, &n4, mk_mat(11, 1, 4));  /* PSL(2,11): 5280 vertices if it works */
        long Nlo = ref > 0 ? ref / 8 + 1 : 3;
        gen_meta(4, (int)Nlo, (int)Nlo + 24, L4, &n4);
    }
    {
        long Nlo = ref > 0 ? ref / 2 + 1 : 3;
        gen_meta(1, (int)Nlo, (int)Nlo + 8, L1, &n1);
    }
    for (int i = 0; i < n2 || i < n4; i++) {
        if (i < n2) all[nall++] = L2[i];
        if (i < n4) all[nall++] = L4[i];
    }
    for (int i = 0; i < n1; i++) all[nall++] = L1[i];
}

/* ------------------------------------------------------------------ lift state */

static void setdart(int t, int v) {
    VV[t] = v;
    VI[t] = INV[v];
}

/* True if voltage v at dart t clashes with another dart of the same pair. */
static int conflict(int t, int v) {
    int base = (t / M) * M;
    for (int u = base; u < base + M; u++)
        if (u != t && VV[u] == v) return 1;
    return 0;
}

static void randomize(void) {
    for (int t = 0; t < NT; t++) {
        int base = (t / M) * M;
        int v, ok;
        do {
            v = rndint(N);
            ok = 1;
            for (int u = base; u < t; u++)
                if (VV[u] == v) { ok = 0; break; }
        } while (!ok);
        setdart(t, v);
    }
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Vertices: A_i,x -> i*N+x (i<P); B_j,y -> P*N + j*N + y. */
static int bfs(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int PN = P * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                const uint16_t *row = T + (size_t)x * N;
                for (int j = 0; j < P; j++) {
                    int base = (i * P + j) * M;
                    for (int k = 0; k < M; k++) {
                        int u = PN + j * N + (int)row[VV[base + k]];
                        if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                    }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                const uint16_t *row = T + (size_t)y * N;
                for (int i = 0; i < P; i++) {
                    int base = (i * P + j) * M;
                    for (int k = 0; k < M; k++) {
                        int u = i * N + (int)row[VI[base + k]];
                        if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    long c = 0;
    long NV = 2L * P * N;
    for (int u = 0; u < 2 * P; u++) {
        int src = (u < P) ? (u * N + e_id) : (P * N + (u - P) * N + e_id);
        c += NV - bfs(src, D);
    }
    return c;
}

static int climb(double until) {
    randomize();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL_LIMIT) {
            randomize();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int t = rndint(NT);
        int old = VV[t];
        int v;
        do v = rndint(N); while (conflict(t, v));
        setdart(t, v);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            setdart(t, old);
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
    int PN = P * N;
    printf("%d %ld\n", 2 * PN, (long)P * d * N);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < P; j++)
                for (int k = 0; k < M; k++) {
                    int t = (i * P + j) * M + k;
                    int y = (int)T[(size_t)x * N + VV[t]];
                    printf("%d %d\n", i * N + x, PN + j * N + y);
                }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 0;
    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    long moore = moore_bound();
    long bestV = 2L * d;
    int have = 0;
    static Cand best;
    static int bestVV[MAXNT];

    build_order(ref);
    double budget0 = t_end - now();

    for (int i = 0; i < nall; i++) {
        Cand *c = &all[i];
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        long vert = 2L * c->P * c->N;
        if (vert <= bestV || vert > moore) continue;
        if (d % c->P) continue;
        if (!apply_cand(c)) continue;
        if (M > N || 2L * P * N != vert) continue;
        double slice = budget0 * c->frac;
        if (slice > remaining) slice = remaining;
        if (climb(now() + slice)) {
            have = 1;
            bestV = vert;
            best = *c;
            memcpy(bestVV, VV, sizeof(int) * (size_t)NT);
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(VV, bestVV, sizeof(int) * (size_t)NT);
    for (int t = 0; t < NT; t++) VI[t] = INV[VV[t]];
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
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph
    if budget > 1.0:
        try:
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
