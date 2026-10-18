"""Program: multi-orbit voltage lifts over finite groups, searched by simulated annealing.

New construction (not in the parent): a K x K base multigraph lifted over a group G of order N.
There are K A-orbits and K B-orbits, each vertex has degree d, and the graph has 2KN vertices.
Dart j = (u, v, g) joins A(u, x) to B(v, x*g) for all x in G. The base matrix M (entries >= 0,
rows and columns summing to d, connected support) is drawn at random for each restart. K = 1 is
exactly the bi-Cayley case of the parent, so the parent's search is a special case.

Why it helps: vertex count is 2KN, so K = 2 needs only N >= 1243 to beat 4970, and K = 3 needs
N >= 829. Each lift keeps left multiplication as an automorphism, so the diameter test needs
BFS from A(u, e) and B(v, e) only, one per orbit.

Scheduling: matrix groups first, then candidates just below the reference (fallback), then
candidates above the reference in ascending order of vertex count. Iterative deepening gives
each candidate a slice that doubles each round.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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
#define MAXK 3
#define MAXDEG 8
#define MAXD (MAXK * MAXDEG)
#define MAXV (2 * MAXK * MAXN)
#define MAXMAT 512
#define POOL 40000
#define MAXCAND 64

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D;
static long REFV, MOORE;
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
static uint16_t *T = NULL;     /* T[x*N+y] = x*y */
static int *INV = NULL;        /* inverses */
static int *idxm = NULL;
static int idxm_cap = 0;
static int qg = 2, psl_g = 0;
static int gmat[MAXN][4];
static int pw[MAXN];

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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b. */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
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

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

/* SL(2,q) or PSL(2,q), q prime. */
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

/* ------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, orb, prio;
    long key;
} Cand;

static Cand pool[POOL];
static int npool = 0;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void finalize_cand(Cand *c) {
    long V = 2L * c->orb * c->N;
    if (c->type == 1) { c->prio = 0; c->key = 0; }
    else if (V <= REFV) { c->prio = 1; c->key = -V; }
    else { c->prio = 2; c->key = V; }
}

static void pool_add(Cand c) {
    if (npool >= POOL) return;
    finalize_cand(&c);
    pool[npool++] = c;
}

static void add_meta(int Nval, int orb) {
    for (int k = 2; k <= Nval / 3; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            c.orb = orb;
            pool_add(c);
            got++;
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->prio != y->prio) return x->prio - y->prio;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------ base matrices */

static int matl[MAXMAT][MAXK][MAXK];
static int nmat = 0;
static int rowrem[MAXK], colrem[MAXK];
static int cellv[MAXK][MAXK];

static int uf_find(int *p, int x) {
    while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; }
    return x;
}

/* Enumerate kk x kk nonnegative integer matrices with all row/column sums d and connected support. */
static void mat_rec(int cell, int kk) {
    if (nmat >= MAXMAT) return;
    if (cell == kk * kk) {
        for (int i = 0; i < kk; i++)
            if (rowrem[i] || colrem[i]) return;
        int par[2 * MAXK];
        for (int i = 0; i < 2 * kk; i++) par[i] = i;
        for (int r = 0; r < kk; r++)
            for (int c = 0; c < kk; c++)
                if (cellv[r][c]) {
                    int a = uf_find(par, r);
                    int b = uf_find(par, kk + c);
                    par[a] = b;
                }
        int root = uf_find(par, 0);
        for (int i = 1; i < 2 * kk; i++)
            if (uf_find(par, i) != root) return;
        memcpy(matl[nmat], cellv, sizeof cellv);
        nmat++;
        return;
    }
    int r = cell / kk, c = cell % kk;
    int hi = rowrem[r] < colrem[c] ? rowrem[r] : colrem[c];
    for (int v = 0; v <= hi; v++) {
        cellv[r][c] = v;
        rowrem[r] -= v;
        colrem[c] -= v;
        mat_rec(cell + 1, kk);
        rowrem[r] += v;
        colrem[c] += v;
    }
    cellv[r][c] = 0;
}

static void gen_mats(int kk) {
    nmat = 0;
    for (int i = 0; i < kk; i++) { rowrem[i] = d; colrem[i] = d; }
    memset(cellv, 0, sizeof cellv);
    mat_rec(0, kk);
}

/* ------------------------------------------------------------ lift state */

static int K = 1;
static int dto[MAXD];      /* dart j leaves A-orbit j/d and enters B-orbit dto[j] */
static int dg[MAXD];       /* voltage */
static int dgi[MAXD];      /* inverse voltage */
static int tol[MAXK][MAXDEG];
static int found_K = 0;
static int found_dto[MAXD], found_dg[MAXD];

static void rebuild_tol(void) {
    int cnt[MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int j = 0; j < K * d; j++) {
        int v = dto[j];
        tol[v][cnt[v]++] = j;
    }
}

static void setup_darts(int mi) {
    int pos[MAXK];
    memset(pos, 0, sizeof pos);
    for (int u = 0; u < K; u++)
        for (int v = 0; v < K; v++)
            for (int c = 0; c < matl[mi][u][v]; c++)
                dto[u * d + pos[u]++] = v;
    rebuild_tol();
}

/* True if dart j with voltage g would duplicate another dart of the same (u,v) pair.
   If partial is set, only darts with index < j are checked. */
static int clash(int j, int g, int partial) {
    int u = j / d, v = dto[j];
    for (int i = 0; i < d; i++) {
        int jj = u * d + i;
        if (jj == j) continue;
        if (partial && jj > j) continue;
        if (dto[jj] == v && dg[jj] == g) return 1;
    }
    return 0;
}

static void randomize_lift(void) {
    for (int j = 0; j < K * d; j++) {
        int g;
        do g = rndint(N); while (clash(j, g, 1));
        dg[j] = g;
        dgi[j] = INV[g];
    }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of vertices within dmax of src (src is an A or B vertex of the lift). */
static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int KN = K * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < KN) {
                int u = v / N, x = v - u * N;
                const uint16_t *row = T + (size_t)x * N;
                for (int i = 0; i < d; i++) {
                    int j = u * d + i;
                    int w = KN + dto[j] * N + row[dg[j]];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            } else {
                int t = v - KN;
                int vv = t / N, y = t - vv * N;
                const uint16_t *row = T + (size_t)y * N;
                for (int i = 0; i < d; i++) {
                    int j = tol[vv][i];
                    int w = (j / d) * N + row[dgi[j]];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over one representative per orbit. 0 = valid. */
static long cost_now(void) {
    long NV = 2L * K * N;
    long c = 0;
    for (int u = 0; u < K; u++) c += NV - ball(u * N + e_id, D);
    for (int v = 0; v < K; v++) c += NV - ball(K * N + v * N + e_id, D);
    return c;
}

/* ------------------------------------------------------------ search */

/* Simulated annealing over voltages with a random base matrix. Returns 1 and records the valid lift. */
static int climb(double until) {
    if (N <= d + 1 || nmat <= 0) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    int mi = rndint(nmat);
    setup_darts(mi);
    randomize_lift();
    int nd = K * d;
    long cur = cost_now();
    long bestc = cur;
    static int bestg[MAXD];
    memcpy(bestg, dg, sizeof(int) * (size_t)nd);
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
        int j = rndint(nd);
        int old = dg[j];
        int g;
        do g = rndint(N); while (g == old || clash(j, g, 0));
        dg[j] = g;
        dgi[j] = INV[g];
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestg, dg, sizeof(int) * (size_t)nd);
            }
        } else {
            dg[j] = old;
            dgi[j] = INV[old];
        }
    }
    if (bestc != 0) return 0;
    memcpy(dg, bestg, sizeof(int) * (size_t)nd);
    for (int j = 0; j < nd; j++) dgi[j] = INV[dg[j]];
    found_K = K;
    memcpy(found_dto, dto, sizeof(int) * (size_t)nd);
    memcpy(found_dg, dg, sizeof(int) * (size_t)nd);
    return 1;
}

static void load_found(void) {
    K = found_K;
    int nd = K * d;
    memcpy(dto, found_dto, sizeof(int) * (size_t)nd);
    memcpy(dg, found_dg, sizeof(int) * (size_t)nd);
    for (int j = 0; j < nd; j++) dgi[j] = INV[dg[j]];
    rebuild_tol();
}

/* ------------------------------------------------------------ output */

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
    REFV = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }
    MOORE = moore_bound();
    if (REFV <= 0) REFV = MOORE / 8;
    if (REFV < 1) REFV = 1;

    long lowV = (long)(0.86 * (double)REFV);
    long hiV = (long)(1.14 * (double)REFV);
    if (hiV > MOORE) hiV = MOORE;

    /* Pool of candidates: matrix groups, then metacyclic groups for K = 1, 2, 3. */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++)
        for (int psl = 0; psl < 2; psl++)
            for (int orb = 1; orb <= MAXK; orb++) {
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                long V = 2L * orb * o;
                if (o > MAXN || o < d + 2 || V < lowV || V > hiV) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.orb = orb;
                pool_add(c);
            }
    for (int orb = 1; orb <= MAXK; orb++) {
        long Nlo = (lowV + 2L * orb - 1) / (2L * orb);
        long Nhi = hiV / (2L * orb);
        if (Nhi > MAXN) Nhi = MAXN;
        if (Nlo < d + 2) Nlo = d + 2;
        if (Nlo < 3) Nlo = 3;
        for (long Nv = Nhi; Nv >= Nlo; Nv--) add_meta((int)Nv, orb);
    }

    qsort(pool, (size_t)npool, sizeof(Cand), cmp_cand);
    static Cand cands[MAXCAND];
    int ncand = 0, tcnt[3] = {0, 0, 0};
    const int tcap[3] = {12, 8, 40};
    for (int i = 0; i < npool && ncand < MAXCAND; i++) {
        int p = pool[i].prio;
        if (tcnt[p] < tcap[p]) { cands[ncand++] = pool[i]; tcnt[p]++; }
    }

    Cand best;
    memset(&best, 0, sizeof best);
    int have = 0;
    long bestV = 0;

    double budget0 = t_end - now();
    double base = budget0 * 0.02;
    if (base < 0.4) base = 0.4;
    if (base > 2.0) base = 2.0;

    for (int round = 0; round < 6; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[i];
            if (2L * c->orb * c->N <= bestV) continue;
            if (2L * c->orb * c->N > MOORE) continue;
            if (!apply_cand(c)) continue;
            long V = 2L * c->orb * N;
            if (V <= bestV || V > MOORE) continue;
            K = c->orb;
            gen_mats(K);
            if (nmat <= 0) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV = V;
                best = *c;
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have || !apply_cand(&best)) { print_complete(); return 0; }
    load_found();
    if (cost_now() != 0) { print_complete(); return 0; }

    long mE = (long)K * d * N;
    printf("%d %ld\n", 2 * K * N, mE);
    for (int j = 0; j < K * d; j++) {
        int u = j / d;
        for (int x = 0; x < N; x++)
            printf("%d %d\n", u * N + x,
                   K * N + dto[j] * N + (int)T[(size_t)x * N + dg[j]]);
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
    moore = lib.moore_bound(d, D)
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= moore:
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        ref = REF_VERTICES.get((d, D), max(best[0], moore // 8))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
