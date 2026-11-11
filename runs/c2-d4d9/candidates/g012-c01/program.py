"""Program: bold multi-orbit lift search with a single-orbit fallback.

Construction (new): a d-regular bipartite graph that is a voltage lift of a base
multigraph with nb A-vertices and nb B-vertices (nb = 1..4). Each base row and column
sums to d. Each base edge carries distinct voltages from a group G of order N:
A_{i,x} ~ B_{j,x*g}. Left multiplication is an automorphism, so the diameter is
checked by BFS from A_{i,e} and B_{j,e} only (2*nb sources). Order = 2*nb*N.

Groups: cyclic, metacyclic Z_m x| Z_k, and PSL/SL(2,q) for q in {5,7,11,13,17}.
Candidates need 2*nb*N above the reference and are tried in ascending order of order.
Simulated annealing over the voltages, with iterative deepening.

Fallback: the same engine restricted to nb = 1 (single-orbit bi-Cayley graphs) with
reference 4968, which reaches the 2*2485 = 4970 record group when it is found.

Safety: every output is checked with lib.is_valid. The known start, or K_{d,d}, is
kept if nothing better is found.
"""
import time

import lib

NEW_C = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXB 4
#define MAXDEG 8
#define MAXDART (MAXB * MAXDEG)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 96
#define MAXRAW 8192

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D, maxb = MAXB;
static long REF;
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

/* SL(2,q) or PSL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb2 = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb2) * q + nc) * q + ne;
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
    int type;     /* 0 = metacyclic (k=1 is cyclic), 1 = matrix */
    int q, psl, m, k, r, nb, N;
    long V;       /* vertex count = 2*nb*N */
} Cand;

static Cand raw[MAXRAW];
static int nraw = 0;
static Cand cand[MAXCAND];
static int ncand = 0;

static int apply_cand(const Cand *c) {
    int got;
    if (c->type == 0) got = build_meta(c->m, c->k, c->r);
    else got = build_matrix(c->q, c->psl);
    return got == c->N;
}

static void push_raw(Cand c) {
    if (nraw < MAXRAW) raw[nraw++] = c;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return 0;
}

static void gen_candidates(void) {
    long moore = moore_bound();
    static const int qs[] = {5, 7, 11, 13, 17};
    nraw = 0;
    for (int b = 1; b <= maxb && b <= d && b <= MAXB; b++) {
        long Nlo = REF / (2L * b) + 1;          /* smallest N with 2bN > REF */
        long Nhi = moore / (2L * b);
        if (Nhi > MAXN) Nhi = MAXN;
        long Nend = Nlo + 200;
        if (Nend > Nhi) Nend = Nhi;
        for (long nv = Nlo; nv <= Nend; nv++) {
            int got = 0;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0; c.m = (int)nv; c.k = 1; c.r = 1; c.N = (int)nv;
            c.nb = b; c.V = 2L * b * nv;
            push_raw(c);
            got++;
            for (int k = 2; k <= nv / 3 && got < 6; k++) {
                if (nv % k) continue;
                int m = (int)(nv / k);
                if (m < 3) continue;
                for (int r = 2; r < m && got < 6; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    Cand e;
                    memset(&e, 0, sizeof e);
                    e.type = 0; e.m = m; e.k = k; e.r = r; e.N = (int)nv;
                    e.nb = b; e.V = 2L * b * nv;
                    push_raw(e);
                    got++;
                }
            }
        }
        for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
            for (int psl = 0; psl < 2; psl++) {
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                if (o < Nlo || o > Nhi) continue;
                Cand e;
                memset(&e, 0, sizeof e);
                e.type = 1; e.q = (int)q; e.psl = psl; e.N = (int)o;
                e.nb = b; e.V = 2L * b * o;
                push_raw(e);
            }
        }
    }
    qsort(raw, (size_t)nraw, sizeof(Cand), cmp_cand);
    ncand = nraw < MAXCAND ? nraw : MAXCAND;
    for (int i = 0; i < ncand; i++) cand[i] = raw[i];
}

/* ------------------------------------------------------------------ darts (voltages) */

static int nb = 1;     /* orbits per side */
static int nd = 0;     /* darts = nb*d */
static int dsrc[MAXDART], dtgt[MAXDART], dg[MAXDART];
static int Adart[MAXB][MAXDEG], Bdart[MAXB][MAXDEG];
static int Rr[MAXDART][MAXN];   /* Rr[k][x] = x * g_k */
static int Ri[MAXDART][MAXN];   /* Ri[k][y] = y * g_k^{-1} */
static int Mx[MAXB][MAXB];

static void set_dart(int k) {
    int g = dg[k], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + g];
        Ri[k][x] = (int)T[(size_t)x * N + gi];
    }
}

static void index_darts(void) {
    int cA[MAXB], cB[MAXB];
    for (int i = 0; i < MAXB; i++) { cA[i] = 0; cB[i] = 0; }
    for (int k = 0; k < nd; k++) {
        Adart[dsrc[k]][cA[dsrc[k]]++] = k;
        Bdart[dtgt[k]][cB[dtgt[k]]++] = k;
    }
}

/* Random nb x nb multiplicity matrix with row and column sums d, connected base. */
static int random_matrix(void) {
    for (int attempt = 0; attempt < 200; attempt++) {
        memset(Mx, 0, sizeof Mx);
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < nb; i++) p[i] = i;
            for (int i = nb - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
            for (int i = 0; i < nb; i++) Mx[i][p[i]]++;
        }
        int seen[2 * MAXB], st[2 * MAXB], sp = 0, cnt = 1;
        for (int v = 0; v < 2 * nb; v++) seen[v] = 0;
        seen[0] = 1;
        st[sp++] = 0;
        while (sp > 0) {
            int v = st[--sp];
            for (int w = 0; w < 2 * nb; w++) {
                if (seen[w]) continue;
                int adj;
                if (v < nb && w >= nb) adj = Mx[v][w - nb] > 0;
                else if (v >= nb && w < nb) adj = Mx[w][v - nb] > 0;
                else adj = 0;
                if (adj) { seen[w] = 1; st[sp++] = w; cnt++; }
            }
        }
        if (cnt == 2 * nb) return 1;
    }
    return 0;
}

/* Darts for each base pair (i,j) get distinct random voltages, so the lift is simple. */
static void build_darts(void) {
    int k = 0;
    for (int i = 0; i < nb; i++)
        for (int j = 0; j < nb; j++)
            for (int c = 0; c < Mx[i][j]; c++) {
                dsrc[k] = i;
                dtgt[k] = j;
                int g;
                for (;;) {
                    g = rndint(N);
                    int ok = 1;
                    for (int k2 = 0; k2 < k; k2++)
                        if (dsrc[k2] == i && dtgt[k2] == j && dg[k2] == g) { ok = 0; break; }
                    if (ok) break;
                }
                dg[k] = g;
                k++;
            }
    nd = k;
    index_darts();
    for (k = 0; k < nd; k++) set_dart(k);
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
    int BN = nb * N;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < BN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = Adart[i][t];
                    int u = (nb + dtgt[k]) * N + Rr[k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int rel = v - BN;
                int j = rel / N, y = rel - j * N;
                for (int t = 0; t < d; t++) {
                    int k = Bdart[j][t];
                    int u = dsrc[k] * N + Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2*nb orbit representatives of the vertices not reached within D. 0 = valid. */
static long cost_now(void) {
    long V = 2L * nb * N;
    long c = 0;
    for (int i = 0; i < nb; i++) c += V - ball(i * N + e_id, D);
    for (int j = 0; j < nb; j++) c += V - ball((nb + j) * N + e_id, D);
    return c;
}

/* ------------------------------------------------------------------ annealing */

static int climb(double until) {
    if (N <= d + 1) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    if (!random_matrix()) return 0;
    build_darts();
    int bestG[MAXDART];
    long cur = cost_now();
    long bestc = cur;
    memcpy(bestG, dg, sizeof(int) * (size_t)nd);
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
        int k = rndint(nd);
        int ng = -1;
        for (int tries = 0; tries < 50 && ng < 0; tries++) {
            int g = rndint(N), ok = 1;
            for (int k2 = 0; k2 < nd; k2++)
                if (k2 != k && dsrc[k2] == dsrc[k] && dtgt[k2] == dtgt[k] && dg[k2] == g) {
                    ok = 0;
                    break;
                }
            if (ok) ng = g;
        }
        if (ng < 0) continue;
        int old = dg[k];
        dg[k] = ng;
        set_dart(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestG, dg, sizeof(int) * (size_t)nd);
            }
        } else {
            dg[k] = old;
            set_dart(k);
        }
    }
    if (bestc != 0) return 0;
    memcpy(dg, bestG, sizeof(int) * (size_t)nd);
    for (int k = 0; k < nd; k++) set_dart(k);
    return 1;
}

/* ------------------------------------------------------------------ output */

static int have = 0;
static Cand bestcand;
static int bnb = 1, bnd = 0;
static int bsrc[MAXDART], bdst[MAXDART], bgg[MAXDART];
static double t_end_dummy = 0.0;

static void print_none(void) { printf("0 0\n"); }

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices] [max_orbits]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    REF = argc > 5 ? atol(argv[5]) : 4970;
    if (REF < 0) REF = 0;
    maxb = argc > 6 ? atoi(argv[6]) : MAXB;
    if (maxb < 1) maxb = 1;
    if (maxb > MAXB) maxb = MAXB;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;
    (void)t_end_dummy;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_none(); return 0; }

    long moore = moore_bound();
    gen_candidates();
    if (ncand == 0) { print_none(); return 0; }

    long bestV = REF;
    double budget0 = t_end - now();
    if (budget0 < 0.5) { print_none(); return 0; }
    double base = 0.03 * budget0;
    if (base < 0.15) base = 0.15;

    for (int round = 0; round < 10; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cand[i];
            if (c->V <= bestV) continue;
            if (c->V > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            nb = c->nb;
            if (climb(now() + slice)) {
                have = 1;
                bestV = c->V;
                bestcand = *c;
                bnb = nb;
                bnd = nd;
                memcpy(bsrc, dsrc, sizeof(int) * (size_t)nd);
                memcpy(bdst, dtgt, sizeof(int) * (size_t)nd);
                memcpy(bgg, dg, sizeof(int) * (size_t)nd);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_none(); return 0; }
    if (!apply_cand(&bestcand)) { print_none(); return 0; }
    nb = bnb;
    nd = bnd;
    memcpy(dsrc, bsrc, sizeof(int) * (size_t)nd);
    memcpy(dtgt, bdst, sizeof(int) * (size_t)nd);
    memcpy(dg, bgg, sizeof(int) * (size_t)nd);
    index_darts();
    for (int k = 0; k < nd; k++) set_dart(k);
    if (cost_now() != 0) { print_none(); return 0; }

    long V = 2L * nb * N;
    long E = (long)nd * N;
    printf("%ld %ld\n", V, E);
    for (int k = 0; k < nd; k++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", dsrc[k] * N + x, (nb + dtgt[k]) * N + Rr[k][x]);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _try(args, budget, best, d, D):
    """Run the C engine once; return its graph if it is valid and larger, else best."""
    try:
        text = lib.run_c(NEW_C, args, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            return out
    except Exception:
        pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best

    ref = REF_VERTICES.get((d, D), best[0])
    total = 0.85 * time_limit - 1.0

    # Phase 1: bold multi-orbit lifts (nb = 1..4), target vertex count above ref.
    bold = 0.6 * total - (time.monotonic() - t0)
    if bold > 1.0:
        best = _try([d, D, seed, round(bold, 2), ref, 4], bold, best, d, D)

    # Phase 2: single-orbit fallback, reaching the 2*2485 = 4970 record group.
    remaining = total - (time.monotonic() - t0)
    if best[0] <= ref and remaining > 3.0:
        fb = remaining - 1.5
        best = _try([d, D, seed, round(fb, 2), max(ref - 2, 1), 1], fb, best, d, D)

    return best
