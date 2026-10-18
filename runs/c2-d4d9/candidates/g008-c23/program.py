"""Program: bi-Cayley search (phase 1) followed by a voltage-lift search over metacyclic groups (phase 2).

Phase 1 is the parent's bi-Cayley search (2N vertices, d-regular, left-multiplication symmetry). It
keeps the known record-level result as a safe baseline.

Phase 2 is the new, different construction. It takes a small bipartite base multigraph with b vertices
per side and d perfect matchings between them. Each base dart gets a voltage in a metacyclic group G
of order N. The lift has 2bN vertices and is d-regular and bipartite. Left multiplication is an
automorphism, so diameter <= D holds iff BFS from (s, e) reaches everything within D steps, for each of
the 2b base vertices s. Hill climbing on voltages and matchings drives the number of unreached pairs
to zero. Any success with more than the current best vertex count replaces the output.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with lib.is_valid and
keeps the best valid graph, falling back to the known start or K_{d,d}.
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
#define MAXB 4
#define LMAX 40000

static int d, D;
static double t_end;
static long ref_vertices = 4970;

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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). Identity is 0. */
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

/* ------------------------------------------------------------------ bi-Cayley connection set */

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

static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 4000) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
            stall = 0;
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
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ best-graph buffer */

static int gb_n = 0, gb_m = 0, gb_cap = 0;
static int *gb_u = NULL, *gb_v = NULL;

static void gb_alloc(int cap) {
    if (cap > gb_cap) {
        free(gb_u);
        free(gb_v);
        gb_u = malloc(sizeof(int) * (size_t)cap);
        gb_v = malloc(sizeof(int) * (size_t)cap);
        gb_cap = cap;
    }
    gb_m = 0;
}

static void gb_add(int u, int v) {
    gb_u[gb_m] = u;
    gb_v[gb_m] = v;
    gb_m++;
}

/* ------------------------------------------------------------------ voltage lift (phase 2) */

/* Base: b A-vertices (ids 0..b-1) and b B-vertices (ids b..2b-1). For each matching j < d,
   sig[j][i] is the B index of the dart from A_i. Dart (i,j) has voltage vol[i][j] in G.
   Lift: (A_i, g) ~ (B_{sig[j][i]}, g*vol[i][j]). Every lifted vertex has degree d. */
static int sig[MAXDEG][MAXB];
static int sigi[MAXDEG][MAXB];
static int vol[MAXB][MAXDEG];
static int wvol[MAXDEG][MAXB];

static void lift_refresh(int b) {
    for (int j = 0; j < d; j++)
        for (int i = 0; i < b; i++)
            sigi[j][sig[j][i]] = i;
    for (int j = 0; j < d; j++)
        for (int w = 0; w < b; w++)
            wvol[j][w] = INV[vol[sigi[j][w]][j]];
}

static void lift_randomize(int b) {
    for (int j = 0; j < d; j++) {
        int p[MAXB];
        for (int i = 0; i < b; i++) p[i] = i;
        for (int i = b - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int t = p[i];
            p[i] = p[r];
            p[r] = t;
        }
        for (int i = 0; i < b; i++) sig[j][i] = p[i];
    }
    for (int i = 0; i < b; i++)
        for (int j = 0; j < d; j++)
            vol[i][j] = rndint(N);
    lift_refresh(b);
}

static int lstamp[LMAX];
static int lqv[LMAX];
static int ltick = 0;

/* BFS in the lift from vertex src; returns number of vertices within distance D. */
static int lift_bfs(int b, int src) {
    if (++ltick == 0x7fffffff) {
        memset(lstamp, 0, sizeof lstamp);
        ltick = 1;
    }
    int head = 0, tail = 0;
    int boundA = b * N;
    lstamp[src] = ltick;
    lqv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = lqv[head];
            int g = v % N;
            if (v < boundA) {
                int i = v / N;
                for (int j = 0; j < d; j++) {
                    int u = (b + sig[j][i]) * N + (int)T[(size_t)g * N + vol[i][j]];
                    if (lstamp[u] != ltick) { lstamp[u] = ltick; lqv[tail++] = u; }
                }
            } else {
                int w = v / N - b;
                for (int j = 0; j < d; j++) {
                    int u = sigi[j][w] * N + (int)T[(size_t)g * N + wvol[j][w]];
                    if (lstamp[u] != ltick) { lstamp[u] = ltick; lqv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Zero iff the lift is simple (no duplicate lifted edges) and has diameter <= D. */
static long lift_cost(int b) {
    long V = 2L * b * N;
    long pen = 0;
    for (int i = 0; i < b; i++)
        for (int j = 0; j < d; j++)
            for (int j2 = j + 1; j2 < d; j2++)
                if (sig[j][i] == sig[j2][i] && vol[i][j] == vol[i][j2]) pen++;
    long un = 0;
    for (int s = 0; s < 2 * b; s++)
        un += V - lift_bfs(b, s * N + e_id);
    return un + pen * V;
}

static int lift_search(int b, double until) {
    lift_randomize(b);
    long cur = lift_cost(b), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > 3000) {
            lift_randomize(b);
            cur = lift_cost(b);
            best_c = cur;
            stall = 0;
            continue;
        }
        int doswap = (b >= 2) && (rndint(4) == 3);
        if (!doswap) {
            int i = rndint(b), j = rndint(d);
            int old = vol[i][j];
            vol[i][j] = rndint(N);
            lift_refresh(b);
            long nc = lift_cost(b);
            if (nc <= cur || rnd01() < 0.02) cur = nc;
            else { vol[i][j] = old; lift_refresh(b); }
        } else {
            int j = rndint(d), i1 = rndint(b), i2 = rndint(b - 1);
            if (i2 >= i1) i2++;
            int t = sig[j][i1];
            sig[j][i1] = sig[j][i2];
            sig[j][i2] = t;
            lift_refresh(b);
            long nc = lift_cost(b);
            if (nc <= cur || rnd01() < 0.02) cur = nc;
            else {
                t = sig[j][i1];
                sig[j][i1] = sig[j][i2];
                sig[j][i2] = t;
                lift_refresh(b);
            }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ phases */

static void phase_bicayley(void) {
    long moore = moore_bound();
    long bestN = d;

    int recHalf = (int)(ref_vertices / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;

    static Cand all[3 * MAXCAND + 32];
    static Cand hi[MAXCAND], lo[MAXCAND];
    int na = 0, nh = 0, nl = 0;

    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (na >= 16) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            c.frac = 0.25;
            all[na++] = c;
        }
    }
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo, &nl);
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, hi, &nh);
    for (int i = 0; i < nl; i++) all[na++] = lo[i];
    for (int i = 0; i < nh; i++) all[na++] = hi[i];

    double budget0 = t_end - now();
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    double base_slice = budget0 * 0.03;
    if (base_slice < 0.3) base_slice = 0.3;
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < na; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &all[i];
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestN = N;
                best = *c;
                memcpy(bS, S, sizeof(int) * (size_t)d);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) return;
    if (!apply_cand(&best)) return;
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) return;

    gb_alloc(N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            gb_add(x, N + Rr[k][x]);
    gb_n = 2 * N;
}

static void phase_lift(void) {
    long vmax = moore_bound();
    if (vmax > LMAX) vmax = LMAX;
    static int divs[MAXN + 1];
    int fails = 0;

    while (now() < t_end - 0.05) {
        int b = 1 + rndint(MAXB);
        long Nmin = (long)gb_n / (2L * b) + 1;
        if (Nmin < 2) Nmin = 2;
        long Nmax = vmax / (2L * b);
        if (Nmax > MAXN) Nmax = MAXN;
        if (Nmin > Nmax) {
            int any = 0;
            for (int bb = 1; bb <= MAXB; bb++) {
                long lo_ = (long)gb_n / (2L * bb) + 1;
                if (lo_ < 2) lo_ = 2;
                long hi_ = vmax / (2L * bb);
                if (hi_ > MAXN) hi_ = MAXN;
                if (lo_ <= hi_) any = 1;
            }
            if (!any) break;
            continue;
        }
        long span = Nmax - Nmin;
        if (span > 150) span = 150;
        int Nv = (int)(Nmin + rndint((int)span + 1));

        int nd = 0;
        for (int k = 1; k <= Nv; k++)
            if (Nv % k == 0 && (k == 1 || Nv / k >= 3)) divs[nd++] = k;
        int k = divs[rndint(nd)];
        int m = Nv / k;
        int r = 1;
        if (k >= 2 && m >= 3) {
            for (int t = 0; t < 40; t++) {
                int cand = 2 + rndint(m - 2);
                if (gcd_l(cand, m) == 1 && powmod_l(cand, k, m) == 1) { r = cand; break; }
            }
        }
        if (!build_meta(m, k, r)) continue;

        double slice = 0.2 * (1.0 + fails / 20.0);
        double rem = t_end - now();
        if (slice > rem) slice = rem;
        if (slice < 0.02) break;

        if (lift_search(b, now() + slice)) {
            long total = 2L * b * N;
            if (total > gb_n) {
                gb_alloc(b * N * d);
                for (int i = 0; i < b; i++)
                    for (int j = 0; j < d; j++)
                        for (int g = 0; g < N; g++)
                            gb_add(i * N + g,
                                   (b + sig[j][i]) * N + (int)T[(size_t)g * N + vol[i][j]]);
                gb_n = (int)total;
            }
        } else {
            fails++;
        }
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
    ref_vertices = ref;

    double t0 = now();
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    double total_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    gb_n = 0;
    gb_m = 0;
    t_end = t0 + 0.3 * usable;
    phase_bicayley();
    t_end = total_end;
    phase_lift();

    if (gb_n == 0) { print_complete(); return 0; }
    printf("%d %d\n", gb_n, gb_m);
    for (int e = 0; e < gb_m; e++) printf("%d %d\n", gb_u[e], gb_v[e]);
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
