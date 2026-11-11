"""Program: multi-base voltage-lift search with bisection over vertex counts.

Construction:
  * Base graph with B vertices per side (B = 1, 2, 3). Each of the d layers is a
    permutation sigma_l of the B sides, and each dart (i, sigma_l(i), g) carries a
    group element g. The lift joins (A_i, x) to (B_j, x*g). Result: 2BN vertices,
    bipartite, degree d. Darts with the same (i, j) must use distinct g.
  * Left multiplication is an automorphism, so diameter <= D holds iff a BFS from
    every (A_i, e) and (B_j, e) reaches all vertices within D steps.
  * Groups: metacyclic Z_m x| Z_k and SL(2,q) / PSL(2,q), q prime.
  * C engine: candidates (B, group) in a vertex-count window. Bisection over the
    vertex levels, each tested with short simulated-annealing runs (longer for near
    misses). The largest valid lift found is printed.

Safety: C prints K_{d,d} if nothing is found. Python validates the output with
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

#define MAXN 3400
#define MAXB 3
#define MAXD 8
#define MAXK (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXPERM 6
#define MAXCAND 20000
#define BIG_COST (1L << 60)

#define T_HI 2.5
#define T_LO 0.05
#define CYCLES 3.0

static int d, D;
static double t_end;
static double s_short, s_long;
static int loV, hiV;

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

/* ------------------------------------------------------------------ base structure */

static int B = 1, NP = 1, KD = 0, V = 0;
static int PERM[MAXPERM][MAXB], PINV[MAXPERM][MAXB];

static void init_perms(void) {
    int tot = 1;
    for (int i = 0; i < B; i++) tot *= B;
    int cnt = 0;
    for (int code = 0; code < tot; code++) {
        int t = code, used[MAXB], p[MAXB], ok = 1;
        for (int i = 0; i < MAXB; i++) used[i] = 0;
        for (int i = 0; i < B; i++) {
            p[i] = t % B;
            t /= B;
            if (used[p[i]]) ok = 0;
            used[p[i]] = 1;
        }
        if (!ok) continue;
        for (int i = 0; i < B; i++) {
            PERM[cnt][i] = p[i];
            PINV[cnt][p[i]] = i;
        }
        cnt++;
    }
    NP = cnt;
}

/* Dart k = l*B + i: source A_i, layer l, target B_{PERM[LP[l]][i]}, group element G[k]. */
static int LP[MAXD];
static int G[MAXK];
static int cbG[MAXK], cbLP[MAXD];
static int gBestG[MAXK], gBestLP[MAXD];
static int Ra[MAXK][MAXN];   /* Ra[k][x] = x * G[k] */
static int Ri[MAXK][MAXN];   /* Ri[k][y] = y * G[k]^{-1} */

static void set_col(int k) {
    int g = G[k], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Ra[k][x] = (int)T[(size_t)x * N + g];
        Ri[k][x] = (int)T[(size_t)x * N + gi];
    }
}

/* Would dart k carrying element g clash with another dart from the same source to the same target? */
static int conflict(int k, int g) {
    int i = k % B;
    int j = PERM[LP[k / B]][i];
    for (int l = 0; l < d; l++) {
        int k2 = l * B + i;
        if (k2 == k) continue;
        if (PERM[LP[l]][i] == j && G[k2] == g) return 1;
    }
    return 0;
}

static int darts_ok(void) {
    for (int i = 0; i < B; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (PERM[LP[l1]][i] == PERM[LP[l2]][i] && G[l1 * B + i] == G[l2 * B + i])
                    return 0;
    return 1;
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
            int t = v / N, x = v - t * N;
            if (t < B) {
                for (int l = 0; l < d; l++) {
                    int k = l * B + t;
                    int j = PERM[LP[l]][t];
                    int u = (B + j) * N + Ra[k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int j = t - B;
                for (int l = 0; l < d; l++) {
                    int i = PINV[LP[l]][j];
                    int k = l * B + i;
                    int u = i * N + Ri[k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices summed over the 2B representatives (A_i,e) and (B_j,e). 0 = valid. */
static long cost_now(void) {
    long c = 0;
    for (int r = 0; r < 2 * B; r++) {
        int reached = ball(r * N + e_id, D);
        c += (long)(V - reached);
    }
    return c;
}

static void randomize(void) {
    for (int l = 0; l < d; l++) LP[l] = NP > 1 ? rndint(NP) : 0;
    for (int k = 0; k < KD; k++) G[k] = -1;
    for (int k = 0; k < KD; k++) {
        int g = rndint(N), tries = 0;
        while (conflict(k, g) && tries < 1000) { g = rndint(N); tries++; }
        G[k] = g;
    }
    for (int k = 0; k < KD; k++) set_col(k);
}

static long last_min = BIG_COST;
static long near_thresh = 0;

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves a valid state in place. */
static int climb(double until) {
    last_min = BIG_COST;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize();
    long cur = cost_now();
    long bestc = cur;
    memcpy(cbG, G, sizeof(int) * (size_t)KD);
    memcpy(cbLP, LP, sizeof(int) * (size_t)d);
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
        if (NP > 1 && rnd01() < 0.1) {
            int l = rndint(d);
            int old = LP[l];
            int np = rndint(NP);
            if (np == old) continue;
            LP[l] = np;
            if (!darts_ok()) { LP[l] = old; continue; }
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(cbG, G, sizeof(int) * (size_t)KD);
                    memcpy(cbLP, LP, sizeof(int) * (size_t)d);
                }
            } else {
                LP[l] = old;
            }
            continue;
        }
        int k = rndint(KD);
        int g = rndint(N);
        if (g == G[k] || conflict(k, g)) continue;
        int old = G[k];
        G[k] = g;
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(cbG, G, sizeof(int) * (size_t)KD);
                memcpy(cbLP, LP, sizeof(int) * (size_t)d);
            }
        } else {
            G[k] = old;
            set_col(k);
        }
    }
    last_min = bestc;
    if (bestc != 0) return 0;
    memcpy(G, cbG, sizeof(int) * (size_t)KD);
    memcpy(LP, cbLP, sizeof(int) * (size_t)d);
    for (int k = 0; k < KD; k++) set_col(k);
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int B, N, type, q, psl, m, k, r, V;
    unsigned key;
} Cand;

static Cand *cands = NULL;
static int ncand = 0;
static Cand bestCand;
static int bestV = 0;

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok) return 0;
    B = c->B;
    KD = B * d;
    init_perms();
    V = 2 * B * N;
    return 1;
}

static void add_cand(int b, int Nv, int type, int q, int psl, int m, int k, int r) {
    if (ncand >= MAXCAND) return;
    Cand c;
    memset(&c, 0, sizeof c);
    c.B = b;
    c.N = Nv;
    c.type = type;
    c.q = q;
    c.psl = psl;
    c.m = m;
    c.k = k;
    c.r = r;
    c.V = 2 * b * Nv;
    c.key = (unsigned)rnd();
    cands[ncand++] = c;
}

static void gen_candidates(void) {
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (int Vv = loV; Vv <= hiV; Vv++) {
        for (int b = 1; b <= MAXB; b++) {
            if (Vv % (2 * b)) continue;
            int Nv = Vv / (2 * b);
            if (Nv < 3 || Nv > MAXN) continue;
            for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
                for (int psl = 0; psl < 2; psl++) {
                    long q = qs[qi];
                    long o = q * (q * q - 1);
                    if (psl) o /= 2;
                    if (o == Nv) add_cand(b, Nv, 1, (int)q, psl, 0, 0, 0);
                }
            }
            for (int k = 2; k <= Nv / 3; k++) {
                if (Nv % k) continue;
                int m = Nv / k;
                if (m < 3) continue;
                int got = 0;
                for (int r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    add_cand(b, Nv, 0, 0, 0, m, k, r);
                    got++;
                }
            }
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

static int lvl_start[MAXCAND], lvl_end[MAXCAND], lvl_ptr[MAXCAND];
static int nlev = 0;

static void record(const Cand *c) {
    if (V <= bestV) return;
    bestV = V;
    bestCand = *c;
    memcpy(gBestG, G, sizeof(int) * (size_t)KD);
    memcpy(gBestLP, LP, sizeof(int) * (size_t)d);
}

static int try_cand(const Cand *c) {
    if (!apply_cand(c)) return 0;
    near_thresh = V / 100 + 4;
    double rest = t_end - now();
    double sl = s_short < rest ? s_short : rest;
    if (sl < 0.05) return 0;
    if (climb(now() + sl)) return 1;
    if (last_min > near_thresh) return 0;
    rest = t_end - now();
    if (rest < 0.2) return 0;
    sl = s_long < rest ? s_long : rest;
    return climb(now() + sl);
}

static int test_level(int m, int K_att) {
    int s = lvl_start[m], cnt = lvl_end[m] - s;
    if (cnt <= 0) return 0;
    for (int a = 0; a < K_att; a++) {
        if (t_end - now() < 0.3) return 0;
        int idx = s + (lvl_ptr[m]++ % cnt);
        if (try_cand(&cands[idx])) {
            record(&cands[idx]);
            return 1;
        }
    }
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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    loV = (int)(0.86 * (double)ref);
    hiV = (int)(1.2 * (double)ref);
    if (hiV > moore) hiV = (int)moore;
    if (hiV > MAXV) hiV = MAXV;
    if (loV < 6) loV = 6;
    if (hiV < loV) { print_complete(); return 0; }

    cands = malloc(sizeof(Cand) * MAXCAND);
    gen_candidates();
    if (ncand == 0) { print_complete(); return 0; }
    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);

    nlev = 0;
    for (int i = 0; i < ncand; i++) {
        if (i == 0 || cands[i].V != cands[i - 1].V) {
            lvl_start[nlev] = i;
            lvl_end[nlev] = i + 1;
            lvl_ptr[nlev] = 0;
            nlev++;
        } else {
            lvl_end[nlev - 1] = i + 1;
        }
    }

    s_short = usable * 0.015;
    s_long = usable * 0.06;

    /* Bisection over vertex levels: lo is feasible (or -1), hi is infeasible (or nlev). */
    int lo = -1, hi = nlev;
    while (t_end - now() > 0.5) {
        int m;
        if (hi - lo > 1) {
            m = (lo + hi) / 2;
        } else {
            if (hi >= nlev) break;
            m = hi;   /* retest the level just above the feasible one */
        }
        if (test_level(m, 4)) {
            lo = m;
            if (hi <= m) hi = nlev;
        } else if (m < hi) {
            hi = m;
        }
    }

    if (bestV == 0) { print_complete(); return 0; }
    if (!apply_cand(&bestCand)) { print_complete(); return 0; }
    memcpy(G, gBestG, sizeof(int) * (size_t)KD);
    memcpy(LP, gBestLP, sizeof(int) * (size_t)d);
    for (int k = 0; k < KD; k++) set_col(k);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", V, (long)B * d * N);
    for (int x = 0; x < N; x++) {
        for (int k = 0; k < KD; k++) {
            int i = k % B;
            int l = k / B;
            int j = PERM[LP[l]][i];
            int u = i * N + x;
            int v = (B + j) * N + Ra[k][x];
            printf("%d %d\n", u, v);
        }
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
    if best[0] >= lib.moore_bound(d, D) or d < 3 or D < 2:
        return best
    ref = REF_VERTICES.get((d, D), max(best[0], 2 * d))
    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
