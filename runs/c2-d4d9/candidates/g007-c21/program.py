"""Program: joint voltage/base annealing over SL(2,q), PSL(2,q) and metacyclic groups.

Construction:
  * Group G of order N (full multiplication table, N <= 3200). Base size P <= 6.
    Vertices are A(i,x) and B(j,y), i,j < P, x,y in G. Colour c in 0..d-1 has a
    permutation pm[c]; dart t = c*P + i joins A-row i to B-row pm[c][i] with voltage g_t,
    so A(i,x) ~ B(j, x*g_t). The graph is d-regular, bipartite, with 2*P*N vertices.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from
    A(i,e) and B(j,e) for every i, j reaches all vertices within D steps.

Search:
  * Candidates (group, P) with 2*P*N in [0.6*ref, 1.3*ref], sorted ascending by order.
  * Ladder: attempts are spaced by about 1% in order. A success raises the floor, so the
    ladder climbs toward the frontier while keeping a valid fallback.
  * Each attempt is a simulated annealing run over voltages and, for P >= 2, row swaps
    inside one colour permutation. Temperature follows a sawtooth schedule. The best
    state is kept. A short triage run is followed by a longer run only for near misses.

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
#define MAXP 6
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 200000
#define PPERM 0.25
#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0
#define NEAR_MISS 6
#define BIG_COST (1L << 60)

static int d, D;
static long MOORE;
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

/* ------------------------------------------------------------------ groups */

static int N = 1, e_id = 0;
static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y */
static int INV[MAXN];
static int qg = 2, psl_g = 0;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

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
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    N = (int)n;
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
    return 1;
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
        if (!idxm) { idxm_cap = 0; return 0; }
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
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;      /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, P;
    long V;        /* total vertices = 2 * P * N */
} Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->type != y->type) return x->type - y->type;
    return 0;
}

static void push_cand(const Cand *c) {
    if (nc < MAXCAND) CAND[nc++] = *c;
}

static void gen_candidates(long lowV, long hiV) {
    static const int qs[] = {5, 7, 11, 13, 17};
    nc = 0;
    for (int Pp = 1; Pp <= MAXP; Pp++) {
        for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
            for (int psl = 0; psl < 2; psl++) {
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                long V = 2L * Pp * o;
                if (o > MAXN || V < lowV || V > hiV || V > MOORE) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.P = Pp;
                c.V = V;
                push_cand(&c);
            }
        }
        long step = 2L * Pp;
        long nlo = (lowV + step - 1) / step;
        if (nlo < 3) nlo = 3;
        long nhi = hiV / step;
        if (nhi > MAXN) nhi = MAXN;
        for (long Nv = nlo; Nv <= nhi; Nv++) {
            for (long k = 2; k <= Nv / 3; k++) {
                if (Nv % k) continue;
                long m = Nv / k;
                if (m < 3) continue;
                int got = 0;
                for (long r = 2; r < m && r < 400 && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.m = (int)m;
                    c.k = (int)k;
                    c.r = (int)r;
                    c.N = (int)Nv;
                    c.P = Pp;
                    c.V = step * Nv;
                    push_cand(&c);
                    got++;
                }
            }
        }
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

/* ------------------------------------------------------------------ base shape */

static int P = 1, half = 1, nd = 0;
static int pm[MAXDEG][MAXP];          /* pm[c][i] = B-row hit by A-row i in colour c */
static int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXN];         /* FW[t][x] = x * g_t        */
static int BW[MAXDART][MAXN];         /* BW[t][y] = y * g_t^{-1}   */

static void set_shape(int Pn) {
    P = Pn;
    half = P * N;
    nd = d * P;
    for (int t = 0; t < nd; t++) dI[t] = t % P;
    for (int i = 0; i < P; i++)
        for (int c = 0; c < d; c++) dA[i][c] = c * P + i;
}

static void sync_base(void) {
    int cb[MAXP];
    memset(cb, 0, sizeof cb);
    for (int c = 0; c < d; c++)
        for (int i = 0; i < P; i++) {
            int t = c * P + i, j = pm[c][i];
            dJ[t] = j;
            dB[j][cb[j]++] = t;
        }
}

static void set_dart(int t) {
    int g = vol[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        FW[t][x] = (int)T[(size_t)x * N + g];
        BW[t][x] = (int)T[(size_t)x * N + gi];
    }
}

/* True if dart t with voltage g clashes with a dart s < upto (s != t) on the same (i,j). */
static int conflict_with(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

static int gen_base(void) {
    int perm[MAXP];
    for (int c = 0; c < d; c++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) pm[c][i] = perm[i];
    }
    sync_base();
    for (int t = 0; t < nd; t++) {
        int g = 0, tries = 0;
        do {
            g = rndint(N);
            tries++;
        } while (conflict_with(t, g, t) && tries < 100000);
        if (tries >= 100000) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok || N != c->N) return 0;
    set_shape(c->P);
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
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = dA[i][k];
                    int u = half + dJ[t] * N + FW[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = dB[j][k];
                    int u = dI[t] * N + BW[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices summed over the sources A(i,e) and B(j,e); 0 means valid. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        c += (long)(2 * half - ball(i * N + e_id, D));
    for (int j = 0; j < P; j++)
        c += (long)(2 * half - ball(half + j * N + e_id, D));
    return c;
}

/* ------------------------------------------------------------------ annealing */

static int bpm[MAXDEG][MAXP];
static int bvol[MAXDART];
static long last_min = BIG_COST;

static void save_best(void) {
    memcpy(bpm, pm, sizeof pm);
    memcpy(bvol, vol, sizeof(int) * (size_t)nd);
}

static void load_best(void) {
    memcpy(pm, bpm, sizeof pm);
    memcpy(vol, bvol, sizeof(int) * (size_t)nd);
    sync_base();
    for (int t = 0; t < nd; t++) set_dart(t);
}

/* Simulated annealing over voltages and (for P >= 2) row swaps. Leaves the best state in place. */
static int climb(double until) {
    last_min = BIG_COST;
    if (!gen_base()) return 0;
    long cur = cost_now();
    long bestc = cur;
    save_best();
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        if (P >= 2 && rnd01() < PPERM) {
            int c = rndint(d);
            int i1 = rndint(P), i2 = rndint(P - 1);
            if (i2 >= i1) i2++;
            int j1 = pm[c][i1], j2 = pm[c][i2];
            int t1 = c * P + i1, t2 = c * P + i2;
            pm[c][i1] = j2;
            pm[c][i2] = j1;
            sync_base();
            if (conflict_with(t1, vol[t1], nd) || conflict_with(t2, vol[t2], nd)) {
                pm[c][i1] = j1;
                pm[c][i2] = j2;
                sync_base();
                continue;
            }
            long c2 = cost_now();
            long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = c2;
            } else {
                pm[c][i1] = j1;
                pm[c][i2] = j2;
                sync_base();
            }
        } else {
            int t = rndint(nd);
            int g = rndint(N);
            int old = vol[t];
            if (g == old || conflict_with(t, g, nd)) continue;
            vol[t] = g;
            set_dart(t);
            long c2 = cost_now();
            long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = c2;
            } else {
                vol[t] = old;
                set_dart(t);
            }
        }
        if (cur < bestc) {
            bestc = cur;
            save_best();
        }
    }
    last_min = bestc;
    if (bestc != 0) return 0;
    load_best();
    return cost_now() == 0;
}

/* Triage: short run; a longer run only if the short run came close to valid. */
static int triage(double usable, double remaining) {
    double slice = usable * 0.02;
    if (slice > remaining) slice = remaining;
    if (slice <= 0.0) return 0;
    if (climb(now() + slice)) return 1;
    if (last_min > (long)NEAR_MISS * P) return 0;
    double rest = t_end - now();
    if (rest < 0.3) return 0;
    slice = usable * 0.08;
    if (slice > rest) slice = rest;
    return climb(now() + slice);
}

static long stride_of(long V) {
    long s = V / 100;
    return s < 1 ? 1 : s;
}

/* ------------------------------------------------------------------ output */

static int gpm[MAXDEG][MAXP];
static int gvol[MAXDART];

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    printf("%d %d\n", 2 * half, nd * N);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int t = dA[i][k];
                printf("%d %d\n", i * N + x, half + dJ[t] * N + FW[t][x]);
            }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    if (ref <= 0) ref = MOORE / 2;
    long lowV = (long)(0.6 * (double)ref);
    if (lowV < 2L * d) lowV = 2L * d;
    long hiV = (long)(1.3 * (double)ref);
    if (hiV > MOORE) hiV = MOORE;
    if (hiV < lowV) { print_complete(); return 0; }

    gen_candidates(lowV, hiV);

    long bestV = 0, nextV = lowV;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);

    for (int i = 0; i < nc; i++) {
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV || c->V < nextV) continue;
        nextV = c->V + stride_of(c->V);
        if (!apply_cand(c)) continue;
        if (triage(usable, remaining)) {
            have = 1;
            bestV = c->V;
            best = *c;
            memcpy(gpm, pm, sizeof pm);
            memcpy(gvol, vol, sizeof(int) * (size_t)nd);
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(pm, gpm, sizeof pm);
    memcpy(vol, gvol, sizeof(int) * (size_t)nd);
    sync_base();
    for (int t = 0; t < nd; t++) set_dart(t);
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
    if best[0] >= lib.moore_bound(d, D):
        return best   # nothing beats a Moore graph
    budget = 0.8 * time_limit - 4.0 - (time.monotonic() - t0)
    if budget > 1.0:
        try:
            ref = REF_VERTICES.get((d, D), max(best[0], 2 * d))
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
