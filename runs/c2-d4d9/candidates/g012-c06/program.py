"""Program: voltage lifts of small bipartite base multigraphs over finite groups, searched
by simulated annealing, with bi-Cayley graphs as the one-vertex special case.

Construction:
  * Base: a bipartite multigraph on NA + NA vertices, d-regular, given by an integer matrix M
    (M[i][j] parallel darts from A_i to B_j). Bases: [d] (bi-Cayley, the previous search space),
    [[a, d-a], [d-a, a]] (two per side), and for d = 4 three 3+3 matrices.
  * Lift: over a finite group G of order N (metacyclic Z_m x| Z_k, cyclic, SL(2,q), PSL(2,q)),
    dart e with voltage g_e joins (A_i, x) to (B_j, x*g_e). The lift has 2*NA*N vertices, is
    bipartite, d-regular, and has no multi-edges when parallel darts have distinct voltages.
  * Left multiplication is an automorphism of the lift, so diameter <= D holds iff BFS from
    (f, e) reaches all vertices within D steps for every fiber f.

Search:
  * Candidates = (base, group) pairs with vertex count in a window around the record. They are
    shuffled and visited in iterative-deepening rounds, with slices that double per round.
  * Each slice is simulated annealing over the voltages. Cost = number of vertices not reached
    within D from the fiber identities, summed over fibers. Cost 0 is a valid graph.

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
#define MAXD 8
#define MAXS 3
#define MAXDART (MAXS * MAXD)
#define MAXV (2 * MAXS * MAXN)
#define MAXCAND 24000
#define MAXBASE 16

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

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

/* ------------------------------------------------------------------ groups */

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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,dd) = (a + r^b c, b + dd). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    static int ya[MAXN], yb[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int y = 0; y < N; y++) { ya[y] = y / k; yb[y] = y % k; }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = ya[y], dd = yb[y];
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

/* ------------------------------------------------------------------ base graphs */

typedef struct { int na; int M[MAXS][MAXS]; } Base;
static Base bases[MAXBASE];
static int nbases = 0;

static void push_base(int na, const int *M) {
    if (nbases >= MAXBASE) return;
    for (int i = 0; i < na; i++) {
        int rs = 0, cs = 0;
        for (int j = 0; j < na; j++) {
            if (M[i * na + j] < 0) return;
            rs += M[i * na + j];
            cs += M[j * na + i];
        }
        if (rs != d || cs != d) return;
    }
    Base *b = &bases[nbases];
    memset(b, 0, sizeof *b);
    b->na = na;
    for (int i = 0; i < na; i++)
        for (int j = 0; j < na; j++) b->M[i][j] = M[i * na + j];
    nbases++;
}

static void init_bases(void) {
    nbases = 0;
    int m1[1] = {d};
    push_base(1, m1);
    for (int a = (d + 1) / 2; a <= d - 1; a++) {
        int m2[4] = {a, d - a, d - a, a};
        push_base(2, m2);
    }
    if (d == 4) {
        static const int m3a[9] = {2, 1, 1, 1, 2, 1, 1, 1, 2};
        static const int m3b[9] = {2, 2, 0, 2, 0, 2, 0, 2, 2};
        static const int m3c[9] = {3, 1, 0, 1, 2, 1, 0, 1, 3};
        push_base(3, m3a);
        push_base(3, m3b);
        push_base(3, m3c);
    }
}

/* ------------------------------------------------------------------ lift state */

static int NA = 1, ndart = 0, nf = 2;
static int dA[MAXDART], dB[MAXDART];
static int incA[MAXS][MAXD], incB[MAXS][MAXD];
static int volt[MAXDART], bestVolt[MAXDART], savedVolt[MAXDART];
static int Rf[MAXDART][MAXN];   /* Rf[e][x] = x * g_e */
static int Rb[MAXDART][MAXN];   /* Rb[e][y] = y * g_e^{-1} */

static void setup_base(const Base *b) {
    NA = b->na;
    nf = 2 * NA;
    ndart = 0;
    for (int i = 0; i < NA; i++)
        for (int j = 0; j < NA; j++)
            for (int t = 0; t < b->M[i][j]; t++) {
                dA[ndart] = i;
                dB[ndart] = j;
                ndart++;
            }
    int ca[MAXS] = {0, 0, 0}, cb[MAXS] = {0, 0, 0};
    for (int e = 0; e < ndart; e++) {
        incA[dA[e]][ca[dA[e]]++] = e;
        incB[dB[e]][cb[dB[e]]++] = e;
    }
}

static void set_dart(int e, int g) {
    volt[e] = g;
    int gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rf[e][x] = (int)T[(size_t)x * N + g];
        Rb[e][x] = (int)T[(size_t)x * N + gi];
    }
}

/* True if voltage g on dart e does not repeat a voltage of an earlier dart e2 < lim with the same ends. */
static int ok_dart(int e, int g, int lim) {
    for (int e2 = 0; e2 < lim; e2++) {
        if (e2 != e && dA[e2] == dA[e] && dB[e2] == dB[e] && volt[e2] == g) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            int f = v / N;
            int x = v - f * N;
            if (f < NA) {
                for (int k = 0; k < d; k++) {
                    int e = incA[f][k];
                    int u = (NA + dB[e]) * N + Rf[e][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int j = f - NA;
                for (int k = 0; k < d; k++) {
                    int e = incB[j][k];
                    int u = dA[e] * N + Rb[e][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over fibers of vertices not reached within D from (fiber, identity). 0 = valid lift. */
static long cost_now(void) {
    long V = (long)nf * N;
    long c = 0;
    for (int f = 0; f < nf; f++)
        c += V - (long)ball(f * N + e_id);
    return c;
}

static void randomize_volt(void) {
    for (int e = 0; e < ndart; e++) {
        int g;
        do g = rndint(N); while (!ok_dart(e, g, e));
        set_dart(e, g);
    }
}

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves the best valid voltages in place. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_volt();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bestVolt, volt, sizeof(int) * (size_t)ndart);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double ph = (t - start) / span * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int e = rndint(ndart);
        int g = rndint(N);
        int old = volt[e];
        if (g == old || !ok_dart(e, g, ndart)) continue;
        set_dart(e, g);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestVolt, volt, sizeof(int) * (size_t)ndart);
            }
        } else {
            set_dart(e, old);
        }
    }
    if (bestc != 0) return 0;
    for (int e = 0; e < ndart; e++) set_dart(e, bestVolt[e]);
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int type, q, psl, m, k, r, N, base; } Cand;
static Cand cands[MAXCAND];
static int ncand = 0;

static void push_cand(int type, int q, int psl, int m, int k, int r, int Nv, int base) {
    if (ncand >= MAXCAND) return;
    Cand *c = &cands[ncand++];
    c->type = type;
    c->q = q;
    c->psl = psl;
    c->m = m;
    c->k = k;
    c->r = r;
    c->N = Nv;
    c->base = base;
}

static void add_meta_cands(int Nv, int base) {
    for (int k = 1; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        if (k == 1) { push_cand(0, 0, 0, m, 1, 1, Nv, base); continue; }
        int got = 0;
        for (int r = 2; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            push_cand(0, 0, 0, m, k, r, Nv, base);
            got++;
        }
    }
}

static void add_matrix_cands(int base, long Nlo, long Nhi) {
    static const int qs[5] = {5, 7, 11, 13, 17};
    for (int qi = 0; qi < 5; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < Nlo || o > Nhi || o > MAXN) continue;
            push_cand(1, (int)q, psl, 0, 0, 0, (int)o, base);
        }
}

/* Build the group and dart structure of candidate c. */
static int prepare(const Cand *c) {
    int n;
    if (c->type == 0) n = build_meta(c->m, c->k, c->r);
    else n = build_matrix(c->q, c->psl);
    if (n != c->N || n < 2) return 0;
    setup_base(&bases[c->base]);
    return 1;
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

    if (d < 3 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    init_bases();

    /* Vertex-count window around the reference record. */
    long lowV = ref * 85 / 100;
    long hiV = ref * 115 / 100;
    if (hiV > moore) hiV = moore;

    ncand = 0;
    for (int b = 0; b < nbases; b++) {
        long na = bases[b].na;
        long Nlo = (lowV + 2 * na - 1) / (2 * na);
        long Nhi = hiV / (2 * na);
        if (Nlo < 3) Nlo = 3;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) add_meta_cands((int)Nv, b);
        add_matrix_cands(b, Nlo, Nhi);
    }
    if (ncand == 0) { print_complete(); return 0; }

    int *order = malloc(sizeof(int) * (size_t)ncand);
    for (int i = 0; i < ncand; i++) order[i] = i;
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = order[i];
        order[i] = order[j];
        order[j] = tmp;
    }

    double budget0 = t_end - now();
    double base_slice = budget0 * 0.02;
    if (base_slice < 0.5) base_slice = 0.5;

    long bestV = 2L * d;   /* must beat the K_{d,d} baseline */
    int have = 0;
    Cand bestC;
    memset(&bestC, 0, sizeof bestC);

    for (int round = 0; round < 10; round++) {
        int any = 0;
        for (int ii = 0; ii < ncand; ii++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[order[ii]];
            long V = 2L * bases[c->base].na * c->N;
            if (V <= bestV) continue;
            if (!prepare(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            any = 1;
            if (climb(now() + slice)) {
                have = 1;
                bestV = V;
                bestC = *c;
                memcpy(savedVolt, volt, sizeof(int) * (size_t)ndart);
            }
        }
        if (t_end - now() < 0.2 || !any) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!prepare(&bestC)) { print_complete(); return 0; }
    for (int e = 0; e < ndart; e++) set_dart(e, savedVolt[e]);
    for (int e = 0; e < ndart; e++)
        if (!ok_dart(e, volt[e], ndart)) { print_complete(); return 0; }
    if (cost_now() != 0) { print_complete(); return 0; }

    long V = (long)nf * N;
    long E = (long)NA * N * d;
    printf("%ld %ld\n", V, E);
    for (int i = 0; i < NA; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int e = incA[i][k];
                printf("%d %d\n", i * N + x, (NA + dB[e]) * N + Rf[e][x]);
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
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
