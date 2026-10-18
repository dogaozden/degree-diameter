"""Program: multi-base voltage lifts over small groups, with simulated annealing.

Construction:
  * Base bipartite multigraph with NB vertices per side (NB = 1..6). Every base vertex has
    degree d. Dart t joins base A-vertex t/d to base B-vertex LAB[t] with voltage G[t] in a
    group G of order N (metacyclic Z_m x| Z_k, or SL(2,q)/PSL(2,q), q in {5,7,11,13}).
  * Lift: A(i,x) ~ B(j, x*g) for each dart (i,j,g). Result: 2*NB*N vertices, bipartite,
    degree d, simple (no two darts share the same (i, j, g)).
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from A_i e and
    B_j e reaches every vertex within D steps, for all base vertices i, j.
  * This generalises the single-orbit bi-Cayley graph (NB = 1) to several orbits, so
    orders like 10 * 497 = 4970 become reachable.

Search:
  * Candidates (NB, group) with vertex count in a window around the reference are sorted
    ascending. Each attempt anneals the voltages and the label assignment for a time slice.
    The next attempt goes to the candidate with the fewest tries among those above the
    current best, so the best order climbs step by step.

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
#define MAXB 6
#define MAXDEG 8
#define MAXDARTS (MAXB * MAXDEG)
#define MAXV 16384
#define MAXCAND 16384

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
    for (int bq = 1; bq < k; bq++) pw[bq] = (int)((long)pw[bq - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, bq = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[bq] * c) % m;
            int bb = (bq + dd) % k;
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
    int type;      /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r;
    int N;         /* group order */
    int b;         /* base vertices per side */
    long V;        /* total vertices 2*b*N */
    int attempts;
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void push_cand(const Cand *c) {
    if (ncand < MAXCAND) cands[ncand++] = *c;
}

static int cmp_cand(const void *pa, const void *pb) {
    long x = ((const Cand *)pa)->V, y = ((const Cand *)pb)->V;
    return (x > y) - (x < y);
}

static const int mq[] = {5, 7, 11, 13};

static void gen_for_order(int Nv, int bb, long lo, long hi) {
    long V = 2L * bb * Nv;
    if (V < lo || V > hi) return;
    int pushed = 0;
    Cand c;
    for (int qi = 0; qi < 4; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = mq[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o != Nv || pushed >= 4) continue;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = Nv;
            c.b = bb;
            c.V = V;
            push_cand(&c);
            pushed++;
        }
    }
    for (int k = 1; k <= 12 && k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int cnt = 0;
        for (int r = 1; r < m && cnt < 2 && pushed < 4; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            c.b = bb;
            c.V = V;
            push_cand(&c);
            cnt++;
            pushed++;
        }
    }
}

/* ------------------------------------------------------------------ base lift state */

static int NB = 1;                   /* base vertices per side */
static int ND = 0;                   /* darts = NB*d */
static int BN = 0;                   /* NB*N: index of first B vertex */
static int VT = 0;                   /* total vertices = 2*BN */
static int G[MAXDARTS];              /* voltage of dart t (group element) */
static int LAB[MAXDARTS];            /* B-label of dart t; A-end of dart t is t/d */
static int LB[MAXB][MAXDEG];         /* darts whose B-label is j */
static uint16_t Rr[MAXDARTS][MAXN];  /* Rr[t][x] = x * G[t] */
static uint16_t Ri[MAXDARTS][MAXN];  /* Ri[t][y] = y * G[t]^{-1} */

static void set_dart(int t) {
    int g = G[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rr[t][x] = T[(size_t)x * N + g];
        Ri[t][x] = T[(size_t)x * N + gi];
    }
}

static void rebuild_lb(void) {
    for (int j = 0; j < NB; j++) {
        int c = 0;
        for (int t = 0; t < ND; t++)
            if (LAB[t] == j && c < d) LB[j][c++] = t;
    }
}

/* No two darts with the same A-end, same B-label and same voltage (would give a duplicate edge). */
static int dup_free(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (t1 / d == t2 / d && LAB[t1] == LAB[t2] && G[t1] == G[t2]) return 0;
    return 1;
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of vertices within distance dmax of src (including src). */
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
            if (v < BN) {
                int i = v / N, x = v - i * N;
                for (int kk = 0; kk < d; kk++) {
                    int t = i * d + kk;
                    int u = BN + LAB[t] * N + Rr[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int j = w / N, y = w - j * N;
                for (int kk = 0; kk < d; kk++) {
                    int t = LB[j][kk];
                    int u = (t / d) * N + Ri[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base sources A_i e and B_j e of vertices not reached within D (0 = valid). */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < NB; i++) {
        c += VT - ball(i * N + e_id, D);
        c += VT - ball(BN + i * N + e_id, D);
    }
    return c;
}

static int randomize_state(void) {
    for (int tries = 0; tries < 200; tries++) {
        for (int t = 0; t < ND; t++) G[t] = rndint(N);
        for (int t = 0; t < ND; t++) LAB[t] = t % NB;
        for (int t = ND - 1; t > 0; t--) {
            int s = rndint(t + 1);
            int tmp = LAB[t];
            LAB[t] = LAB[s];
            LAB[s] = tmp;
        }
        if (dup_free()) {
            for (int t = 0; t < ND; t++) set_dart(t);
            rebuild_lb();
            return 1;
        }
    }
    return 0;
}

/* Simulated annealing with sawtooth reheating; returns 1 and leaves the best valid state in place. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    if (!randomize_state()) return 0;
    long cur = cost_now();
    long bestc = cur;
    static int bG[MAXDARTS], bL[MAXDARTS];
    memcpy(bG, G, sizeof(int) * (size_t)ND);
    memcpy(bL, LAB, sizeof(int) * (size_t)ND);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double tt = now();
            if (tt >= until) break;
            double f = (tt - start) / span;
            double ph = f * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        if (rndint(10) < 6) {
            /* voltage move */
            int t = rndint(ND);
            int old = G[t];
            int x = rndint(N);
            if (x == old) continue;
            G[t] = x;
            if (!dup_free()) { G[t] = old; continue; }
            set_dart(t);
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bG, G, sizeof(int) * (size_t)ND);
                    memcpy(bL, LAB, sizeof(int) * (size_t)ND);
                }
            } else {
                G[t] = old;
                set_dart(t);
            }
        } else {
            /* label swap move (keeps each label used d times) */
            int t1 = rndint(ND), t2 = rndint(ND);
            if (LAB[t1] == LAB[t2]) continue;
            int tmp = LAB[t1];
            LAB[t1] = LAB[t2];
            LAB[t2] = tmp;
            if (!dup_free()) {
                tmp = LAB[t1]; LAB[t1] = LAB[t2]; LAB[t2] = tmp;
                continue;
            }
            rebuild_lb();
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bG, G, sizeof(int) * (size_t)ND);
                    memcpy(bL, LAB, sizeof(int) * (size_t)ND);
                }
            } else {
                tmp = LAB[t1]; LAB[t1] = LAB[t2]; LAB[t2] = tmp;
                rebuild_lb();
            }
        }
    }
    if (bestc != 0) return 0;
    memcpy(G, bG, sizeof(int) * (size_t)ND);
    memcpy(LAB, bL, sizeof(int) * (size_t)ND);
    for (int t = 0; t < ND; t++) set_dart(t);
    rebuild_lb();
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long lo = (long)(0.65 * (double)ref);
    long hi = (long)(1.08 * (double)ref);
    if (hi > moore) hi = moore;
    if (hi > MAXV) hi = MAXV;

    ncand = 0;
    for (int bb = 1; bb <= MAXB; bb++) {
        long step = 2L * bb;
        long nlo = (lo + step - 1) / step;
        long nhi = hi / step;
        if (nhi > MAXN) nhi = MAXN;
        if (nlo < 3) nlo = 3;
        for (long nv = nlo; nv <= nhi; nv++) gen_for_order((int)nv, bb, lo, hi);
    }
    if (ncand > 0) qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);

    int have = 0;
    Cand bestC;
    memset(&bestC, 0, sizeof bestC);
    static int bestG[MAXDARTS], bestL[MAXDARTS];
    long bestV = 0;

    /* Ladder: pick the candidate above the current best with the fewest attempts (lowest V on ties). */
    for (;;) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        int pick = -1;
        for (int i = 0; i < ncand; i++) {
            if (cands[i].V <= bestV) continue;
            if (pick < 0 || cands[i].attempts < cands[pick].attempts) pick = i;
        }
        if (pick < 0) break;
        Cand *c = &cands[pick];
        c->attempts++;
        if (!apply_cand(c) || N != c->N) continue;
        NB = c->b;
        ND = NB * d;
        BN = NB * N;
        VT = 2 * BN;
        if (VT > MAXV || (long)VT != c->V) continue;
        double slice = usable * 0.05;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (climb(now() + slice)) {
            have = 1;
            bestV = VT;
            bestC = *c;
            memcpy(bestG, G, sizeof(int) * (size_t)ND);
            memcpy(bestL, LAB, sizeof(int) * (size_t)ND);
        }
    }

    if (!have || !apply_cand(&bestC) || N != bestC.N) { print_complete(); return 0; }
    NB = bestC.b;
    ND = NB * d;
    BN = NB * N;
    VT = 2 * BN;
    memcpy(G, bestG, sizeof(int) * (size_t)ND);
    memcpy(LAB, bestL, sizeof(int) * (size_t)ND);
    for (int t = 0; t < ND; t++) set_dart(t);
    rebuild_lb();
    if (cost_now() != 0 || !dup_free()) { print_complete(); return 0; }

    printf("%d %d\n", VT, ND * N);
    for (int i = 0; i < NB; i++)
        for (int x = 0; x < N; x++)
            for (int kk = 0; kk < d; kk++) {
                int t = i * d + kk;
                printf("%d %d\n", i * N + x, BN + LAB[t] * N + Rr[t][x]);
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
