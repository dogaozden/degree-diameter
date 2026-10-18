"""Program: voltage lifts of small bipartite base multigraphs over metacyclic groups.

Construction (new in this version):
  * Base graph: B vertices on each side (B = 1..4), with a multiplicity matrix M whose row and
    column sums are d. The matrix is random and must be connected. Parallel darts between the
    same pair of base vertices get distinct group voltages, so the lift is simple.
  * Lift over a group G of order N: vertex (A_i, x) is joined to (B_j, x*g) for each dart
    (i, j, g). The lift has 2*B*N vertices, is d-regular and bipartite, and has D-diameter
    checks done from the 2B base sources (A_i, e) and (B_j, e). Left multiplication is an
    automorphism, so these sources suffice.
  * Search: simulated annealing over the dart voltages. The cost is the number of vertices not
    reached within D from the 2B sources. Candidates are (pattern, group) pairs with 2*B*N
    above the reference. Iterative-deepening rounds give each candidate a slice that doubles
    per round.
  * Guard: B = 1 is the bi-Cayley graph from the parent (one dart class, group order ref/2),
    so the reference size is still reachable.

Safety: the C engine prints K_{d,d} if nothing valid is found. Python checks the output with
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
#define MAXB 4
#define MAXDEG 8
#define MAXD (MAXB * MAXDEG)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 48
#define MAXPAT 8

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
static int *INV = NULL;

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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d).
   k = 1 gives the cyclic group Z_m. */
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

/* ------------------------------------------------------------------ lift state */

static int B = 0;                       /* base size per side */
static int Mtx[MAXB][MAXB];             /* multiplicity matrix, row/col sums = d */
static int nd = 0;                      /* number of darts = B*d */
static int dA[MAXD], dB[MAXD], dg[MAXD];
static int adjA[MAXB][MAXDEG], adjB[MAXB][MAXDEG];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];

static void setup_darts(void) {
    nd = 0;
    int ca[MAXB], cb[MAXB];
    for (int i = 0; i < MAXB; i++) { ca[i] = 0; cb[i] = 0; }
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int c = 0; c < Mtx[i][j]; c++) {
                dA[nd] = i;
                dB[nd] = j;
                adjA[i][ca[i]++] = nd;
                adjB[j][cb[j]++] = nd;
                nd++;
            }
}

static void set_dart(int t) {
    int g = dg[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        fwd[t][x] = (int)T[(size_t)x * N + g];
        bwd[t][x] = (int)T[(size_t)x * N + gi];
    }
}

/* Voltage v is allowed for dart t if no other dart in the same block has it. Unassigned = -1. */
static int dart_ok(int t, int v) {
    for (int s = 0; s < nd; s++)
        if (s != t && dA[s] == dA[t] && dB[s] == dB[t] && dg[s] == v) return 0;
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
    int bN = B * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < bN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = adjA[i][k];
                    int u = bN + dB[t] * N + fwd[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - bN;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = adjB[j][k];
                    int u = dA[t] * N + bwd[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertices not reached within D from the 2B base sources (0 = valid). */
static long cost_now(void) {
    int V = 2 * B * N;
    int bN = B * N;
    long c = 0;
    for (int i = 0; i < B; i++) c += (long)(V - ball(i * N + e_id, D));
    for (int j = 0; j < B; j++) c += (long)(V - ball(bN + j * N + e_id, D));
    return c;
}

static void random_voltages(void) {
    for (int t = 0; t < nd; t++) dg[t] = -1;
    for (int t = 0; t < nd; t++) {
        int v;
        do v = rndint(N); while (!dart_ok(t, v));
        dg[t] = v;
    }
}

static int gbest[MAXD];

/* Simulated annealing over dart voltages with sawtooth reheating. 1 = valid found (gbest set). */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    random_voltages();
    for (int t = 0; t < nd; t++) set_dart(t);
    long cur = cost_now();
    long bestc = cur;
    memcpy(gbest, dg, sizeof(int) * (size_t)nd);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double tn = now();
            if (tn >= until) break;
            double f = (tn - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int t = rndint(nd);
        int old = dg[t];
        int v;
        do v = rndint(N); while (v == old || !dart_ok(t, v));
        dg[t] = v;
        set_dart(t);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(gbest, dg, sizeof(int) * (size_t)nd);
            }
        } else {
            dg[t] = old;
            set_dart(t);
        }
    }
    if (bestc != 0) return 0;
    memcpy(dg, gbest, sizeof(int) * (size_t)nd);
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int b;
    int M[MAXB][MAXB];
    int m, k, r;
    int N;
    int w;
} Cand;

static int apply_cand(const Cand *c) {
    B = c->b;
    memcpy(Mtx, c->M, sizeof Mtx);
    if (!build_meta(c->m, c->k, c->r)) return 0;
    setup_darts();
    return 1;
}

/* Metacyclic groups of order Nv: one r per k, up to maxg groups. */
static int groups_for(int Nv, int *gm, int *gk, int *gr, int maxg) {
    int cnt = 0;
    for (int k = 2; k <= Nv / 3 && cnt < maxg; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            gm[cnt] = m;
            gk[cnt] = k;
            gr[cnt] = r;
            cnt++;
            break;
        }
    }
    return cnt;
}

static int find_root(int *par, int x) {
    while (par[x] != x) {
        par[x] = par[par[x]];
        x = par[x];
    }
    return x;
}

static int connected_pat(int b, int M[MAXB][MAXB]) {
    int par[2 * MAXB];
    for (int i = 0; i < 2 * b; i++) par[i] = i;
    for (int i = 0; i < b; i++)
        for (int j = 0; j < b; j++)
            if (M[i][j] > 0) {
                int a = find_root(par, i);
                int c = find_root(par, b + j);
                par[a] = c;
            }
    int r = find_root(par, 0);
    for (int i = 1; i < 2 * b; i++)
        if (find_root(par, i) != r) return 0;
    return 1;
}

static int pat_n[MAXB + 1];
static int pat_M[MAXB + 1][MAXPAT][MAXB][MAXB];

/* Random connected multiplicity matrices: sum of d random permutation matrices. */
static void gen_patterns(int b, int want) {
    pat_n[b] = 0;
    for (int tries = 0; tries < 400 && pat_n[b] < want; tries++) {
        int M[MAXB][MAXB];
        memset(M, 0, sizeof M);
        for (int l = 0; l < d; l++) {
            int p[MAXB];
            for (int i = 0; i < b; i++) p[i] = i;
            for (int i = b - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = p[i];
                p[i] = p[j];
                p[j] = tmp;
            }
            for (int i = 0; i < b; i++) M[i][p[i]]++;
        }
        if (!connected_pat(b, M)) continue;
        int dup = 0;
        for (int q = 0; q < pat_n[b]; q++)
            if (memcmp(pat_M[b][q], M, sizeof M) == 0) { dup = 1; break; }
        if (dup) continue;
        memcpy(pat_M[b][pat_n[b]], M, sizeof M);
        pat_n[b]++;
    }
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

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (ref <= 0) ref = moore / 4;
    if (ref < 1) ref = 1;

    static Cand cands[MAXCAND];
    int nc = 0, wsum = 0;

    for (int b = 1; b <= MAXB; b++) {
        int npat;
        if (b == 1) {
            npat = 1;
            pat_n[1] = 1;
            memset(pat_M[1][0], 0, sizeof pat_M[1][0]);
            pat_M[1][0][0][0] = d;
        } else {
            gen_patterns(b, 2);
            npat = pat_n[b];
        }
        for (int pi = 0; pi < npat; pi++) {
            for (int s = 0; s < 2; s++) {
                int guard = (b == 1 && s == 0);
                long Nv;
                int w;
                if (b == 1) {
                    Nv = ref / 2 + s;          /* bi-Cayley guard, then just above */
                    w = guard ? 2 : 1;
                } else {
                    Nv = ref / (2 * b) + 1 + s; /* 2*b*Nv just above the reference */
                    w = 1;
                }
                if (Nv < 3 || Nv > MAXN || 2L * b * Nv > moore) continue;
                int gm[4], gk[4], gr[4];
                int ng = groups_for((int)Nv, gm, gk, gr, guard ? 2 : 1);
                for (int g = 0; g < ng && nc < MAXCAND; g++) {
                    Cand *c = &cands[nc++];
                    c->b = b;
                    memcpy(c->M, pat_M[b][pi], sizeof c->M);
                    c->m = gm[g];
                    c->k = gk[g];
                    c->r = gr[g];
                    c->N = (int)Nv;
                    c->w = w;
                    wsum += w;
                }
                if ((ng == 0 || guard) && nc < MAXCAND) {
                    Cand *c = &cands[nc++];
                    c->b = b;
                    memcpy(c->M, pat_M[b][pi], sizeof c->M);
                    c->m = (int)Nv;
                    c->k = 1;
                    c->r = 1;
                    c->N = (int)Nv;
                    c->w = w;
                    wsum += w;
                }
            }
        }
    }

    if (nc == 0 || wsum <= 0) { print_complete(); return 0; }

    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    long bestV = 0;
    double base = usable * 0.7 / (double)wsum;
    if (base < 0.2) base = 0.2;

    /* Iterative deepening: each round gives every candidate still able to improve a slice
       scaled by its weight, and the slice doubles per round. */
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < nc; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[i];
            long V = 2L * c->b * c->N;
            if (V <= bestV) continue;
            if (V > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base * (double)c->w * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV = V;
                best = *c;
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(dg, gbest, sizeof(int) * (size_t)nd);
    for (int t = 0; t < nd; t++) set_dart(t);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * B * N, (long)nd * N);
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", dA[t] * N + x, B * N + dB[t] * N + fwd[t][x]);
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
        return best   # already optimal; no search needed
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
