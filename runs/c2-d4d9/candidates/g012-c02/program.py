"""Program: multi-base voltage lifts over finite groups, searched by simulated annealing.

Construction (different from the bi-Cayley parent):
  * Base graph: P A-vertices and P B-vertices. A-vertex a is joined to B-vertex (a + c_j) mod P
    for each shift c_j (the c_j are distinct, so the base is simple and d-regular).
  * Voltages: each dart (a, j) carries a group element v[a][j]. The lift has vertices (u, x),
    u in 0..2P-1, x in G, with (a, x) ~ (P + a + c_j, x * v[a][j]). The lift is d-regular,
    bipartite, simple, and has 2*P*|G| vertices.
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from (u, e) reaches
    everything within D steps for each of the 2P base vertices u.
  * Groups: metacyclic Z_m x| Z_k (including cyclic), and PSL/SL(2,q). Candidates are chosen so
    that 2*P*|G| just beats the record vertex count, for P in {d, d+1}.

Search: iterative deepening over candidates (smaller orders first). Each candidate runs
simulated annealing over the voltages with sawtooth reheating. The cost is the number of
(base representative, vertex) pairs not reached within D.

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
#define MAXP 8
#define MAXD 8
#define MAXCAND 120
#define MAXS (2 * MAXP)
#define MAXV (MAXS * MAXN)
#define QMAX 17

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D, P = 0;
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

/* ------------------------------------------------------------------ group tables */

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
static int pw_tab[MAXN];
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (m < 1 || k < 1 || n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    pw_tab[0] = 1 % m;
    for (int b = 1; b < k; b++) pw_tab[b] = (int)((long)pw_tab[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw_tab[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return 1;
}

/* SL(2,q) or PSL(2,q), q prime <= QMAX. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int idxm[QMAX * QMAX * QMAX * QMAX];

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    if (q > QMAX || q < 2) return 0;
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    static int gm[MAXN][4];
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gm[cnt][0] = a;
                    gm[cnt][1] = b;
                    gm[cnt][2] = c;
                    gm[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gm[y][0], b2 = gm[y][1], c2 = gm[y][2], e2 = gm[y][3];
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
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    int p;      /* base half-size P */
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

/* Up to maxo groups of order Nv: one nonabelian metacyclic per k, a cyclic group, and matrix groups. */
static void groups_of_order(int Nv, Cand *out, int *no, int maxo) {
    for (int k = 2; k <= Nv / 3 && *no < maxo; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            out[(*no)++] = c;
            break;
        }
    }
    if (*no < maxo) {
        Cand c;
        memset(&c, 0, sizeof c);
        c.type = 0;
        c.m = Nv;
        c.k = 1;
        c.r = 1;
        c.N = Nv;
        out[(*no)++] = c;
    }
    static const int mq[] = {5, 7, 11, 13, 17};
    for (unsigned qi = 0; qi < sizeof mq / sizeof mq[0] && *no < maxo; qi++) {
        for (int psl = 0; psl < 2 && *no < maxo; psl++) {
            long q = mq[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o == Nv && o <= MAXN) {
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = Nv;
                out[(*no)++] = c;
            }
        }
    }
}

/* ------------------------------------------------------------------ lift state */

static int V[MAXP][MAXD];    /* voltage of dart (a, j) */
static int C[MAXD];          /* shifts, distinct mod P */
static int cbV[MAXP][MAXD], cbC[MAXD];

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Vertices: index s*N + x, s < P is an A-vertex, s >= P a B-vertex. */
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
            int u = qv[head];
            int s = u / N;
            int x = u - s * N;
            if (s < P) {
                for (int j = 0; j < d; j++) {
                    int b = s + C[j];
                    if (b >= P) b -= P;
                    int w = (P + b) * N + (int)T[(size_t)x * N + V[s][j]];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            } else {
                int b = s - P;
                for (int k = 0; k < d; k++) {
                    int a = b - C[k];
                    if (a < 0) a += P;
                    int w = a * N + (int)T[(size_t)x * N + INV[V[a][k]]];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base representatives of the number of vertices not reached within D. 0 = valid. */
static long cost_now(void) {
    long total = 2L * P * N;
    long c = 0;
    for (int s = 0; s < 2 * P; s++) {
        c += total - ball(s * N + e_id, D);
    }
    return c;
}

static void randomize_state(void) {
    int perm[MAXP];
    for (int i = 0; i < P; i++) perm[i] = i;
    for (int i = P - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int j = 0; j < d; j++) C[j] = perm[j];
    for (int a = 0; a < P; a++)
        for (int j = 0; j < d; j++) V[a][j] = rndint(N);
}

/* Simulated annealing over voltages with sawtooth reheating. Returns 1 and leaves the valid
   state in V/C if one is found before `until`. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_state();
    long cur = cost_now();
    long bestc = cur;
    memcpy(cbV, V, sizeof V);
    memcpy(cbC, C, sizeof C);
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
        int a = rndint(P), j = rndint(d);
        int old = V[a][j];
        int g = rndint(N);
        if (g == old) continue;
        V[a][j] = g;
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(cbV, V, sizeof V);
                memcpy(cbC, C, sizeof C);
            }
        } else {
            V[a][j] = old;
        }
    }
    if (bestc != 0) return 0;
    memcpy(V, cbV, sizeof V);
    memcpy(C, cbC, sizeof C);
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
    long target = ref + 2;   /* need strictly more vertices than the reference */

    int pl[2], Nmin[2], Nmax[2];
    int npl = 0;
    for (int p = d; p <= d + 1 && p <= MAXP && npl < 2; p++) {
        pl[npl] = p;
        long nmin = (target + 2L * p - 1) / (2L * p);
        long spread = nmin / 8;
        if (spread < 16) spread = 16;
        long nmax = nmin + spread;
        if (nmax > MAXN) nmax = MAXN;
        Nmin[npl] = (int)nmin;
        Nmax[npl] = (int)nmax;
        npl++;
    }
    int Nlo = MAXN + 1, Nhi = 0;
    for (int pi = 0; pi < npl; pi++) {
        if (Nmin[pi] < Nlo) Nlo = Nmin[pi];
        if (Nmax[pi] > Nhi) Nhi = Nmax[pi];
    }

    static Cand cands[MAXCAND];
    int ncand = 0;
    for (int Nv = Nlo; Nv <= Nhi && ncand < MAXCAND; Nv++) {
        if (Nv < 2 || Nv > MAXN) continue;
        Cand gl[8];
        int ng = 0;
        groups_of_order(Nv, gl, &ng, 4);
        for (int pi = 0; pi < npl; pi++) {
            if (Nv < Nmin[pi] || Nv > Nmax[pi]) continue;
            int p = pl[pi];
            if (2L * p * Nv > moore) continue;
            for (int g = 0; g < ng && ncand < MAXCAND; g++) {
                cands[ncand] = gl[g];
                cands[ncand].p = p;
                ncand++;
            }
        }
    }
    if (ncand == 0) { print_complete(); return 0; }

    static int bV[MAXP][MAXD];
    static int bC[MAXD];
    long bestVerts = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    int have = 0;

    /* Iterative deepening: each round gives every still-improving candidate a slice that
       doubles per round. Candidates must beat the best vertex count found so far. */
    double budget0 = t_end - now();
    double base = budget0 * 0.5 / (double)ncand;
    if (base < 0.2) base = 0.2;
    for (int round = 0; round < 10; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[i];
            long nv = 2L * c->p * c->N;
            if (nv <= bestVerts) continue;
            if (nv > moore) continue;
            P = c->p;
            if (!apply_cand(c)) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestVerts = nv;
                best = *c;
                memcpy(bV, V, sizeof V);
                memcpy(bC, C, sizeof C);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    P = best.p;
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(V, bV, sizeof V);
    memcpy(C, bC, sizeof C);
    if (cost_now() != 0) { print_complete(); return 0; }

    long nverts = 2L * P * N;
    long nedges = (long)P * d * N;
    printf("%ld %ld\n", nverts, nedges);
    for (int a = 0; a < P; a++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < d; j++) {
                int u = a * N + x;
                int b = a + C[j];
                if (b >= P) b -= P;
                int w = (P + b) * N + (int)T[(size_t)x * N + V[a][j]];
                printf("%d %d\n", u, w);
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
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing larger exists
    budget = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget <= 1.0:
        return best
    ref = REF_VERTICES.get((d, D), best[0])
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                         timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
