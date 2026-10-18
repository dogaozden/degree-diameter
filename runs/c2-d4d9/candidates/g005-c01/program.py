"""Program: voltage lifts of small bipartite base graphs over non-abelian groups.

Construction (new in this version):
  * Pick a group G of order N (SL(2,q)/PSL(2,q) or metacyclic Z_m x| Z_k) and a
    base size P. Vertices are A(i,x) and B(j,y) for i,j < P and x,y in G.
  * The base is a random P x P bipartite multigraph with all row and column sums d
    (a sum of d random permutation matrices). Each base dart (i,j) carries a voltage
    g in G, and the lift joins A(i,x) to B(j, x*g). Darts sharing the same (i,j) use
    distinct voltages, so the graph is simple, bipartite and d-regular on 2*P*N vertices.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from
    every A(i,e) and every B(j,e) reaches all 2*P*N vertices within D steps.
  * Hill-climbing changes one voltage at a time. Restarts draw a fresh base and voltages.
  * P = 1 with SL(2,13) is the bi-Cayley graph of order 4368 that the previous version
    reached. It runs first as a guaranteed floor. Then candidates with more vertices than
    the floor are tried in increasing order. Matrix groups come before metacyclic groups,
    since non-abelian voltage groups are the strongest known source of records.

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
#define MAXP 8
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 60000
#define IDXM_CAP 100000
#define STALL 3000

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
static int pw_tmp[MAXN];
static int qg, psl_g;
static int gmat[MAXN][4];
static int idxm[IDXM_CAP];

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
    pw_tmp[0] = 1 % m;
    for (int b = 1; b < k; b++) pw_tmp[b] = (int)((long)pw_tmp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw_tmp[b] * c) % m;
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
    int na = (q - a) % q, nb = (q - b) % q, nc2 = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc2) * q + ne;
    return k < kn ? k : kn;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > IDXM_CAP) return 0;
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
    int q, psl, m, k, r, N, P, tier;
    long V;        /* total vertices = 2 * P * N */
} Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->tier != y->tier) return x->tier - y->tier;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
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
                if (o > MAXN || V <= lowV || V > hiV || V > MOORE) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.P = Pp;
                c.V = V;
                c.tier = 0;
                push_cand(&c);
            }
        }
    }
    for (long Nv = 3; Nv <= MAXN && 2L * Nv <= hiV; Nv++) {
        for (long k = 2; k <= Nv / 3; k++) {
            if (Nv % k) continue;
            long m = Nv / k;
            if (m < 3) continue;
            int got = 0;
            for (long r = 2; r < m && r < 300 && got < 2; r++) {
                if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
                for (int Pp = 1; Pp <= MAXP; Pp++) {
                    long V = 2L * Pp * Nv;
                    if (V <= lowV || V > hiV || V > MOORE) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.m = (int)m;
                    c.k = (int)k;
                    c.r = (int)r;
                    c.N = (int)Nv;
                    c.P = Pp;
                    c.V = V;
                    c.tier = 1;
                    push_cand(&c);
                }
                got++;
            }
        }
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

/* Build the group for a candidate and set N, P, half. */
static int P = 1, half = 1, nd = 0;

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok || N != c->N) return 0;
    P = c->P;
    half = P * N;
    return 1;
}

/* ------------------------------------------------------------------ voltage lift */

static int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXN];   /* FW[t][x] = x * g_t        (A side -> B side) */
static int BW[MAXDART][MAXN];   /* BW[t][y] = y * g_t^{-1}   (B side -> A side) */

static void set_dart(int t) {
    int g = vol[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        FW[t][x] = (int)T[(size_t)x * N + g];
        BW[t][x] = (int)T[(size_t)x * N + gi];
    }
}

static void build_lists(void) {
    int ca[MAXP], cb[MAXP];
    memset(ca, 0, sizeof ca);
    memset(cb, 0, sizeof cb);
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t];
        dA[i][ca[i]++] = t;
        dB[j][cb[j]++] = t;
    }
}

/* True if dart t with voltage g clashes with an earlier dart s < upto on the same (i,j). */
static int conflict(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

static int gen_base(void) {
    int M[MAXP][MAXP];
    int perm[MAXP];
    memset(M, 0, sizeof M);
    for (int c = 0; c < d; c++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) M[i][perm[i]]++;
    }
    nd = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++) {
            if (M[i][j] > N) return 0;
            for (int c = 0; c < M[i][j]; c++) {
                dI[nd] = i;
                dJ[nd] = j;
                nd++;
            }
        }
    build_lists();
    for (int t = 0; t < nd; t++) {
        int g, tries = 0;
        do {
            g = rndint(N);
            tries++;
        } while (conflict(t, g, t) && tries < 100000);
        if (tries >= 100000) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
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

static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        c += (long)(2 * half - ball(i * N + e_id, D));
    for (int j = 0; j < P; j++)
        c += (long)(2 * half - ball(half + j * N + e_id, D));
    return c;
}

/* ------------------------------------------------------------------ search */

static int climb(double until) {
    if (!gen_base()) return 0;
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            if (!gen_base()) return 0;
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int t = rndint(nd);
        int old = vol[t];
        int g = rndint(N);
        if (g == old || conflict(t, g, nd)) { stall++; continue; }
        vol[t] = g;
        set_dart(t);
        long nc2 = cost_now();
        if (nc2 <= cur || rnd01() < 0.01) {
            cur = nc2;
        } else {
            vol[t] = old;
            set_dart(t);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ snapshot / output */

static int sP, sN, snd;
static int sdI[MAXDART], sdJ[MAXDART], svol[MAXDART];

static void snapshot(void) {
    sP = P;
    sN = N;
    snd = nd;
    memcpy(sdI, dI, sizeof(int) * (size_t)nd);
    memcpy(sdJ, dJ, sizeof(int) * (size_t)nd);
    memcpy(svol, vol, sizeof(int) * (size_t)nd);
}

/* Requires the group of the snapshot candidate to be the current group. */
static int restore(void) {
    if (N != sN) return 0;
    P = sP;
    half = P * N;
    nd = snd;
    memcpy(dI, sdI, sizeof(int) * (size_t)nd);
    memcpy(dJ, sdJ, sizeof(int) * (size_t)nd);
    memcpy(vol, svol, sizeof(int) * (size_t)nd);
    build_lists();
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

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

    long lowV, hiV;
    if (ref <= 0) {
        lowV = 2L * d;
        hiV = MOORE;
    } else {
        lowV = (long)(0.87 * (double)ref);
        if (lowV < 2L * d) lowV = 2L * d;
        hiV = (long)(1.25 * (double)ref);
        if (hiV > MOORE) hiV = MOORE;
    }
    gen_candidates(lowV, hiV);

    double budget0 = t_end - now();
    int have = 0;
    long bestV = 0;
    Cand best;
    memset(&best, 0, sizeof best);

    /* Floor: SL(2,13) with one base vertex (bi-Cayley, 4368 vertices for d = 4). */
    Cand fb;
    memset(&fb, 0, sizeof fb);
    fb.type = 1;
    fb.q = 13;
    fb.psl = 0;
    fb.N = 2184;
    fb.P = 1;
    fb.V = 2L * 2184;
    if (fb.V <= MOORE && apply_cand(&fb)) {
        double rem = t_end - now();
        double slice = budget0 * 0.25;
        if (slice > rem) slice = rem;
        if (slice > 0.0 && climb(now() + slice)) {
            have = 1;
            bestV = fb.V;
            best = fb;
            snapshot();
        }
    }

    /* Ladder: matrix-group lifts first, then metacyclic, each in increasing order. */
    for (int i = 0; i < nc; i++) {
        if (t_end - now() < 0.3) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV) continue;
        if (c->type == 1 && c->q == 13 && c->psl == 0 && c->P == 1) continue;
        if (!apply_cand(c)) continue;
        double rem = t_end - now();
        double slice = budget0 * 0.05;
        if (slice > rem) slice = rem;
        if (slice <= 0.0) break;
        if (climb(now() + slice)) {
            have = 1;
            bestV = c->V;
            best = *c;
            snapshot();
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best) || !restore()) { print_complete(); return 0; }
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
