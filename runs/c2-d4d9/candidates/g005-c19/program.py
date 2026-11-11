"""Program: bi-Cayley search over metacyclic groups and PSL/SL(2,q), with a successive-halving race.

New routine (this version):
  * Race over candidate groups instead of giving each one a fixed slice. Every candidate gets a short
    simulated-annealing run on its connection set. The better half, ranked by residual unreached
    pairs per vertex, gets double the time in the next round. Candidates are resumable: each keeps
    its best connection set, so a later round continues from it.
  * Annealing accepts worsening moves with a temperature that scales with the current cost, and
    restarts from random when it stalls.

Construction:
  * Group G of order N (full multiplication table, N <= 3200).
  * Bi-Cayley graph: A_x is joined to B_{x*s_k} for k < d. The result is d-regular, bipartite, and has
    2N vertices. Left multiplication is an automorphism, so the diameter is <= D iff BFS from A_e and
    from B_e reaches all 2N vertices within D steps.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with lib.is_valid
and keeps the best valid graph, falling back to the known start or K_{d,d}.
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
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 48
#define STALL_LIMIT 30000

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
static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y */
static int INV[MAXN];

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

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int idxm[160000];

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
    if (ks > 160000) return 0;
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
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    int hasS, solved;
    long bestCost;
    int bestS[MAXDEG];
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_cand(int type, int q, int psl, int m, int k, int r, int Nval) {
    if (ncand >= MAXCAND) return;
    Cand *c = &cands[ncand++];
    memset(c, 0, sizeof *c);
    c->type = type;
    c->q = q;
    c->psl = psl;
    c->m = m;
    c->k = k;
    c->r = r;
    c->N = Nval;
    c->bestCost = 1L << 40;
}

/* Adds up to two metacyclic groups of order Nval. */
static void gen_meta(int Nval) {
    int added = 0;
    for (int k = 2; k <= Nval / 3 && added < 2 && ncand < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        for (int r = 2; r < m && added < 2 && ncand < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            add_cand(0, 0, 0, m, k, r, Nval);
            added++;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

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

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
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

/* ------------------------------------------------------------------ annealing */

static int load_state(const Cand *c) {
    if (!apply_cand(c)) return 0;
    if (c->hasS) {
        memcpy(S, c->bestS, sizeof(int) * (size_t)d);
        for (int k = 0; k < d; k++) set_col(k);
    } else {
        randomize_S();
    }
    return 1;
}

/* Resumes simulated annealing on candidate c until time `until`, keeping its best state. */
static void anneal(Cand *c, double until) {
    if (!load_state(c)) { c->bestCost = 1L << 40; return; }
    c->N = N;
    long cur = cost_now();
    long best = cur;
    int bS[MAXDEG];
    memcpy(bS, S, sizeof(int) * (size_t)d);
    long stall = 0;
    while (cur > 0 && now() < until) {
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0) {
            cur = nc;
        } else {
            double temp = 0.3 + 0.03 * (double)cur;
            if (rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                S[k] = old;
                set_col(k);
            }
        }
        if (cur < best) {
            best = cur;
            memcpy(bS, S, sizeof(int) * (size_t)d);
            stall = 0;
        } else if (++stall > STALL_LIMIT) {
            randomize_S();
            cur = cost_now();
            stall = 0;
        }
    }
    if (!c->hasS || best < c->bestCost) {
        c->bestCost = best;
        c->hasS = 1;
        memcpy(c->bestS, bS, sizeof(int) * (size_t)d);
    }
    if (best == 0) c->solved = 1;
}

static double score_of(int i) {
    if (cands[i].bestCost >= (1L << 40)) return 1e18;
    return (double)cands[i].bestCost / (2.0 * (double)cands[i].N);
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
    double usable = limit - 2.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long recHalf = ref / 2;
    long lowN = (long)(0.87 * (double)recHalf);
    long hiN = (long)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = moore / 2;
    if (lowN < d + 1) lowN = d + 1;
    long recN = recHalf + 1;

    /* 1. matrix groups in the window */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            add_cand(1, (int)q, psl, 0, 0, 0, (int)o);
        }
    }

    /* 2. metacyclic groups above and below the record half, interleaved */
    long nh = recN, nl = recHalf;
    while (ncand < MAXCAND && (nh <= hiN || nl >= lowN)) {
        if (nh <= hiN) { gen_meta((int)nh); nh++; }
        if (nl >= lowN && ncand < MAXCAND) { gen_meta((int)nl); nl--; }
    }

    if (ncand == 0) { print_complete(); return 0; }

    /* 3. successive halving race */
    double U = t_end - now();
    if (U > 0.3) {
        double slice = U / (4.0 * (double)ncand);
        if (slice < 0.05) slice = 0.05;
        static int active[MAXCAND];
        int nact = 0;
        for (int i = 0; i < ncand; i++) active[nact++] = i;

        while (nact > 0 && now() < t_end - 0.05) {
            for (int a = 0; a < nact; a++) {
                if (now() >= t_end - 0.05) break;
                int i = active[a];
                double until = now() + slice;
                if (until > t_end) until = t_end;
                anneal(&cands[i], until);
            }
            /* drop solved candidates, rank the rest by normalized residual cost */
            int w = 0;
            for (int a = 0; a < nact; a++)
                if (!cands[active[a]].solved) active[w++] = active[a];
            nact = w;
            for (int a = 1; a < nact; a++) {
                int v = active[a];
                double sv = score_of(v);
                int b = a - 1;
                while (b >= 0 && score_of(active[b]) > sv) {
                    active[b + 1] = active[b];
                    b--;
                }
                active[b + 1] = v;
            }
            nact = (nact + 1) / 2;   /* keep the better half */
            slice *= 2.0;
        }
    }

    /* 4. output the largest solved group */
    int bi = -1;
    for (int i = 0; i < ncand; i++)
        if (cands[i].solved && (bi < 0 || cands[i].N > cands[bi].N)) bi = i;
    if (bi < 0) { print_complete(); return 0; }

    if (!load_state(&cands[bi])) { print_complete(); return 0; }
    memcpy(S, cands[bi].bestS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
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
