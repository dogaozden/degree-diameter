"""Program: bi-Cayley search over SL(2,q), PSL(2,q) and metacyclic groups.

Construction: a bi-Cayley graph on A_x, B_y (x, y in G) with A_x ~ B_{x s_k}, k < d.
It is d-regular and bipartite with 2|G| vertices. Left multiplication is an automorphism,
so diameter <= D iff BFS from A_e and from B_e reaches everything within D steps.

New in this version:
  * Lazy group arithmetic. The C engine never builds an |G|^2 multiplication table. It
    multiplies elements with closed formulas (metacyclic) or 2x2 matrix products with a
    canonical-key lookup (SL/PSL). Building a group is O(|G|), not O(|G|^2).
  * Normalisation s_0 = e. Relabelling B by right multiplication by s_0 gives an isomorphic
    graph, so only s_1..s_{d-1} are searched. This cuts the search space by a factor |G|.
  * Successive halving over candidate groups. A random pool of (group, r) candidates in the
    target window gets short annealing slices. Survivors are ranked by normalised residual
    (unreached pairs / 2|G|), the better half continues with doubled slices, and each
    candidate warm-starts from its own best set. Any success raises the order bar.

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
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define QMAX 19
#define MAXCAND 8000
#define MAXPOOL 48
#define BIGCOST (1L << 60)

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

typedef struct {
    int type;          /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    long bestcost;
    double score;
    int hasS;
    int S[MAXDEG];     /* best connection set found so far, S[0] = identity */
} Cand;

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

/* ------------------------------------------------------------------ group (lazy arithmetic) */

static int N = 0, e_id = 0;               /* current group order and identity index */
static int G_type = 0, G_m = 0, G_k = 0, G_r = 0, G_q = 0, G_psl = 0;
static int pwr[MAXN];                     /* metacyclic: r^b mod m */
static int gm[MAXN][4];                   /* matrix: entries a,b,c,e of element i */
static int idxm[QMAX * QMAX * QMAX * QMAX];

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int set_meta(int m, int k, int r) {
    if (m < 2 || k < 1 || m * k > MAXN) return 0;
    G_type = 0; G_m = m; G_k = k; G_r = r;
    pwr[0] = 1 % m;
    for (int b = 1; b < k; b++) pwr[b] = (int)((long)pwr[b - 1] * r % m);
    N = m * k;
    e_id = 0;
    return 1;
}

static int mat_key(int q, int a, int b, int c, int e) {
    int key = ((a * q + b) * q + c) * q + e;
    if (!G_psl) return key;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return key < kn ? key : kn;
}

/* SL(2,q) or PSL(2,q), q prime. Enumerates elements and indexes canonical keys. */
static int set_matrix(int q, int psl) {
    if (q < 2 || q > QMAX) return 0;
    G_type = 1; G_q = q; G_psl = psl;
    int ks = q * q * q * q;
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int ee = 0; ee < q; ee++) {
                    if ((((a * ee - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + ee;
                    if (mat_key(q, a, b, c, ee) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gm[cnt][0] = a; gm[cnt][1] = b; gm[cnt][2] = c; gm[cnt][3] = ee;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    e_id = idxm[mat_key(q, 1 % q, 0, 0, 1 % q)];
    return cnt > 0 ? 1 : 0;
}

static int g_mul(int x, int y) {
    if (G_type == 0) {
        int k = G_k, m = G_m;
        int a = x / k, b = x - a * k;
        int c = y / k, dd = y - c * k;
        int aa = (int)(((long)a + (long)pwr[b] * c) % m);
        int bb = b + dd;
        if (bb >= k) bb -= k;
        return aa * k + bb;
    } else {
        int q = G_q;
        const int *X = gm[x];
        const int *Y = gm[y];
        int a = X[0], b = X[1], c = X[2], e = X[3];
        int a2 = Y[0], b2 = Y[1], c2 = Y[2], e2 = Y[3];
        int pa = (a * a2 + b * c2) % q;
        int pb = (a * b2 + b * e2) % q;
        int pc = (c * a2 + e * c2) % q;
        int pe = (c * b2 + e * e2) % q;
        return idxm[mat_key(q, pa, pb, pc, pe)];
    }
}

static int g_inv(int x) {
    if (G_type == 0) {
        int k = G_k, m = G_m;
        int a = x / k, b = x - a * k;
        int nb = (k - b) % k;
        long t = ((long)pwr[nb] * a) % m;
        int na = (int)((m - t) % m);
        return na * k + nb;
    } else {
        int q = G_q;
        const int *X = gm[x];
        int a = X[0], b = X[1], c = X[2], e = X[3];
        return idxm[mat_key(q, e % q, (q - b) % q, (q - c) % q, a % q)];
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Sinv[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */
static int saveR[MAXN], saveI[MAXN];

static int in_S(int x, int cnt) {
    for (int k = 0; k < cnt; k++)
        if (S[k] == x) return 1;
    return 0;
}

static void set_col(int k) {
    int s = S[k], si = Sinv[k];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = g_mul(x, s);
        Ri[k][x] = g_mul(x, si);
    }
}

static void load_inv_cols(void) {
    for (int k = 0; k < d; k++) Sinv[k] = g_inv(S[k]);
    for (int k = 0; k < d; k++) set_col(k);
}

/* S[0] is always the identity (WLOG by relabelling B). */
static void load_S(const int *src) {
    for (int k = 0; k < d; k++) S[k] = src[k];
    S[0] = e_id;
    load_inv_cols();
}

static void random_S(void) {
    S[0] = e_id;
    for (int k = 1; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    load_inv_cols();
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

/* Number of vertices not reached within D from A_e and from B_e (0 = valid). */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

/* ------------------------------------------------------------------ annealing */

/* Anneals from the currently loaded S. Writes the best S into c->S, returns its cost. */
static long anneal(double until, Cand *c) {
    long cur = cost_now();
    long bestc = cur;
    memcpy(c->S, S, sizeof(int) * (size_t)d);
    if (cur == 0) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return bestc;
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int k = 1 + rndint(d - 1);
        int old = S[k], oldinv = Sinv[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        memcpy(saveR, Rr[k], sizeof(int) * (size_t)N);
        memcpy(saveI, Ri[k], sizeof(int) * (size_t)N);
        S[k] = x;
        Sinv[k] = g_inv(x);
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(c->S, S, sizeof(int) * (size_t)d);
            }
        } else {
            S[k] = old;
            Sinv[k] = oldinv;
            memcpy(Rr[k], saveR, sizeof(int) * (size_t)N);
            memcpy(Ri[k], saveI, sizeof(int) * (size_t)N);
        }
    }
    return bestc;
}

/* ------------------------------------------------------------------ candidates */

static Cand allc[MAXCAND];
static int nall = 0;

static void add_cand(int type, int q, int psl, int m, int k, int r, int Nv) {
    if (nall >= MAXCAND) return;
    Cand *c = &allc[nall++];
    memset(c, 0, sizeof *c);
    c->type = type;
    c->q = q;
    c->psl = psl;
    c->m = m;
    c->k = k;
    c->r = r;
    c->N = Nv;
}

static void gen_candidates(int lowN, int hiN) {
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    nall = 0;
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o >= lowN && o <= hiN) add_cand(1, (int)q, psl, 0, 0, 0, (int)o);
        }
    }
    for (int Nv = lowN; Nv <= hiN; Nv++) {
        for (int k = 2; k <= Nv / 3; k++) {
            if (Nv % k) continue;
            int m = Nv / k;               /* m >= 3 */
            int got = 0;
            for (int r = m - 1; r >= 2 && got < 2; r--) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1) continue;
                add_cand(0, 0, 0, m, k, r, Nv);
                got++;
            }
        }
    }
}

static int set_group_cand(const Cand *c) {
    int ok;
    if (c->type == 0) ok = set_meta(c->m, c->k, c->r);
    else ok = set_matrix(c->q, c->psl);
    return ok && N > d + 1 && N <= MAXN;
}

static Cand pool[MAXPOOL];
static int alive[MAXPOOL];
static int np = 0;

static void make_pool(int bestN, int hiN) {
    static int idx[MAXCAND];
    int ne = 0;
    for (int i = 0; i < nall; i++)
        if (allc[i].N > bestN && allc[i].N <= hiN) idx[ne++] = i;
    np = ne < MAXPOOL ? ne : MAXPOOL;
    for (int j = 0; j < np; j++) {
        int r = j + rndint(ne - j);
        int t = idx[j]; idx[j] = idx[r]; idx[r] = t;
        pool[j] = allc[idx[j]];
        pool[j].bestcost = BIGCOST;
        pool[j].score = 1e300;
        pool[j].hasS = 0;
        alive[j] = 1;
    }
}

/* ------------------------------------------------------------------ search */

static Cand best;
static int have = 0;
static int bestN = 0;

static void search(int lowN, int hiN) {
    gen_candidates(lowN, hiN);
    while (now() < t_end - 0.05) {
        make_pool(bestN, hiN);
        if (np == 0) break;
        int nalive = np;
        double remaining = t_end - now();
        double s0 = remaining / ((double)np * (log((double)np) / log(2.0) + 2.0));
        if (s0 < 0.01) s0 = 0.01;
        double slice = s0;
        while (nalive > 0 && now() < t_end - 0.05) {
            for (int i = 0; i < np; i++) {
                if (!alive[i]) continue;
                if (now() >= t_end - 0.05) break;
                Cand *c = &pool[i];
                if (c->N <= bestN || !set_group_cand(c)) {
                    alive[i] = 0;
                    nalive--;
                    continue;
                }
                if (c->hasS) load_S(c->S);
                else random_S();
                double until = now() + slice;
                if (until > t_end) until = t_end;
                long bc = anneal(until, c);
                c->hasS = 1;
                if (bc < c->bestcost) c->bestcost = bc;
                if (bc == 0) {
                    have = 1;
                    bestN = c->N;
                    best = *c;
                    alive[i] = 0;
                    nalive--;
                }
            }
            /* successive halving on normalised residual */
            if (nalive > 1) {
                int ord[MAXPOOL], cntA = 0;
                for (int i = 0; i < np; i++) {
                    if (!alive[i]) continue;
                    pool[i].score = (double)pool[i].bestcost / (2.0 * (double)pool[i].N);
                    ord[cntA++] = i;
                }
                for (int a = 1; a < cntA; a++) {
                    int t = ord[a];
                    int b = a - 1;
                    while (b >= 0 && pool[ord[b]].score > pool[t].score) {
                        ord[b + 1] = ord[b];
                        b--;
                    }
                    ord[b + 1] = t;
                }
                int keep = (cntA + 1) / 2;
                for (int j = keep; j < cntA; j++) {
                    alive[ord[j]] = 0;
                    nalive--;
                }
            }
            slice *= 2.0;
        }
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
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long recHalf = ref / 2;
    long lowN = (long)(0.87 * (double)recHalf);
    long hiN = (long)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = moore / 2;
    if (lowN < d + 2) lowN = d + 2;
    if (lowN < 3) lowN = 3;
    if (hiN < lowN) { print_complete(); return 0; }

    search((int)lowN, (int)hiN);

    if (!have) { print_complete(); return 0; }
    if (!set_group_cand(&best)) { print_complete(); return 0; }
    load_S(best.S);
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
