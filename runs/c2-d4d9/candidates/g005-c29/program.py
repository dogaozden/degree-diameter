"""Program: multi-orbit voltage lifts over metacyclic groups, with successive halving.

New construction (the parent only uses one A-orbit and one B-orbit):
  * Take k A-orbits and k B-orbits, each a copy of a group G of order |G| = m*kk
    (metacyclic Z_m x|_r Z_kk, or cyclic when kk = 1).
  * Dart (t, i), for t < d and i < k, joins (i, g) to (sig_t(i), g * s_{t,i}), where
    each sig_t is a permutation of [k] and s_{t,i} is a group element.
  * Every orbit then has degree d, the graph is bipartite, and it has 2*k*|G| vertices.
    Record 4970 = 10 * 497 has exactly this shape with k = 5.
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from one
    vertex of each of the 2k orbits reaches all vertices within D steps.
  * Search: simulated annealing over voltages and permutations, with a penalty for
    duplicate darts. A pool of candidate (k, G, r) shapes near the record is run with
    successive halving: each round doubles the slice and keeps the better half by
    normalized cost. The 2-orbit matrix-group fallback (SL(2,13), 4368) runs first.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start.
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

#define MAXG 2600
#define MAXK 12
#define MAXD 8
#define MAXV 6000
#define MAXPOOL 40000
#define MAXCAND 24
#define STALL 2500

static int d, D;
static double t_end;
static int REFV;

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

/* ------------------------------------------------------------ group layer */

static int ctype = 0;                 /* 0: metacyclic formula, 1: table */
static int G = 0, e_id = 0;
static int gmm = 1, gmk = 1, gmr = 1; /* Z_gmm x| Z_gmk */
static int pwA[MAXG];
static uint16_t T[MAXG * MAXG];
static int INVT[MAXG];
static int mq = 2, mpsl = 0;
static int gmat[MAXG][4];
static int idxm[130321];

static void setup_meta(int m, int kk, int r) {
    ctype = 0;
    gmm = m;
    gmk = kk;
    gmr = r;
    G = m * kk;
    e_id = 0;
    pwA[0] = 1 % m;
    for (int b = 1; b < kk; b++) pwA[b] = (int)((long)pwA[b - 1] * r % m);
}

static int canon_key(int a, int b, int c, int e) {
    int q = mq;
    int k = ((a * q + b) * q + c) * q + e;
    if (!mpsl) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static void setup_matrix(int q, int psl) {
    mq = q;
    mpsl = psl;
    ctype = 1;
    int ks = q * q * q * q;
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXG) { G = 0; return; }
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    G = cnt;
    for (int x = 0; x < G; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < G; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * G + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    for (int x = 0; x < G; x++) {
        INVT[x] = -1;
        for (int y = 0; y < G; y++)
            if ((int)T[(size_t)x * G + y] == e_id) { INVT[x] = y; break; }
    }
}

static inline int gmul(int x, int y) {
    if (ctype == 0) {
        int a = x / gmk, b = x % gmk;
        int c = y / gmk, dd = y % gmk;
        int aa = (int)((a + (long)pwA[b] * c) % gmm);
        int bb = (b + dd) % gmk;
        return aa * gmk + bb;
    }
    return (int)T[(size_t)x * G + y];
}

static inline int ginv(int x) {
    if (ctype == 0) {
        int a = x / gmk, b = x % gmk;
        int nb = (gmk - b) % gmk;
        long na = ((long)pwA[nb] * a) % gmm;
        na = (gmm - na) % gmm;
        return (int)na * gmk + nb;
    }
    return INVT[x];
}

/* ------------------------------------------------------------ lift state */

static int K = 1, V = 0;
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], volt[MAXD][MAXK], vinv[MAXD][MAXK];
static int adj[MAXV * MAXD];
static int stampv[MAXV];
static int tickv = 0;
static int qv[MAXV];

/* Rewrite the adjacency entries touched by dart (t, i). */
static void update_dart(int t, int i) {
    int j = sig[t][i];
    int s = volt[t][i], si = vinv[t][i];
    for (int g = 0; g < G; g++)
        adj[(i * G + g) * d + t] = (K + j) * G + gmul(g, s);
    for (int h = 0; h < G; h++)
        adj[((K + j) * G + h) * d + t] = i * G + gmul(h, si);
}

static void rebuild_full(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) update_dart(t, i);
}

static void sync_inv(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) {
            vinv[t][i] = ginv(volt[t][i]);
            sinv[t][sig[t][i]] = i;
        }
}

static int ball_count(int src) {
    if (++tickv == 0x7fffffff) {
        memset(stampv, 0, sizeof stampv);
        tickv = 1;
    }
    int head = 0, tail = 0;
    stampv[src] = tickv;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int *a = adj + qv[head] * d;
            for (int t = 0; t < d; t++) {
                int u = a[t];
                if (stampv[u] != tickv) {
                    stampv[u] = tickv;
                    qv[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (sig[t1][i] == sig[t2][i] && volt[t1][i] == volt[t2][i]) c++;
    return c;
}

/* Zero iff simple, degree d, and diameter <= D. */
static long eval_cost(void) {
    long c = 0;
    for (int o = 0; o < 2 * K; o++)
        c += V - ball_count(o * G + e_id);
    c += (long)V * dup_count();
    return c;
}

static int accept(long nc, long cur) {
    if (nc <= cur) return 1;
    double temp = 0.01 * (double)V + 1.0;
    return rnd01() < exp(-(double)(nc - cur) / temp);
}

static void random_config(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) sig[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[t][i];
            sig[t][i] = sig[t][j];
            sig[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) volt[t][i] = rndint(G);
    }
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int type, k, G, m, kk, r, q, psl, V, nonab;
    int started;
    long bestc;
    int sig[MAXD][MAXK], volt[MAXD][MAXK];
    int bsig[MAXD][MAXK], bvolt[MAXD][MAXK];
} Cand;

typedef struct {
    int type, k, G, m, kk, r, q, psl, V, nonab;
} Desc;

static Cand cand[MAXCAND];
static int ncand = 0;
static Desc pool[MAXPOOL];
static int npool = 0;

static void add_desc(int type, int k, int gv, int m, int kk, int r, int q, int psl, int nonab) {
    if (npool >= MAXPOOL) return;
    Desc *x = &pool[npool++];
    x->type = type;
    x->k = k;
    x->G = gv;
    x->m = m;
    x->kk = kk;
    x->r = r;
    x->q = q;
    x->psl = psl;
    x->V = 2 * k * gv;
    x->nonab = nonab;
}

static void take(const Desc *x) {
    Cand *c = &cand[ncand++];
    memset(c, 0, sizeof *c);
    c->type = x->type;
    c->k = x->k;
    c->G = x->G;
    c->m = x->m;
    c->kk = x->kk;
    c->r = x->r;
    c->q = x->q;
    c->psl = x->psl;
    c->V = x->V;
    c->nonab = x->nonab;
    c->bestc = (long)1 << 60;
}

static int cmp_desc(const void *A, const void *B) {
    const Desc *a = A, *b = B;
    int aa = a->V > REFV, bb = b->V > REFV;
    if (aa != bb) return bb - aa;               /* above-record first */
    if (aa) {
        if (a->V != b->V) return a->V - b->V;   /* nearest above first */
        return b->nonab - a->nonab;
    }
    if (a->V != b->V) return b->V - a->V;       /* nearest below first */
    return b->nonab - a->nonab;
}

static void setup_cand(const Cand *c) {
    if (c->type == 0) setup_meta(c->m, c->kk, c->r);
    else setup_matrix(c->q, c->psl);
    K = c->k;
    V = 2 * K * G;
}

static void save_best(Cand *c, long cost) {
    c->bestc = cost;
    memcpy(c->bsig, sig, sizeof sig);
    memcpy(c->bvolt, volt, sizeof volt);
}

/* Resume the annealing of candidate c until time `until`. */
static void run_cand(Cand *c, double until) {
    setup_cand(c);
    if (!c->started) {
        random_config();
        c->started = 1;
        c->bestc = (long)1 << 60;
    } else {
        memcpy(sig, c->sig, sizeof sig);
        memcpy(volt, c->volt, sizeof volt);
    }
    sync_inv();
    rebuild_full();
    long cur = eval_cost();
    if (cur < c->bestc) save_best(c, cur);

    long stall = 0, it = 0;
    while (c->bestc > 0) {
        if ((++it & 7) == 0 && now() > until) break;
        if (stall > STALL) {
            memcpy(sig, c->bsig, sizeof sig);
            memcpy(volt, c->bvolt, sizeof volt);
            sync_inv();
            rebuild_full();
            for (int p = 0; p < 3; p++) {
                int t = rndint(d), i = rndint(K);
                volt[t][i] = rndint(G);
            }
            sync_inv();
            rebuild_full();
            cur = eval_cost();
            stall = 0;
            continue;
        }
        if (K > 1 && rnd01() < 0.3) {
            int t = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int j1 = sig[t][i1], j2 = sig[t][i2];
            sig[t][i1] = j2;
            sig[t][i2] = j1;
            sinv[t][j2] = i1;
            sinv[t][j1] = i2;
            update_dart(t, i1);
            update_dart(t, i2);
            long nc = eval_cost();
            if (accept(nc, cur)) {
                cur = nc;
            } else {
                sig[t][i1] = j1;
                sig[t][i2] = j2;
                sinv[t][j1] = i1;
                sinv[t][j2] = i2;
                update_dart(t, i1);
                update_dart(t, i2);
            }
        } else {
            int t = rndint(d), i = rndint(K);
            int old = volt[t][i], oldi = vinv[t][i];
            int g = rndint(G);
            volt[t][i] = g;
            vinv[t][i] = ginv(g);
            update_dart(t, i);
            long nc = eval_cost();
            if (accept(nc, cur)) {
                cur = nc;
            } else {
                volt[t][i] = old;
                vinv[t][i] = oldi;
                update_dart(t, i);
            }
        }
        if (cur < c->bestc) {
            save_best(c, cur);
            stall = 0;
        } else {
            stall++;
        }
    }
    memcpy(c->sig, sig, sizeof sig);
    memcpy(c->volt, volt, sizeof volt);
}

static int emit_cand(Cand *c) {
    setup_cand(c);
    memcpy(sig, c->bsig, sizeof sig);
    memcpy(volt, c->bvolt, sizeof volt);
    sync_inv();
    rebuild_full();
    if (eval_cost() != 0) return 0;
    printf("%d %ld\n", V, (long)K * d * G);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++)
            for (int g = 0; g < G; g++)
                printf("%d %d\n", i * G + g, (K + sig[t][i]) * G + gmul(g, volt[t][i]));
    return 1;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static double key_of(int ci) {
    return (double)cand[ci].bestc / (double)cand[ci].V;
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

    REFV = (int)ref;
    long moore = moore_bound();
    int lo = (int)(0.87 * (double)ref + 0.999);
    int hi = (int)(1.13 * (double)ref);
    if (hi > moore) hi = (int)moore;
    if (hi > MAXV) hi = MAXV;
    if (lo < 4) lo = 4;

    /* 1. enumerate multi-orbit lift shapes (k, G) with 2*k*|G| in [lo, hi] */
    for (int k = 1; k <= MAXK; k++) {
        int gmin = (lo + 2 * k - 1) / (2 * k);
        int gmax = hi / (2 * k);
        if (gmin < 3) gmin = 3;
        if (gmax > MAXG) gmax = MAXG;
        for (int gv = gmin; gv <= gmax; gv++) {
            for (int kk = 1; kk <= gv / 3; kk++) {
                if (gv % kk) continue;
                int m = gv / kk;
                if (m < 3) continue;
                if (kk == 1) {
                    add_desc(0, k, gv, m, 1, 1, 0, 0, 0);
                    continue;
                }
                for (int r = 2; r < m; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, kk, m) != 1) continue;
                    add_desc(0, k, gv, m, kk, r, 0, 0, 1);   /* non-abelian */
                    break;
                }
            }
        }
    }
    /* 2. matrix groups (bi-Cayley, k = 1): known fallback */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXG) continue;
            if (2 * o < lo || 2 * o > hi) continue;
            add_desc(1, 1, (int)o, 0, 0, 0, (int)q, psl, 0);
        }
    if (npool == 0) { print_complete(); return 0; }

    qsort(pool, (size_t)npool, sizeof(Desc), cmp_desc);

    /* 3. choose the pool: nearest above-record shapes (<= 3 per k), two matrix
          fallbacks below the record, then the nearest below-record lifts */
    int cntk[MAXK + 1];
    memset(cntk, 0, sizeof cntk);
    int nab = 0, fb = -1;
    for (int i = 0; i < npool && nab < 16 && ncand < MAXCAND; i++) {
        Desc *x = &pool[i];
        if (x->V <= REFV) break;
        if (cntk[x->k] >= 3) continue;
        cntk[x->k]++;
        take(x);
        nab++;
    }
    int nmat = 0;
    for (int i = 0; i < npool && nmat < 2 && ncand < MAXCAND; i++) {
        Desc *x = &pool[i];
        if (x->V > REFV || x->type != 1) continue;
        take(x);
        if (fb < 0) fb = ncand - 1;
        nmat++;
    }
    for (int i = 0; i < npool && ncand < MAXCAND; i++) {
        Desc *x = &pool[i];
        if (x->V > REFV || x->type != 0) continue;
        if (cntk[x->k] >= 4) continue;
        cntk[x->k]++;
        take(x);
    }
    if (ncand == 0) { print_complete(); return 0; }

    int bestIdx = -1, bestV = 0;

    /* 4. short guaranteed-baseline run on the matrix fallback */
    if (fb >= 0) {
        run_cand(&cand[fb], now() + 0.08 * usable);
        if (cand[fb].bestc == 0) { bestIdx = fb; bestV = cand[fb].V; }
    }

    /* 5. successive halving over the pool */
    int alive[MAXCAND], nalive = 0;
    for (int i = 0; i < ncand; i++)
        if (cand[i].bestc != 0) alive[nalive++] = i;
    double slice = usable / (4.0 * (double)ncand);
    if (slice < 0.2) slice = 0.2;
    while (nalive > 0 && t_end - now() > 0.05) {
        for (int a = 0; a < nalive; a++) {
            if (t_end - now() < 0.05) break;
            int ci = alive[a];
            double until = now() + slice;
            if (until > t_end) until = t_end;
            run_cand(&cand[ci], until);
            if (cand[ci].bestc == 0 && cand[ci].V > bestV) {
                bestV = cand[ci].V;
                bestIdx = ci;
            }
        }
        int m = 0;
        for (int a = 0; a < nalive; a++) {
            int ci = alive[a];
            if (cand[ci].bestc == 0 || cand[ci].V <= bestV) continue;
            alive[m++] = ci;
        }
        nalive = m;
        for (int a = 1; a < nalive; a++) {
            int x = alive[a];
            double kx = key_of(x);
            int b = a - 1;
            while (b >= 0 && key_of(alive[b]) > kx) {
                alive[b + 1] = alive[b];
                b--;
            }
            alive[b + 1] = x;
        }
        if (nalive > 1) nalive = (nalive + 1) / 2;
        slice *= 2.0;
    }

    if (bestIdx < 0 || !emit_cand(&cand[bestIdx])) print_complete();
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
    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), max(best[0], 2))
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
