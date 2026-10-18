"""Program: two-orbit bi-Cayley search with successive halving over group candidates.

New idea (not in the parent): a 2-orbit bi-Cayley graph. Base vertices are A_0, A_1, B_0, B_1,
each with a group orbit G (order N). Block (i,j) joins A_i x to B_j (x*s) for s in S_ij.
Block sizes are [[a, d-a], [d-a, a]], so every vertex has degree d and the graph has 4N vertices.
This gives vertex counts 4N, which are not reachable with one orbit when N is near 1243.

Diameter check: left translation is an automorphism, so the diameter is <= D iff BFS from
each of the 2K base vertices reaches all 2KN vertices within D steps.

Search: each candidate (group and orbit count K) keeps its own simulated-annealing state.
Successive halving runs every alive candidate for a slice that doubles each round, then drops
the worse half, ranked by unreached pairs per vertex. A valid candidate sets the new bar, and
only candidates with more vertices stay alive. Candidates include:
  * K=1, metacyclic Z_m x| Z_k of order N near record/2 (the parent's family);
  * K=2, metacyclic of order N near record/4 (new family, 4N vertices);
  * SL(2,q)/PSL(2,q) for both K.

Safety: C prints K_{d,d} if nothing is found. Python checks the output with lib.is_valid and
keeps the best valid graph. Moore graphs return immediately.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXB 4
#define MAXD 8
#define MAXV (MAXB * MAXN)
#define MAXPOOL 96
#define MAXQ4 130321

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

/* ------------------------------------------------------------ group (lazy) */
/* Elements are never tabulated: multiplication and inversion are computed on the fly. */

static int gtype = -1;          /* 0 = metacyclic, 1 = matrix */
static int N = 0, e_id = 0;
static int gm = 1, gk = 1;      /* metacyclic: Z_gm x| Z_gk */
static int pw[MAXN];            /* pw[b] = r^b mod gm */
static int gmat[MAXN][4];       /* matrix elements (canonical reps) */
static int idxm[MAXQ4];
static int qg = 2, psl_g = 0;
static int loaded_c = -1;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static void build_meta(int m, int k, int r) {
    gtype = 0;
    gm = m;
    gk = k;
    N = m * k;
    e_id = 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

static int build_matrix(int q, int psl) {
    gtype = 1;
    qg = q;
    psl_g = psl;
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
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    e_id = idxm[canon_key(1, 0, 0, 1)];
    return N;
}

typedef struct {
    int type, q, psl, m, k, r, N, K, a, V;
    int inited, alive;
    double temp;
    long best_cost;
    int sh[2][2][MAXD];
    int bsh[2][2][MAXD];
} Cand;

static Cand pool[MAXPOOL];
static int np = 0;
static long LOWV = 0, HIV = 0;

static void load_group(const Cand *cd, int idx) {
    if (loaded_c == idx) return;
    if (cd->type == 0) build_meta(cd->m, cd->k, cd->r);
    else build_matrix(cd->q, cd->psl);
    loaded_c = idx;
}

static int mul_el(int x, int y) {
    if (gtype == 0) {
        int a = x / gk, b = x - a * gk;
        int c = y / gk, dd = y - c * gk;
        int aa = (int)(((long)a + (long)pw[b] * c) % gm);
        int bb = (b + dd) % gk;
        return aa * gk + bb;
    }
    int q = qg;
    int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
    int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
    int pa = (a * a2 + b * c2) % q;
    int pb = (a * b2 + b * e2) % q;
    int pc = (c * a2 + e * c2) % q;
    int pe = (c * b2 + e * e2) % q;
    return idxm[canon_key(pa, pb, pc, pe)];
}

static int inv_el(int x) {
    if (gtype == 0) {
        int a = x / gk, b = x - a * gk;
        int nb = (gk - b) % gk;
        int aa = (int)((((long)(gm - pw[nb])) % gm) * a % gm);
        return aa * gk + nb;
    }
    int q = qg;
    int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
    return idxm[canon_key(e, (q - b) % q, (q - c) % q, a)];
}

/* ------------------------------------------------------------ 2-orbit structure */
/* Base vertices: A_i = i (i < Kc), B_j = Kc + j. Global vertex = base * N + x. */

static int Kc = 1;
static int sz[2][2];
static int cs[2][2][MAXD];                 /* current shifts */
static int NBR[MAXB][MAXD][MAXN];          /* NBR[base][dart][x] = neighbour global index */
static int bl_i[4], bl_j[4], nbl = 0;

static void set_sizes(int K_, int a) {
    Kc = K_;
    memset(sz, 0, sizeof sz);
    if (Kc == 1) {
        sz[0][0] = d;
    } else {
        sz[0][0] = a;
        sz[0][1] = d - a;
        sz[1][0] = d - a;
        sz[1][1] = a;
    }
    nbl = 0;
    for (int i = 0; i < Kc; i++)
        for (int j = 0; j < Kc; j++)
            if (sz[i][j] > 0) { bl_i[nbl] = i; bl_j[nbl] = j; nbl++; }
}

static int posA(int i, int j, int k) {
    int s = 0;
    for (int jj = 0; jj < j; jj++) s += sz[i][jj];
    return s + k;
}

static int posB(int j, int i, int k) {
    int s = 0;
    for (int ii = 0; ii < i; ii++) s += sz[ii][j];
    return s + k;
}

static void update_block(int i, int j, int k) {
    int g = cs[i][j][k];
    int gi = inv_el(g);
    int pa = posA(i, j, k), pb = posB(j, i, k);
    int tb = Kc + j;
    for (int x = 0; x < N; x++) {
        NBR[i][pa][x] = tb * N + mul_el(x, g);
        NBR[tb][pb][x] = i * N + mul_el(x, gi);
    }
}

static void rebuild_all(void) {
    for (int i = 0; i < Kc; i++)
        for (int j = 0; j < Kc; j++)
            for (int k = 0; k < sz[i][j]; k++) update_block(i, j, k);
}

static int in_block(int i, int j, int g, int upto) {
    for (int k = 0; k < upto; k++)
        if (cs[i][j][k] == g) return 1;
    return 0;
}

static void random_init(void) {
    for (int i = 0; i < Kc; i++)
        for (int j = 0; j < Kc; j++)
            for (int k = 0; k < sz[i][j]; k++) {
                int g;
                do g = rndint(N); while (in_block(i, j, g, k));
                cs[i][j][k] = g;
            }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int qv[MAXV];
static int tick = 0;

static int ball(int src) {
    if (++tick == INT_MAX) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int u = qv[head];
            int b = u / N, x = u - b * N;
            for (int p = 0; p < d; p++) {
                int w = NBR[b][p][x];
                if (stamp[w] != tick) {
                    stamp[w] = tick;
                    qv[tail++] = w;
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, target) pairs, summed over the 2*Kc base sources. */
static long cost_now(void) {
    long V = 2L * Kc * N;
    long c = 0;
    for (int s = 0; s < 2 * Kc; s++) {
        int src = s * N + e_id;
        c += V - ball(src);
    }
    return c;
}

/* ------------------------------------------------------------ candidates */

static int find_meta(long Nv, int *mo, int *ko, int *ro) {
    for (long kk = 2; kk <= Nv / 3; kk++) {
        if (Nv % kk) continue;
        long m = Nv / kk;
        if (m < 3) continue;
        for (long rr = 2; rr < m; rr++) {
            if (gcd_l(rr, m) != 1) continue;
            if (powmod_l(rr, kk, m) != 1) continue;
            *mo = (int)m;
            *ko = (int)kk;
            *ro = (int)rr;
            return 1;
        }
    }
    return 0;
}

static void add_matrix(long q, int psl, long o, int Kk, int a) {
    long V = 2L * Kk * o;
    if (np >= MAXPOOL || V < LOWV || V > HIV) return;
    Cand *c = &pool[np];
    memset(c, 0, sizeof *c);
    c->type = 1;
    c->q = (int)q;
    c->psl = psl;
    c->N = (int)o;
    c->K = Kk;
    c->a = a;
    c->V = (int)V;
    c->best_cost = LONG_MAX;
    c->temp = 2.0;
    np++;
}

static void add_meta_near(long center, long lo, long hi, int Kk, int a, int cap) {
    int got = 0;
    for (long t = 0; got < cap && t <= MAXN; t++) {
        if (center - t < lo && center + t > hi) break;
        for (int sg = 0; sg < 2; sg++) {
            if (t == 0 && sg == 1) continue;
            long Nv = sg == 0 ? center - t : center + t;
            if (Nv < lo || Nv > hi) continue;
            if (Nv <= d || Nv > MAXN) continue;
            if (np >= MAXPOOL) return;
            int m, k, r;
            if (!find_meta(Nv, &m, &k, &r)) continue;
            Cand *c = &pool[np];
            memset(c, 0, sizeof *c);
            c->type = 0;
            c->m = m;
            c->k = k;
            c->r = r;
            c->N = (int)Nv;
            c->K = Kk;
            c->a = a;
            c->V = 2 * Kk * (int)Nv;
            c->best_cost = LONG_MAX;
            c->temp = 2.0;
            np++;
            got++;
            if (got >= cap) return;
        }
    }
}

/* ------------------------------------------------------------ search */

static int run_slice(int c, double until) {
    Cand *cd = &pool[c];
    load_group(cd, c);
    if (N != cd->N) { cd->alive = 0; return 0; }
    set_sizes(cd->K, cd->a);
    if (!cd->inited) {
        random_init();
        memcpy(cd->sh, cs, sizeof cs);
        cd->inited = 1;
    }
    memcpy(cs, cd->sh, sizeof cs);
    rebuild_all();
    long cur = cost_now();
    if (cur < cd->best_cost) {
        cd->best_cost = cur;
        memcpy(cd->bsh, cs, sizeof cs);
    }
    int ok = (cur == 0);
    double temp = cd->temp;
    while (!ok && now() < until) {
        int bi = rndint(nbl);
        int i = bl_i[bi], j = bl_j[bi];
        int k = rndint(sz[i][j]);
        int g;
        do g = rndint(N); while (in_block(i, j, g, sz[i][j]));
        int old = cs[i][j][k];
        cs[i][j][k] = g;
        update_block(i, j, k);
        long nc = cost_now();
        int acc = (nc <= cur) || (rnd01() < exp(-(double)(nc - cur) / temp));
        if (acc) {
            cur = nc;
            if (cur < cd->best_cost) {
                cd->best_cost = cur;
                memcpy(cd->bsh, cs, sizeof cs);
                if (cur == 0) ok = 1;
            }
        } else {
            cs[i][j][k] = old;
            update_block(i, j, k);
        }
        temp *= 0.9995;
        if (temp < 0.15) temp = 0.15;
    }
    cd->temp = temp;
    memcpy(cd->sh, cs, sizeof cs);
    return ok;
}

static double score_of(const Cand *c) {
    if (c->best_cost == LONG_MAX) return 1e18;
    return (double)c->best_cost / (double)c->V;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void output_best(int c) {
    Cand *cd = &pool[c];
    load_group(cd, c);
    if (N != cd->N) { print_complete(); return; }
    set_sizes(cd->K, cd->a);
    memcpy(cs, cd->bsh, sizeof cs);
    rebuild_all();
    if (cost_now() != 0) { print_complete(); return; }
    long V = 2L * Kc * N;
    long E = (long)Kc * d * N;
    printf("%ld %ld\n", V, E);
    for (int i = 0; i < Kc; i++)
        for (int p = 0; p < d; p++)
            for (int x = 0; x < N; x++)
                printf("%d %d\n", i * N + x, NBR[i][p][x]);
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
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (ref <= 0) ref = moore / 4;
    if (ref < 4) ref = 4;
    LOWV = (long)(0.85 * (double)ref);
    HIV = (long)(1.2 * (double)ref);
    if (HIV > moore) HIV = moore;
    if (LOWV < 2L * d + 2) LOWV = 2L * d + 2;

    /* ---- candidate pool ---- */
    np = 0;
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN || o <= d) continue;
            add_matrix(q, psl, o, 1, 0);
            for (int a = 1; a <= d / 2; a++) add_matrix(q, psl, o, 2, a);
        }
    }
    /* one orbit, orders around record/2 (parent's family) */
    add_meta_near(ref / 2, LOWV / 2, HIV / 2, 1, 0, 12);
    /* two orbits, orders around record/4 (new family) */
    if (d / 2 >= 1) add_meta_near(ref / 4 + 1, LOWV / 4 + 1, HIV / 4, 2, d / 2, 36);
    if (d / 2 >= 2) add_meta_near(ref / 4 + 1, LOWV / 4 + 1, HIV / 4, 2, 1, 6);

    long bestV = 0;
    int bestc = -1;
    for (int c = 0; c < np; c++) pool[c].alive = 1;
    int stop = (np == 0);

    /* ---- successive halving ---- */
    for (int round = 0; !stop && round < 60; round++) {
        double slice = 0.12 * (double)(1L << (round < 8 ? round : 8));
        for (int c = 0; c < np && !stop; c++) {
            Cand *cd = &pool[c];
            if (!cd->alive) continue;
            if ((long)cd->V <= bestV) { cd->alive = 0; continue; }
            double rem = t_end - now();
            if (rem < 0.05) { stop = 1; break; }
            double s = slice < rem ? slice : rem;
            if (run_slice(c, now() + s)) {
                bestV = cd->V;
                bestc = c;
                cd->alive = 0;
            }
        }
        if (stop) break;

        int idx[MAXPOOL], na = 0;
        for (int c = 0; c < np; c++)
            if (pool[c].alive && (long)pool[c].V > bestV) idx[na++] = c;
        if (na == 0) break;
        if (na > 3) {
            for (int i = 1; i < na; i++) {
                int key = idx[i];
                double ks = score_of(&pool[key]);
                int j = i - 1;
                while (j >= 0 && score_of(&pool[idx[j]]) > ks) {
                    idx[j + 1] = idx[j];
                    j--;
                }
                idx[j + 1] = key;
            }
            for (int t = (na + 1) / 2; t < na; t++) pool[idx[t]].alive = 0;
        }
        if (t_end - now() < 0.05) break;
    }

    if (bestc < 0) { print_complete(); return 0; }
    output_best(bestc);
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
        return best   # Moore graph: nothing can beat it
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        try:
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, int(seed), round(budget, 2), ref],
                             timeout=budget + 8)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
