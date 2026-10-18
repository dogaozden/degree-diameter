"""Program: multi-base voltage lifts over finite groups, annealed in C.

New construction (not in the parent): a voltage lift over a group G of order N with
2b base vertices, b "A" base vertices and b "B" base vertices. Each A_i has d darts. Slot k
of A_i joins it to B_{(i+s_k) mod b} with voltage g_{i,k}, so the vertex set is
A(i,x), B(j,y), x,y in G, and A(i,x) ~ B((i+s_k) mod b, x*g_{i,k}).

  * Every slot k is a bijection on base indices, so every B_j also has degree d.
  * Left multiplication by G is an automorphism, so the diameter test needs only
    BFS from A(i,e) and B(j,e) for i, j in 0..b-1 (2b BFS per evaluation).
  * Order 2bN can exceed the bi-Cayley case (b = 1) for the same group order N.
    For d = 4, D = 9 the record 4970 needs N >= 1244 when b = 2, N >= 830 when b = 3,
    N >= 622 when b = 4.
  * C does simulated annealing over voltages and base shifts. A move is valid only if,
    for each A_i, the pairs (s_k, g_{i,k}) stay distinct, which keeps the graph simple.
  * Candidates: metacyclic and SL/PSL(2,q) groups for b = 2, 3, 4, plus b = 1 near
    N = record/2 as a safety net. They are sorted by vertex count, and iterative
    deepening gives each one a slice.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph.
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
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 160
#define PER_BASE_CAP 8

static int d, D, b, N, e_id;
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

static long gcd_l(long a, long c) {
    while (c) { long t = a % c; a = c; c = t; }
    return a;
}

static long powmod_l(long bs, long e, long m) {
    long r = 1 % m;
    bs %= m;
    while (e > 0) {
        if (e & 1) r = r * bs % m;
        bs = bs * bs % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------------ group */

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

/* Z_m x|_r Z_k, element (a,c) coded as a*k+c, (a,c)(a2,c2) = (a + r^c a2, c + c2). k = 1 gives Z_m. */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int q = 1; q < k; q++) pw[q] = (int)((long)pw[q - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, cb = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[cb] * c) % m;
            int bb = (cb + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int bb, int c, int e) {
    int q = qg;
    int k = ((a * q + bb) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - bb) % q, nc = (q - c) % q, ne = (q - e) % q;
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
        for (int bb = 0; bb < q; bb++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - bb * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + bb) * q + c) * q + e;
                    if (canon_key(a, bb, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = bb;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], bb = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + bb * c2) % q;
            int pb = (a * b2 + bb * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------ multi-base lift */

/* Vertices: A(i,x) = i*N + x, B(j,y) = b*N + j*N + y, with i,j in 0..b-1. */
static int sig[MAXDEG];                 /* slot k joins A_i to B_{(i+sig[k]) mod b} */
static int G[MAXB][MAXDEG];             /* voltage of A_i in slot k */
static int NA[MAXB][MAXDEG][MAXN];      /* NA[i][k][x] = B-neighbour of A(i,x) via slot k */
static int NB[MAXB][MAXDEG][MAXN];      /* NB[j][k][y] = A-neighbour of B(j,y) via slot k */

static void set_slot(int i, int k) {
    int j = (i + sig[k]) % b;
    int g = G[i][k], gi = INV[g];
    for (int x = 0; x < N; x++)
        NA[i][k][x] = b * N + j * N + (int)T[(size_t)x * N + g];
    for (int y = 0; y < N; y++)
        NB[j][k][y] = i * N + (int)T[(size_t)y * N + gi];
}

static void set_all(void) {
    for (int i = 0; i < b; i++)
        for (int k = 0; k < d; k++) set_slot(i, k);
}

/* Neighbours of A_i must be distinct: slots with equal sig need distinct voltages. */
static int valid_i(int i) {
    for (int k1 = 0; k1 < d; k1++)
        for (int k2 = k1 + 1; k2 < d; k2++)
            if (sig[k1] == sig[k2] && G[i][k1] == G[i][k2]) return 0;
    return 1;
}

static int stamp[MAXV];
static int tickc = 0;
static int qv[MAXV];

static int ball(int src) {
    if (++tickc == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tickc = 1;
    }
    int half = b * N;
    int head = 0, tail = 0;
    stamp[src] = tickc;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int u = NA[i][k][x];
                    if (stamp[u] != tickc) { stamp[u] = tickc; qv[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int u = NB[j][k][y];
                    if (stamp[u] != tickc) { stamp[u] = tickc; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    long V = 2L * b * N, c = 0;
    for (int i = 0; i < b; i++) {
        c += V - ball(i * N + e_id);
        c += V - ball(b * N + i * N + e_id);
    }
    return c;
}

static void randomize_state(void) {
    for (int k = 0; k < d; k++) sig[k] = (b > 1) ? rndint(b) : 0;
    for (int i = 0; i < b; i++) {
        do {
            for (int k = 0; k < d; k++) G[i][k] = rndint(N);
        } while (!valid_i(i));
    }
    set_all();
}

static int accept_move(long nc, long cur) {
    if (nc <= cur) return 1;
    return rnd01() < exp(-(double)(nc - cur) / 0.7);
}

static int climb(double until) {
    randomize_state();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 6000) {
            randomize_state();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        if (b > 1 && rndint(100) < 8) {
            int k = rndint(d), old = sig[k], ns = rndint(b);
            if (ns == old) { stall++; continue; }
            sig[k] = ns;
            int ok = 1;
            for (int i = 0; i < b && ok; i++) ok = valid_i(i);
            if (!ok) { sig[k] = old; stall++; continue; }
            set_all();
            long nc = cost_now();
            if (accept_move(nc, cur)) cur = nc;
            else { sig[k] = old; set_all(); }
        } else {
            int i = rndint(b), k = rndint(d), old = G[i][k], ng = rndint(N);
            if (ng == old) { stall++; continue; }
            G[i][k] = ng;
            if (!valid_i(i)) { G[i][k] = old; stall++; continue; }
            set_slot(i, k);
            long nc = cost_now();
            if (accept_move(nc, cur)) cur = nc;
            else { G[i][k] = old; set_slot(i, k); }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, b;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r) > 0;
    return build_matrix(c->q, c->psl) > 0;
}

static void push_meta(Cand *arr, int *cnt, int Nv, int bb, int m, int k, int r) {
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 0; c.m = m; c.k = k; c.r = r; c.N = Nv; c.b = bb;
    arr[(*cnt)++] = c;
}

static int gen_meta(int Nv, int bb, Cand *arr, int *cnt, int maxadd) {
    int added = 0;
    if (Nv >= 3 && *cnt < MAXCAND && added < maxadd) {
        push_meta(arr, cnt, Nv, bb, Nv, 1, 1);   /* cyclic */
        added++;
    }
    for (int k = 2; k <= Nv / 3 && added < maxadd && *cnt < MAXCAND; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        for (int r = 2; r < m && added < maxadd && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            push_meta(arr, cnt, Nv, bb, m, k, r);
            added++;
        }
    }
    return added;
}

static void push_matrix(Cand *arr, int *cnt, int q, int psl, int o, int bb) {
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 1; c.q = q; c.psl = psl; c.N = o; c.b = bb;
    arr[(*cnt)++] = c;
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = x, *s = y;
    long vp = 2L * p->b * p->N, vs = 2L * s->b * s->N;
    return (vp > vs) - (vp < vs);
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int c = 0; c < d; c++) printf("%d %d\n", a, d + c);
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

    static Cand cands[MAXCAND];
    int nc = 0;

    /* b = 1 safety net near the record vertex count (N = ref/2 and just below). */
    long h = ref / 2;
    for (long Nv = h; Nv >= h - 1 && nc < MAXCAND; Nv--)
        if (Nv >= d && Nv <= MAXN) gen_meta((int)Nv, 1, cands, &nc, 2);

    /* Multi-base lifts: 2b*N must beat the reference. Smallest N first. */
    static const int bases[3] = {2, 3, 4};
    for (int bi = 0; bi < 3; bi++) {
        int bb = bases[bi];
        long Nmin = ref / (2L * bb) + 1;
        long Nmax = moore / (2L * bb);
        if (Nmax > MAXN) Nmax = MAXN;
        int cntb = 0;
        for (long Nv = Nmin; Nv <= Nmax && cntb < PER_BASE_CAP && nc < MAXCAND; Nv++) {
            int room = PER_BASE_CAP - cntb;
            cntb += gen_meta((int)Nv, bb, cands, &nc, room < 2 ? room : 2);
        }
    }

    /* Matrix groups in the window. */
    static const int qs[6] = {5, 7, 11, 13, 17, 19};
    for (int qi = 0; qi < 6; qi++)
        for (int psl = 0; psl < 2; psl++)
            for (int bi = 0; bi < 3; bi++) {
                int bb = bases[bi];
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                long V = 2L * bb * o;
                if (o > MAXN || V <= ref || V > moore || nc >= MAXCAND) continue;
                push_matrix(cands, &nc, (int)q, psl, (int)o, bb);
            }

    qsort(cands, (size_t)nc, sizeof(Cand), cmp_cand);

    double budget0 = t_end - now();
    double base = budget0 / (4.0 * (nc > 0 ? nc : 1));
    if (base < 0.15) base = 0.15;

    int have = 0;
    long bestV = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bsig[MAXDEG];
    static int bG[MAXB][MAXDEG];

    for (int round = 0; round < 12; round++) {
        for (int i = 0; i < nc; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &cands[i];
            long Vc = 2L * c->b * c->N;
            if (Vc <= bestV || Vc > moore) continue;
            if (!apply_cand(c)) continue;
            if (N < d) continue;
            long Va = 2L * c->b * N;
            if (Va <= bestV || Va > moore) continue;
            b = c->b;
            double slice = base * (double)(1 << round);
            if (slice > rem) slice = rem;
            if (climb(now() + slice)) {
                have = 1;
                bestV = Va;
                best = *c;
                memcpy(bsig, sig, sizeof sig);
                memcpy(bG, G, sizeof G);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    b = best.b;
    memcpy(sig, bsig, sizeof sig);
    memcpy(G, bG, sizeof G);
    set_all();
    if (cost_now() != 0) { print_complete(); return 0; }

    long V = 2L * b * N, E = (long)b * N * d;
    printf("%ld %ld\n", V, E);
    for (int i = 0; i < b; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, NA[i][k][x]);
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
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
