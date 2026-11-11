"""Program: multi-orbit voltage lifts (bi-Cayley generalisation) over metacyclic and PSL/SL(2,q) groups.

New idea (not in the parent):
  * Base graph with NB vertices per side and d-regular multiplicity matrix M (row and column sums d,
    connected). Each base dart e from A_i to B_j carries a voltage g_e in a group G of order N.
    The lift has vertices A_{i,x}, B_{j,y} (x, y in G) and edges A_{i,x} ~ B_{j, x*g_e}.
    It is bipartite, d-regular, and has 2*NB*N vertices.
  * Left multiplication by h in G is an automorphism, so the diameter test only needs BFS from
    A_{i,e} and B_{j,e} for each base vertex (2*NB sources).
  * Spanning-tree normalisation: a relabelling of fibres lets every spanning-tree dart carry the
    identity voltage, so only the non-tree darts are searched.
  * Parallel darts on the same base pair must have distinct voltages (no multi-edges).
  * Candidates are all (group, NB) pairs with NB*N in a window just above the record half-size,
    ordered by vertex count. Iterative deepening gives every candidate a slice that doubles per round.

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
#define MAXB 5
#define MAXDEG 8
#define MAXDART (MAXB * MAXDEG)
#define MAXV 10240
#define MAXCAND 400
#define SPAN 4
#define STALL_LIMIT 2500

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, b;
    long V;
} Cand;

static int d, D;
static long moore;
static long TH, HI;
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

static long gcd_l(long a, long b2) {
    while (b2) { long t = a % b2; a = b2; b2 = t; }
    return a;
}

static long powmod_l(long bb, long e, long m) {
    long r = 1 % m;
    bb %= m;
    while (e > 0) {
        if (e & 1) r = r * bb % m;
        bb = bb * bb % m;
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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int t = 1; t < k; t++) pw[t] = (int)((long)pw[t - 1] * r % m);
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

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int bb, int c, int e) {
    int q = qg;
    int kk = ((a * q + bb) * q + c) * q + e;
    if (!psl_g) return kk;
    int na = (q - a) % q, nb = (q - bb) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return kk < kn ? kk : kn;
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

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

/* ------------------------------------------------------------------ base graph */

static int NB = 1;                 /* base vertices per side */
static int Mb[MAXB][MAXB];         /* multiplicities: darts from A_i to B_j */
static int ufp[2 * MAXB];

static int uf_find(int x) {
    while (ufp[x] != x) { ufp[x] = ufp[ufp[x]]; x = ufp[x]; }
    return x;
}

/* Random d-regular multiplicity matrix on NB+NB base vertices, connected. */
static int random_base(void) {
    for (int att = 0; att < 300; att++) {
        int M[MAXB][MAXB];
        int cs[MAXB];
        memset(M, 0, sizeof M);
        memset(cs, 0, sizeof cs);
        int ok = 1;
        for (int i = 0; i < NB && ok; i++)
            for (int t = 0; t < d; t++) {
                int cand[MAXB], nc = 0;
                for (int j = 0; j < NB; j++) if (cs[j] < d) cand[nc++] = j;
                if (nc == 0) { ok = 0; break; }
                int j = cand[rndint(nc)];
                M[i][j]++;
                cs[j]++;
            }
        if (!ok) continue;
        for (int x = 0; x < 2 * NB; x++) ufp[x] = x;
        for (int i = 0; i < NB; i++)
            for (int j = 0; j < NB; j++)
                if (M[i][j]) {
                    int u = uf_find(i), v = uf_find(NB + j);
                    if (u != v) ufp[u] = v;
                }
        int root = uf_find(0), conn = 1;
        for (int x = 1; x < 2 * NB; x++)
            if (uf_find(x) != root) { conn = 0; break; }
        if (!conn) continue;
        memcpy(Mb, M, sizeof M);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ darts */

static int ndart = 0;
static int dtail[MAXDART], dhead[MAXDART], dvolt[MAXDART], dtree[MAXDART];
static int listA[MAXB][MAXDEG], listB[MAXB][MAXDEG];
static int freeList[MAXDART], nfree = 0;
static int RA[MAXDART][MAXN];   /* RA[e][x] = x * g_e */
static int RB[MAXDART][MAXN];   /* RB[e][y] = y * g_e^{-1} */

static void index_darts(void) {
    int ca[MAXB], cb[MAXB];
    memset(ca, 0, sizeof ca);
    memset(cb, 0, sizeof cb);
    for (int e = 0; e < ndart; e++) {
        int i = dtail[e], j = dhead[e];
        listA[i][ca[i]++] = e;
        listB[j][cb[j]++] = e;
    }
}

/* Darts from the multiplicity matrix, plus a random spanning tree (tree darts get the identity). */
static void build_darts(void) {
    ndart = 0;
    for (int i = 0; i < NB; i++)
        for (int j = 0; j < NB; j++)
            for (int c = 0; c < Mb[i][j]; c++) {
                dtail[ndart] = i;
                dhead[ndart] = j;
                ndart++;
            }
    index_darts();
    int perm[MAXDART];
    for (int e = 0; e < ndart; e++) perm[e] = e;
    for (int t = ndart - 1; t > 0; t--) {
        int s = rndint(t + 1);
        int tmp = perm[t];
        perm[t] = perm[s];
        perm[s] = tmp;
    }
    for (int x = 0; x < 2 * NB; x++) ufp[x] = x;
    for (int t = 0; t < ndart; t++) {
        int e = perm[t];
        int u = uf_find(dtail[e]), v = uf_find(NB + dhead[e]);
        dtree[e] = 0;
        if (u != v) {
            ufp[u] = v;
            dtree[e] = 1;
        }
    }
    nfree = 0;
    for (int e = 0; e < ndart; e++)
        if (!dtree[e]) freeList[nfree++] = e;
}

static void set_volt(int e, int g) {
    dvolt[e] = g;
    int gi = INV[g];
    for (int x = 0; x < N; x++) {
        RA[e][x] = (int)T[(size_t)x * N + g];
        RB[e][x] = (int)T[(size_t)x * N + gi];
    }
}

/* True if another dart on the same base pair already has voltage g. */
static int conflict(int e, int g) {
    for (int f = 0; f < ndart; f++)
        if (f != e && dtail[f] == dtail[e] && dhead[f] == dhead[e] && dvolt[f] == g)
            return 1;
    return 0;
}

static int init_volts(void) {
    for (int e = 0; e < ndart; e++) dvolt[e] = -1;
    for (int e = 0; e < ndart; e++)
        if (dtree[e]) set_volt(e, e_id);
    for (int e = 0; e < ndart; e++) {
        if (dtree[e]) continue;
        int ok = 0;
        for (int t = 0; t < 200 && !ok; t++) {
            int g = rndint(N);
            if (!conflict(e, g)) {
                set_volt(e, g);
                ok = 1;
            }
        }
        if (!ok) return 0;
    }
    return 1;
}

static void reroll_free(void) {
    for (int t = 0; t < nfree; t++) {
        int e = freeList[t];
        for (int tr = 0; tr < 200; tr++) {
            int g = rndint(N);
            if (!conflict(e, g)) {
                set_volt(e, g);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of lifted vertices within distance dmax of src. */
static int ball_lift(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int bN = NB * N;
    int hd = 0, tl = 0;
    stamp[src] = tick;
    qv[tl++] = src;
    for (int lvl = 0; lvl < dmax && hd < tl; lvl++) {
        int end = tl;
        for (; hd < end; hd++) {
            int v = qv[hd];
            if (v < bN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int e = listA[i][k];
                    int u = bN + dhead[e] * N + RA[e][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tl++] = u; }
                }
            } else {
                int w = v - bN;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int e = listB[j][k];
                    int u = dtail[e] * N + RB[e][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tl++] = u; }
                }
            }
        }
    }
    return tl;
}

/* Sum over base sources of unreached vertices. Zero iff the lift has diameter <= D. */
static long cost_now(void) {
    long V = 2L * NB * N, c = 0;
    for (int i = 0; i < NB; i++) {
        c += V - ball_lift(i * N + e_id, D);
        c += V - ball_lift(NB * N + i * N + e_id, D);
    }
    return c;
}

static int climb(double until) {
    if (!init_volts()) return 0;
    if (nfree == 0) return 0;
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL_LIMIT) {
            reroll_free();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int e = freeList[rndint(nfree)];
        int old = dvolt[e], g = -1;
        for (int t = 0; t < 50; t++) {
            int x = rndint(N);
            if (x != old && !conflict(e, x)) { g = x; break; }
        }
        if (g < 0) { stall++; continue; }
        set_volt(e, g);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.01) cur = nc;
        else set_volt(e, old);
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ candidates */

static Cand cands[2 * MAXCAND];
static int ncand = 0;

static void push_cand(Cand c) {
    if (ncand >= 2 * MAXCAND) return;
    if (c.N > MAXN || c.N < 2) return;
    long bn = (long)c.b * c.N;
    if (bn < TH || bn > HI) return;
    c.V = 2L * bn;
    cands[ncand++] = c;
}

static void gen_cands(void) {
    static const int qs[] = {7, 11, 13, 17};
    for (int qi = 0; qi < 4; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN) continue;
            for (int bb = 1; bb <= MAXB; bb++) {
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.b = bb;
                push_cand(c);
            }
        }
    for (int bb = 1; bb <= MAXB; bb++) {
        long Nlo = (TH + bb - 1) / bb;
        for (long Nv = Nlo; Nv <= Nlo + SPAN && Nv <= MAXN; Nv++) {
            if (Nv * bb > HI) break;
            for (long k = 1; k <= Nv; k++) {
                if (Nv % k) continue;
                long m = Nv / k;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 0;
                c.N = (int)Nv;
                c.b = bb;
                c.k = (int)k;
                c.m = (int)m;
                if (k == 1) {
                    c.r = 1;
                    push_cand(c);
                    continue;
                }
                if (m < 3) continue;
                int got = 0;
                for (long r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    c.r = (int)r;
                    push_cand(c);
                    got++;
                }
            }
        }
    }
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = x, *q2 = y;
    if (p->V != q2->V) return p->V < q2->V ? -1 : 1;
    return p->type - q2->type;
}

static long moore_cap;
static long bestV = 0;
static int have = 0;
static Cand bestC;
static int bestNB, bestNd;
static int bestTail[MAXDART], bestHead[MAXDART], bestVolt[MAXDART];

static int try_cand(const Cand *c, double until) {
    if (!apply_cand(c)) return 0;
    NB = c->b;
    long bn = (long)NB * N;
    if (2L * bn <= bestV) return 0;
    if (2L * bn > moore_cap) return 0;
    if (2L * bn > MAXV) return 0;
    if (!random_base()) return 0;
    build_darts();
    return climb(until);
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b2 = 0; b2 < d; b2++) printf("%d %d\n", a, d + b2);
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
    moore = moore_bound();
    moore_cap = moore;
    TH = ref / 2 + 1;          /* need NB*N >= TH, i.e. 2*NB*N > ref */
    HI = 2 * TH;
    if (HI > MAXV / 2) HI = MAXV / 2;
    if (TH > HI || 2 * TH > moore) { print_complete(); return 0; }

    gen_cands();
    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);
    bestV = ref;

    double budget = t_end - now();
    double base = budget / (6.0 * (double)(ncand > 0 ? ncand : 1));
    if (base < 0.15) base = 0.15;

    for (int round = 0; round < 12; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.1) break;
            if (cands[i].V <= bestV) continue;
            double slice = base * (double)(1L << round);
            if (slice > remaining) slice = remaining;
            if (try_cand(&cands[i], now() + slice)) {
                have = 1;
                bestC = cands[i];
                bestNB = NB;
                bestNd = ndart;
                bestV = 2L * NB * N;
                memcpy(bestTail, dtail, sizeof(int) * (size_t)ndart);
                memcpy(bestHead, dhead, sizeof(int) * (size_t)ndart);
                memcpy(bestVolt, dvolt, sizeof(int) * (size_t)ndart);
            }
        }
        if (t_end - now() < 0.1) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&bestC)) { print_complete(); return 0; }
    NB = bestNB;
    ndart = bestNd;
    memcpy(dtail, bestTail, sizeof(int) * (size_t)ndart);
    memcpy(dhead, bestHead, sizeof(int) * (size_t)ndart);
    index_darts();
    for (int e = 0; e < ndart; e++) set_volt(e, bestVolt[e]);
    long V = 2L * NB * N;
    if (V <= ref || cost_now() != 0) { print_complete(); return 0; }

    printf("%ld %ld\n", V, (long)ndart * N);
    for (int e = 0; e < ndart; e++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", dtail[e] * N + x, NB * N + dhead[e] * N + RA[e][x]);
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
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
