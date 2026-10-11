"""Bold variant: voltage lifts over an explicit list of finite groups.

The C engine does simulated annealing with breakout weights and an elite pool
(iterated local search). Groups come in two families, chosen 50/50 when both
are eligible:
  * semidirect products Z_m x| Z_k (computed by formula in C), sampled from all
    valid (m, k, r) with r^k = 1 mod m;
  * explicit multiplication tables for non-metacyclic groups: PSL(2,7),
    PGL(2,7), SL(2,5), PGL(2,5), AGL(1,16), AGL(1,25), AGL(2,3), and direct
    products with small cyclic groups.

A lift over a group of order N with K base vertices per side has 2KN vertices
and degree DEG. Left multiplication is an automorphism, so the diameter check
only needs BFS from the 2K block representatives.

Baselines (Haar graph, PG(2,q), W(q)) are always computed in Python and
validated, so every case returns a valid graph.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine.
# Input (stdin, read as a flat token stream after the "n m" header):
#   ngroups, then per group:
#     0 m k r                 semidirect Z_m x| Z_k, element a*k+b
#     1 N t_0 ... t_{N*N-1}   explicit table, t[x*N+y] = x*y
# Output: "n m" plus edges of the best valid graph found, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 8000
#define MAXN 1024
#define MAXK 4
#define MAXDEG 8
#define MAXT (MAXDEG * MAXK)
#define MAXV (2 * MAXK * MAXN)
#define WINDOW 1600
#define POOLMAX 24
#define ITERS 15000
#define ILS_ITERS 6000
#define BRK 150

typedef struct {
    int type;
    int N;
    int m, k;
    int *pw;
    int *tab;
} Group;

typedef struct {
    int gi, K;
    long long cost;
    int J[MAXT], S[MAXT];
} Elite;

static Group grp[MAXG];
static int ngrp = 0;
static Elite pool[POOLMAX];
static int npool = 0;

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;

static long long bestn = 0;
static int have_best = 0;
static int best_gi = -1, best_K = 0;
static int best_dJ[MAXT], best_dS[MAXT];

static int gi, K, N, T;
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int bJ[MAXT], bS[MAXT];
static int perm[MAXT * MAXN];
static int adj[MAXV * MAXDEG];
static int cntv[MAXV], stampa[MAXV], fr[MAXV], nx[MAXV];
static int curstamp = 0;
static long long wt[2 * MAXK], unc[2 * MAXK], cur_unc[2 * MAXK];
static long long last_true, last_w, last_pen;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static inline int gmul(int g, int x, int y) {
    const Group *G = &grp[g];
    if (G->type == 1) return G->tab[(size_t)x * (size_t)G->N + (size_t)y];
    int k = G->k, m = G->m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int ra = (int)(((long long)a + (long long)G->pw[b] * c) % m);
    int rb = (b + e) % k;
    return ra * k + rb;
}

static int eligible(int g, int kk) {
    long long V = 2LL * kk * grp[g].N;
    return V > bestn && V <= WINDOW;
}

static void set_group(int g, int kk) {
    gi = g;
    K = kk;
    N = grp[g].N;
    T = DEG * K;
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
}

static void build_perm(int t) {
    int *pm = perm + (size_t)t * MAXN;
    for (int x = 0; x < N; x++) pm[x] = gmul(gi, x, dS[t]);
}

/* Each layer l holds K darts t = l*K + i with dI = i. dJ is a permutation per layer. */
static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(N);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(N);
            build_perm(t);
        }
    }
}

/* Computes per-block uncovered counts (unc), duplicate-edge penalty, and both costs. */
static void eval_state(void) {
    int V = 2 * K * N;
    for (int v = 0; v < V; v++) cntv[v] = 0;
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * N, bj = (K + dJ[t]) * N;
        const int *pm = perm + (size_t)t * MAXN;
        for (int x = 0; x < N; x++) {
            int a = ai + x, b = bj + pm[x];
            adj[(size_t)a * DEG + cntv[a]++] = b;
            adj[(size_t)b * DEG + cntv[b]++] = a;
        }
    }
    long long dup = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dup++;
    long long pen = dup * (long long)V;

    for (int r = 0; r < 2 * K; r++) {
        int src = r * N;
        if (curstamp >= 2000000000) {
            memset(stampa, 0, sizeof(stampa));
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stampa[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stampa[v] != curstamp) {
                        stampa[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = V - count;
    }
    long long total = 0, w = 0;
    for (int r = 0; r < 2 * K; r++) {
        total += unc[r];
        w += wt[r] * unc[r];
    }
    last_pen = pen;
    last_true = total + pen;
    last_w = w + pen;
}

/* Annealing on the breakout-weighted cost. Returns the best true cost; the best state is in bJ/bS. */
static long long run_sa(int iters, double tscale) {
    const int nb = 2 * K;
    long long cur = last_true, curw = last_w, curpen = last_pen;
    for (int r = 0; r < nb; r++) cur_unc[r] = unc[r];
    long long bestc = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    long long prevc = cur;
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cur >= prevc) {
                for (int r = 0; r < nb; r++)
                    if (cur_unc[r] > 0) wt[r]++;
                curw = curpen;
                for (int r = 0; r < nb; r++) curw += wt[r] * cur_unc[r];
            }
            prevc = cur;
        }
        double sumw = 0.0;
        for (int r = 0; r < nb; r++) sumw += (double)wt[r];
        double temp = tscale * (2.0 * (1.0 - (double)it / iters) + 0.05) * (sumw / nb);
        int accept = 0;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            eval_state();
            if (last_w <= curw || rnd_unit() < exp(-(double)(last_w - curw) / temp)) accept = 1;
            else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t], news = rnd_int(N);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            eval_state();
            if (last_w <= curw || rnd_unit() < exp(-(double)(last_w - curw) / temp)) accept = 1;
            else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (accept) {
            cur = last_true;
            curw = last_w;
            curpen = last_pen;
            for (int r = 0; r < nb; r++) cur_unc[r] = unc[r];
            if (cur < bestc) {
                bestc = cur;
                memcpy(bJ, dJ, sizeof(int) * (size_t)T);
                memcpy(bS, dS, sizeof(int) * (size_t)T);
            }
        }
    }
    return bestc;
}

static void record_success(void) {
    long long V = 2LL * K * N;
    if (V > bestn) {
        bestn = V;
        have_best = 1;
        best_gi = gi;
        best_K = K;
        memcpy(best_dJ, bJ, sizeof(int) * (size_t)T);
        memcpy(best_dS, bS, sizeof(int) * (size_t)T);
    }
}

static void pool_add(long long cost, int g, int kk) {
    if (cost <= 0) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Elite *e = &pool[slot];
    e->gi = g;
    e->K = kk;
    e->cost = cost;
    memcpy(e->J, bJ, sizeof(int) * (size_t)(DEG * kk));
    memcpy(e->S, bS, sizeof(int) * (size_t)(DEG * kk));
}

static int pick_elite(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (eligible(pool[i].gi, pool[i].K)) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Choose a (group, K) pair whose vertex count beats bestn, half from tables and half from semidirect products. */
static int pick_pair(int *og, int *ok) {
    long long cnt[2] = {0, 0};
    for (int g = 0; g < ngrp; g++)
        for (int kk = 1; kk < MAXK; kk++)
            if (eligible(g, kk)) cnt[grp[g].type]++;
    if (cnt[0] == 0 && cnt[1] == 0) return 0;
    int ty;
    if (cnt[0] == 0) ty = 1;
    else if (cnt[1] == 0) ty = 0;
    else ty = (rnd_unit() < 0.5) ? 1 : 0;
    long long pick = (long long)(rnd64() % (uint64_t)cnt[ty]);
    for (int g = 0; g < ngrp; g++)
        for (int kk = 1; kk < MAXK; kk++) {
            if (grp[g].type == ty && eligible(g, kk)) {
                if (pick == 0) {
                    *og = g;
                    *ok = kk;
                    return 1;
                }
                pick--;
            }
        }
    return 0;
}

static void ils_run(int e) {
    int g = pool[e].gi, kk = pool[e].K;
    set_group(g, kk);
    memcpy(dJ, pool[e].J, sizeof(int) * (size_t)T);
    memcpy(dS, pool[e].S, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    perturb(2 + rnd_int(4));
    eval_state();
    long long bc = run_sa(ILS_ITERS, 0.4);
    if (bc == 0) record_success();
    pool_add(bc, gi, K);
}

static int fresh_run(void) {
    int g = 0, kk = 0;
    if (!pick_pair(&g, &kk)) return 0;
    set_group(g, kk);
    random_init();
    eval_state();
    long long bc = run_sa(ITERS, 1.0);
    if (bc == 0) record_success();
    pool_add(bc, gi, K);
    return 1;
}

static void read_input(void) {
    long long hn = 0, hm = 0;
    if (scanf("%lld %lld", &hn, &hm) != 2) return;
    int cnt = 0;
    if (scanf("%d", &cnt) != 1) return;
    for (int g = 0; g < cnt; g++) {
        int type = 0;
        if (scanf("%d", &type) != 1) return;
        if (type == 0) {
            int m = 0, k = 0, r = 0;
            if (scanf("%d %d %d", &m, &k, &r) != 3) return;
            if (ngrp >= MAXG || m < 1 || k < 1 || m * k > MAXN) continue;
            Group *G = &grp[ngrp++];
            G->type = 0;
            G->m = m;
            G->k = k;
            G->N = m * k;
            G->tab = NULL;
            G->pw = malloc(sizeof(int) * (size_t)k);
            G->pw[0] = 1 % m;
            for (int b = 1; b < k; b++)
                G->pw[b] = (int)((long long)G->pw[b - 1] * r % m);
        } else {
            int n = 0;
            if (scanf("%d", &n) != 1) return;
            long long cells = (long long)n * (long long)n;
            int keep = (n >= 1 && n <= MAXN && ngrp < MAXG);
            int *tab = keep ? malloc(sizeof(int) * (size_t)cells) : NULL;
            for (long long i = 0; i < cells; i++) {
                int v = 0;
                if (scanf("%d", &v) != 1) return;
                if (tab) tab[i] = v;
            }
            if (keep) {
                Group *G = &grp[ngrp++];
                G->type = 1;
                G->N = n;
                G->m = 0;
                G->k = 0;
                G->pw = NULL;
                G->tab = tab;
            } else {
                free(tab);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    bestn = argc > 5 ? atoll(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    read_input();
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int e = -1;
        if (npool > 0 && rnd_unit() < 0.5) e = pick_elite();
        if (e >= 0) ils_run(e);
        else if (!fresh_run()) break;
    }

    if (have_best) {
        int kk = best_K, g = best_gi;
        int NN = grp[g].N;
        int V = 2 * kk * NN, TT = DEG * kk;
        printf("%d %d\n", V, TT * NN);
        for (int t = 0; t < TT; t++) {
            int i = t % kk;
            for (int x = 0; x < NN; x++) {
                int a = i * NN + x;
                int b = (kk + best_dJ[t]) * NN + gmul(g, x, best_dS[t]);
                printf("%d %d\n", a, b);
            }
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baseline families (unchanged from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group families for the C engine.
# ----------------------------------------------------------------------------

def _semidirect_sample(seed, min_order=60, max_order=800, cap=2500):
    """Random sample of (m, k, r) with Z_m x| Z_k, r^k = 1 mod m, gcd(r, m) = 1, order in range."""
    cands = []
    for m in range(2, max_order + 1):
        for k in range(1, max_order // m + 1):
            if m * k < min_order:
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append((m, k, r))
    rng = random.Random(seed * 7919 + 1)
    if len(cands) > cap:
        cands = rng.sample(cands, cap)
    return cands


def _matrix_table(q, mode):
    """Multiplication table of SL(2,q) ('sl'), PGL(2,q) ('pgl') or PSL(2,q) ('psl'), q prime."""
    F = lib.GF(q)
    MT = F.mul_table.tolist()
    AD = F.add_table.tolist()
    INV = [0] + [F.inv(x) for x in range(1, q)]
    squares = {MT[x][x] for x in range(1, q)}

    def canon(m):
        if mode == "sl":
            return m
        c = next(x for x in m if x)
        ci = INV[c]
        return tuple(MT[ci][x] for x in m)

    def mm(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return canon((AD[MT[a][e]][MT[b][g]], AD[MT[a][f]][MT[b][h]],
                      AD[MT[c][e]][MT[d][g]], AD[MT[c][f]][MT[d][h]]))

    elems = set()
    for m in itertools.product(range(q), repeat=4):
        det = F.sub(F.mul(m[0], m[3]), F.mul(m[1], m[2]))
        if det == 0:
            continue
        if mode == "sl" and det != 1:
            continue
        if mode == "psl" and det not in squares:
            continue
        elems.add(canon(m))
    elems = sorted(elems)
    idx = {e: i for i, e in enumerate(elems)}
    flat = []
    for x in elems:
        for y in elems:
            flat.append(idx[mm(x, y)])
    return len(elems), flat


def _agl1_table(q):
    """Affine group AGL(1,q) = {x -> a x + b}, a != 0, with q a prime power (table via numpy)."""
    F = lib.GF(q)
    M = F.mul_table
    AD = F.add_table
    A = np.repeat(np.arange(1, q), q)
    B = np.tile(np.arange(q), q - 1)
    a2 = M[A[:, None], A[None, :]]
    b2 = AD[M[A[:, None], B[None, :]], B[:, None]]
    idx = (a2 - 1) * q + b2
    return len(A), idx.ravel().tolist()


def _agl23_table():
    """Affine group AGL(2,3) = {x -> A x + v}, A in GL(2,3), order 432."""
    p = 3
    mats = [m for m in itertools.product(range(p), repeat=4) if (m[0] * m[3] - m[1] * m[2]) % p]
    vecs = list(itertools.product(range(p), repeat=2))
    els = [(m, v) for m in mats for v in vecs]
    idx = {e: i for i, e in enumerate(els)}

    def mm(x, y):
        (a, b, c, d), v = x
        (e, f, g, h), w = y
        M2 = ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)
        u = ((a * w[0] + b * w[1] + v[0]) % p, (c * w[0] + d * w[1] + v[1]) % p)
        return (M2, u)

    flat = [idx[mm(x, y)] for x in els for y in els]
    return len(els), flat


def _times_cyclic(N, flat, c):
    """Direct product of a table group (order N) with Z_c."""
    base = np.array(flat, dtype=np.int64).reshape(N, N)
    g = np.repeat(np.arange(N), c)
    z = np.tile(np.arange(c), N)
    tab = base[g[:, None], g[None, :]] * c + (z[:, None] + z[None, :]) % c
    return N * c, tab.ravel().tolist()


def _table_groups(start, limit):
    """Explicit non-metacyclic groups, built while the time guard allows."""
    builders = [
        lambda: _matrix_table(7, "psl"),                    # PSL(2,7), order 168
        lambda: _matrix_table(7, "pgl"),                    # PGL(2,7), order 336
        lambda: _matrix_table(5, "sl"),                     # SL(2,5), order 120
        lambda: _matrix_table(5, "pgl"),                    # S5 = PGL(2,5), order 120
        lambda: _agl1_table(16),                            # AGL(1,16), order 240
        lambda: _agl23_table(),                             # AGL(2,3), order 432
        lambda: _agl1_table(25),                            # AGL(1,25), order 600
        lambda: _times_cyclic(*_matrix_table(5, "sl"), 3),  # SL(2,5) x Z3, order 360
        lambda: _times_cyclic(*_matrix_table(5, "pgl"), 3), # S5 x Z3, order 360
        lambda: _times_cyclic(*_matrix_table(7, "psl"), 2), # PSL(2,7) x Z2, order 336
        lambda: _times_cyclic(*_matrix_table(5, "sl"), 2),  # SL(2,5) x Z2, order 240
    ]
    tables = []
    for make in builders:
        if time.monotonic() - start > 0.2 * limit:
            break
        N, flat = make()
        if 2 <= N <= 1024:
            tables.append((N, flat))
    return tables


def _encode(sem, tables):
    """Pack the group list as a flat token stream, shipped as (u, v) pairs on stdin."""
    toks = [len(sem) + len(tables)]
    for m, k, r in sem:
        toks += [0, m, k, r]
    for N, flat in tables:
        toks += [1, N]
        toks += flat
    if len(toks) % 2:
        toks.append(0)
    return list(zip(toks[0::2], toks[1::2]))


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D) or d > 8:
        return best

    try:
        sem = _semidirect_sample(seed)
        tables = _table_groups(start, time_limit)
        edges = _encode(sem, tables)
        remaining = 0.88 * time_limit - (time.monotonic() - start) - 2.0
        if remaining >= 2.0:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=(0, edges), timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
