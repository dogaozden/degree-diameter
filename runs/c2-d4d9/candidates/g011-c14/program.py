"""Program: multi-orbit bi-lifts over metacyclic groups, searched as resumable pool.

New idea relative to the parent (single-orbit bi-Cayley, Z_N-style groups):
  * Base graph with b A-vertices and b B-vertices, each of degree d, realised as a
    random perfect matching of A-slots to B-slots (a d-regular bipartite multigraph).
  * Each A-slot k carries a voltage g_k in a group G. The lift has 2bN vertices:
    A_i,x is joined to B_j,x*g_k for every slot k of A_i (k matched to B_j).
  * Left multiplication by G is an automorphism, so the diameter test needs only
    BFS from the 2b base vertices (v, identity). Parallel darts with equal voltage
    produce the same edge; they are merged on output (degrees only drop, so the
    result stays valid).
  * Group operations use the formula for Z_m x|_r Z_k, so no N^2 tables are needed.
    Each voltage change rebuilds only the affected slot.
  * Search: a pool of resumable simulated-annealing-style climbs over candidates
    (b, N, group) with 2bN just above the record, taken in ascending order of vertex
    count. The pool is round-robin sliced; each candidate keeps its state between
    slices. A success raises the bar, and candidates at or below the bar are dropped.
  * Metacyclic groups are tried before the cyclic group, because the parent found
    non-abelian groups effective.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output
with lib.is_valid and keeps the best valid graph, falling back to the known
construction or K_{d,d}.
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
#define MAXDEG 8
#define MAXB 6
#define MAXSLOT (MAXB * MAXDEG)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 4096
#define POOL 6
#define SLICE 0.25
#define STALL 6000

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

/* ---------------------------------------------------------- group Z_m x|_r Z_k */
/* element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */

static int GM = 3, GK = 1, NN = 3;
static int PW[MAXN];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    NN = m * k;
    long p = 1 % m;
    for (int j = 0; j < k; j++) {
        PW[j] = (int)p;
        p = p * r % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, bb = x % GK, c = y / GK, dd = y % GK;
    int aa = (int)(((long)a + (long)PW[bb] * c) % GM);
    int bq = (bb + dd) % GK;
    return aa * GK + bq;
}

static int ginv(int x) {
    int a = x / GK, bb = x % GK;
    int nbb = (GK - bb) % GK;
    long na = ((long)(GM - a) % GM) * PW[nbb] % GM;
    return (int)na * GK + nbb;
}

/* ---------------------------------------------------------- lift state */

typedef struct {
    int V, b, m, k, r, N;
    int p[MAXSLOT];      /* p[A-slot] = B-slot, a permutation of [0, b*d) */
    int g[MAXSLOT];      /* voltage of A-slot */
    long cur, bestc, stall;
    double spent;
    int inited, found;
} Cand;

static Cand Q[MAXCAND];
static int nq = 0;
static int inpool[MAXCAND];

static int nb = 1;                 /* base vertices per side for active candidate */
static int VA[MAXSLOT][MAXN];      /* VA[k][x] = x * g_k        (A side -> B side) */
static int VB[MAXSLOT][MAXN];      /* VB[k][y] = y * g_k^{-1}   (B side -> A side) */
static int qinv_arr[MAXSLOT];
static int stamp[MAXV];
static int tickc = 0;
static int qbuf[MAXV];

static void rebuild_slot(const Cand *c, int k) {
    int g = c->g[k];
    int gi = ginv(g);
    for (int x = 0; x < NN; x++) {
        VA[k][x] = gmul(x, g);
        VB[k][x] = gmul(x, gi);
    }
}

static void activate(const Cand *c) {
    set_group(c->m, c->k, c->r);
    nb = c->b;
    int S = nb * d;
    for (int k = 0; k < S; k++) rebuild_slot(c, k);
}

/* Sum over the 2b base vertices of the number of vertices NOT within distance D. */
static long eval_cost(const Cand *c) {
    int S = nb * d;
    for (int t = 0; t < S; t++) qinv_arr[t] = 0;
    for (int k = 0; k < S; k++) qinv_arr[c->p[k]] = k;
    int V2 = 2 * nb * NN;
    long total = 0;
    for (int src = 0; src < 2 * nb; src++) {
        if (++tickc == 0x7fffffff) {
            memset(stamp, 0, sizeof stamp);
            tickc = 1;
        }
        int head = 0, tail = 0;
        int sid = src * NN;
        stamp[sid] = tickc;
        qbuf[tail++] = sid;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            for (; head < end; head++) {
                int id = qbuf[head];
                int v = id / NN;
                int e = id - v * NN;
                if (v < nb) {
                    int base = v * d;
                    for (int s = 0; s < d; s++) {
                        int k = base + s;
                        int nid = (nb + c->p[k] / d) * NN + VA[k][e];
                        if (stamp[nid] != tickc) { stamp[nid] = tickc; qbuf[tail++] = nid; }
                    }
                } else {
                    int base = (v - nb) * d;
                    for (int s = 0; s < d; s++) {
                        int k = qinv_arr[base + s];
                        int nid = (k / d) * NN + VB[k][e];
                        if (stamp[nid] != tickc) { stamp[nid] = tickc; qbuf[tail++] = nid; }
                    }
                }
            }
        }
        total += V2 - tail;
    }
    return total;
}

static void randomize_cand(Cand *c) {
    int S = c->b * d;
    for (int t = 0; t < S; t++) c->p[t] = t;
    for (int t = S - 1; t > 0; t--) {
        int r = rndint(t + 1);
        int tmp = c->p[t];
        c->p[t] = c->p[r];
        c->p[r] = tmp;
    }
    for (int k = 0; k < S; k++) c->g[k] = rndint(c->N);
}

/* Resumable climb: runs until 'until' or until a valid lift is found. */
static void climb(Cand *c, double until) {
    double t0 = now();
    if (!c->inited) {
        c->inited = 1;
        randomize_cand(c);
        c->bestc = -1;
        c->stall = 0;
    }
    activate(c);
    long cur = eval_cost(c);
    if (c->bestc < 0 || cur < c->bestc) { c->bestc = cur; c->stall = 0; }
    int S = nb * d;
    while (cur > 0) {
        if (now() >= until) break;
        if (c->stall > STALL) {
            randomize_cand(c);
            activate(c);
            cur = eval_cost(c);
            c->bestc = cur;
            c->stall = 0;
            continue;
        }
        if (rnd01() < 0.5) {
            int k = rndint(S);
            int old = c->g[k];
            c->g[k] = rndint(c->N);
            rebuild_slot(c, k);
            long nc = eval_cost(c);
            if (nc <= cur || rnd01() < 0.01) {
                cur = nc;
            } else {
                c->g[k] = old;
                rebuild_slot(c, k);
            }
        } else {
            int k1 = rndint(S), k2 = rndint(S);
            if (k1 == k2) continue;
            int t = c->p[k1];
            c->p[k1] = c->p[k2];
            c->p[k2] = t;
            long nc = eval_cost(c);
            if (nc <= cur || rnd01() < 0.01) {
                cur = nc;
            } else {
                t = c->p[k1];
                c->p[k1] = c->p[k2];
                c->p[k2] = t;
            }
        }
        if (cur < c->bestc) { c->bestc = cur; c->stall = 0; }
        else c->stall++;
    }
    c->spent += now() - t0;
    if (cur == 0) c->found = 1;
}

/* ---------------------------------------------------------- candidate queue */

static void add_cand(int V, int b, int m, int k, int r) {
    if (nq >= MAXCAND) return;
    Cand *c = &Q[nq++];
    memset(c, 0, sizeof *c);
    c->V = V;
    c->b = b;
    c->m = m;
    c->k = k;
    c->r = r;
    c->N = m * k;
}

/* Metacyclic (non-abelian) groups first, then the cyclic group. */
static void add_groups(int V, int b, int N) {
    int got = 0;
    for (int k = 2; k <= 12 && got < 2; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m < 3) continue;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            add_cand(V, b, m, k, r);
            got++;
            break;
        }
    }
    add_cand(V, b, N, 1, 1);
}

/* ---------------------------------------------------------- output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static int dup_dart(const Cand *c, int i, int s) {
    int k = i * d + s;
    int j = c->p[k] / d;
    int g = c->g[k];
    for (int s2 = 0; s2 < s; s2++) {
        int k2 = i * d + s2;
        if (c->p[k2] / d == j && c->g[k2] == g) return 1;
    }
    return 0;
}

static void emit(const Cand *c) {
    activate(c);
    long cnt = 0;
    for (int i = 0; i < nb; i++)
        for (int s = 0; s < d; s++)
            if (!dup_dart(c, i, s)) cnt += NN;
    printf("%d %ld\n", 2 * nb * NN, cnt);
    for (int i = 0; i < nb; i++)
        for (int s = 0; s < d; s++) {
            if (dup_dart(c, i, s)) continue;
            int k = i * d + s;
            int j = c->p[k] / d;
            for (int x = 0; x < NN; x++)
                printf("%d %d\n", i * NN + x, (nb + j) * NN + VA[k][x]);
        }
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
    if (ref < 4) ref = 4;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < 0.5 * limit) usable = 0.5 * limit;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long Vlo = ref + (ref & 1);          /* smallest even order >= ref */
    long Vhi = Vlo + 320;
    for (long V = Vlo; V <= Vhi && V <= moore; V += 2) {
        for (int b = 1; b <= MAXB; b++) {
            if (V % (2 * b)) continue;
            long N = V / (2 * b);
            if (N < 3 || N > MAXN || (long)b * d > MAXSLOT) continue;
            add_groups((int)V, b, (int)N);
        }
    }
    if (nq == 0) { print_complete(); return 0; }

    double RET = usable / 3.0;
    int pool[POOL];
    int np = 0, qn = 0;
    long bestV = 0;
    int bestI = -1;

    while (now() < t_end) {
        while (np < POOL) {
            int pick = -1;
            for (int pass = 0; pass < 2 && pick < 0; pass++) {
                for (int t = 0; t < nq; t++) {
                    int i = qn;
                    qn = (qn + 1) % nq;
                    Cand *c = &Q[i];
                    if (inpool[i] || c->found || c->V <= bestV) continue;
                    if (pass == 0 && c->spent >= RET) continue;
                    pick = i;
                    break;
                }
            }
            if (pick < 0) break;
            inpool[pick] = 1;
            pool[np++] = pick;
        }
        if (np == 0) break;
        for (int i = 0; i < np && now() < t_end;) {
            int qi = pool[i];
            Cand *c = &Q[qi];
            if (c->V <= bestV || c->found || c->spent >= RET) {
                inpool[qi] = 0;
                pool[i] = pool[--np];
                continue;
            }
            double until = now() + SLICE;
            if (until > t_end) until = t_end;
            climb(c, until);
            if (c->found) {
                if (c->V > bestV) { bestV = c->V; bestI = qi; }
                inpool[qi] = 0;
                pool[i] = pool[--np];
                continue;
            }
            i++;
        }
    }

    if (bestI < 0) { print_complete(); return 0; }
    Cand *c = &Q[bestI];
    activate(c);
    if (eval_cost(c) != 0) { print_complete(); return 0; }
    emit(c);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    best = start
    if D == 3 and best[0] >= lib.moore_bound(d, D):
        return best                            # Moore graph: nothing to improve
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            ref = REF_VERTICES.get((d, D), 2 * d + 2)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
