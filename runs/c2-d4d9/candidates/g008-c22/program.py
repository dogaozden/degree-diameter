"""Program: multi-orbit voltage lifts over small groups, searched by annealing and successive halving.

Construction:
  * Base graph: a vertices A_0..A_{a-1} and a vertices B_0..B_{a-1}. Each A_i carries d darts.
    Dart e = (i, k) points at B_{tgt[e]} with voltage s_e in G. Every B_j receives exactly d darts,
    which the swap moves preserve.
  * Lift: (i, x) is adjacent to (tgt[e], x * s_e) for the d darts e of A_i. The result is d-regular,
    bipartite, and has 2aN vertices. It is simple iff no two darts of one A_i share (target, voltage).
  * Left multiplication by G is an automorphism, so diameter <= D holds iff a BFS from one
    representative of each of the 2a base orbits reaches every vertex within D steps.
  * Groups are never tabulated. Products and inverses come from closed formulas for metacyclic
    groups Z_m x| Z_k, or from 2x2 matrix arithmetic with an index table for SL/PSL(2,q), q <= 17.
  * Candidates (group, a) with a*N in a window near the record are scheduled by successive halving
    over repeated pools. Each candidate gets simulated annealing over dart voltages and target swaps.
    a = 1 reproduces the plain bi-Cayley search.

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
#define MAXDEG 8
#define MAXA 8
#define MAXDART (MAXA * MAXDEG)
#define MAXM 3200
#define MAXV (2 * MAXM)
#define MAXCAND 60000
#define POOL_CAP 48
#define COST_FAIL (1L << 40)
#define AMAX 6
#define QKEY 83521
#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

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

/* ------------------------------------------------------------------ groups (no tables) */

static int gtype = 0;        /* 0 = Z_m x| Z_k, 1 = SL/PSL(2,q) */
static int N = 0, e_id = 0;
static int gm = 1, gk = 1, gr = 1;
static int pw[MAXN];        /* pw[b] = r^b mod m */
static int gq = 2, gpsl = 0;
static int gmat[MAXN][4];
static int IDXM[QKEY];

static int canon_key(int a, int b, int c, int e) {
    int q = gq;
    int k = ((a * q + b) * q + c) * q + e;
    if (!gpsl) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

/* group product x*y on element codes 0..N-1 */
static int gmul(int x, int y) {
    if (gtype == 0) {
        int k = gk, m = gm;
        int a = x / k, b = x % k, c = y / k, dd = y % k;
        int aa = (a + pw[b] * c) % m;
        int bb = (b + dd) % k;
        return aa * k + bb;
    }
    int q = gq;
    int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
    int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
    int pa = (a * a2 + b * c2) % q;
    int pb = (a * b2 + b * e2) % q;
    int pc = (c * a2 + e * c2) % q;
    int pe = (c * b2 + e * e2) % q;
    return IDXM[canon_key(pa, pb, pc, pe)];
}

/* group inverse */
static int ginv(int x) {
    if (gtype == 0) {
        int k = gk, m = gm;
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int t = pw[nb] * a % m;
        int na = (m - t) % m;
        return na * k + nb;
    }
    int q = gq;
    int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
    return IDXM[canon_key(e % q, (q - b) % q, (q - c) % q, a % q)];
}

/* Z_m x| Z_k, element (a,b) coded a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    gtype = 0;
    gm = m;
    gk = k;
    gr = r;
    N = n;
    e_id = 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    return N;
}

/* SL(2,q) or PSL(2,q), q prime, q <= 17. */
static int build_matrix(int q, int psl) {
    gtype = 1;
    gq = q;
    gpsl = psl;
    int ks = q * q * q * q;
    if (ks > QKEY) return 0;
    for (int i = 0; i < ks; i++) IDXM[i] = -1;
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
                    IDXM[own] = cnt;
                    cnt++;
                }
    N = cnt;
    e_id = IDXM[canon_key(1, 0, 0, 1)];
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, a;
} Cand;

/* lift state: NB base vertices per side, NDART = NB*d darts, MM = NB*N, V = 2*MM */
static int NB = 1, MM = 0, NDART = 0, V = 0;
static int tgt[MAXDART], sv[MAXDART];
static int Rr[MAXDART][MAXN];   /* Rr[e][x] = x * s_e */
static int Ri[MAXDART][MAXN];   /* Ri[e][y] = y * s_e^{-1} */
static int Bd[MAXA][MAXDEG];    /* darts into B_j */

static int apply_cand(const Cand *c) {
    int got = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (got != c->N || N <= d + 1) return 0;
    NB = c->a;
    MM = NB * N;
    if (MM > MAXM) return 0;
    NDART = NB * d;
    V = 2 * MM;
    return 1;
}

static void set_dart(int e) {
    int s = sv[e], si = ginv(s);
    for (int x = 0; x < N; x++) {
        Rr[e][x] = gmul(x, s);
        Ri[e][x] = gmul(x, si);
    }
}

static void rebuild_bd(void) {
    int cnt[MAXA];
    for (int j = 0; j < NB; j++) cnt[j] = 0;
    for (int e = 0; e < NDART; e++) {
        int j = tgt[e];
        if (cnt[j] < d) Bd[j][cnt[j]++] = e;
    }
}

/* true if dart e duplicates an edge of another dart from the same A_i */
static int dup_dart(int e) {
    int i = e / d;
    for (int k = 0; k < d; k++) {
        int e2 = i * d + k;
        if (e2 != e && tgt[e2] == tgt[e] && sv[e2] == sv[e]) return 1;
    }
    return 0;
}

static void init_state(void) {
    int ms[MAXDART];
    for (int t = 0; t < NDART; t++) ms[t] = t / d;
    for (int t = NDART - 1; t > 0; t--) {
        int r = rndint(t + 1);
        int tmp = ms[t];
        ms[t] = ms[r];
        ms[r] = tmp;
    }
    for (int e = 0; e < NDART; e++) tgt[e] = ms[e];
    for (int e = 0; e < NDART; e++) {
        sv[e] = rndint(N);
        while (dup_dart(e)) sv[e] = rndint(N);
    }
    for (int e = 0; e < NDART; e++) set_dart(e);
    rebuild_bd();
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* number of vertices within distance D of src */
static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < MM) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int e = i * d + k;
                    int u = MM + tgt[e] * N + Rr[e][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - MM;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int e = Bd[j][k];
                    int u = (e / d) * N + Ri[e][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* unreached vertices summed over one representative per base orbit (0 = valid) */
static long cost_now(void) {
    long c = 0;
    for (int s = 0; s < 2 * NB; s++) {
        int src = (s < NB) ? s * N + e_id : MM + (s - NB) * N + e_id;
        c += (long)(V - ball(src));
    }
    return c;
}

/* Simulated annealing over voltages and target swaps, with sawtooth reheating.
 * Returns the best cost; on return the lift state holds the best configuration seen. */
static long climb(double until) {
    if (N <= d + 1) return COST_FAIL;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return COST_FAIL;
    init_state();
    long cur = cost_now();
    long bestc = cur;
    static int bT[MAXDART], bS[MAXDART];
    memcpy(bT, tgt, sizeof(int) * (size_t)NDART);
    memcpy(bS, sv, sizeof(int) * (size_t)NDART);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int e = rndint(NDART);
        if (NB > 1 && rnd01() < 0.3) {
            /* swap the B-targets of two darts: keeps every B_j at degree d */
            int e2 = rndint(NDART);
            if (tgt[e2] == tgt[e]) continue;
            int t1 = tgt[e];
            tgt[e] = tgt[e2];
            tgt[e2] = t1;
            if (dup_dart(e) || dup_dart(e2)) {
                tgt[e2] = tgt[e];
                tgt[e] = t1;
                continue;
            }
            rebuild_bd();
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bT, tgt, sizeof(int) * (size_t)NDART);
                    memcpy(bS, sv, sizeof(int) * (size_t)NDART);
                }
            } else {
                tgt[e2] = tgt[e];
                tgt[e] = t1;
                rebuild_bd();
            }
        } else {
            /* change one voltage */
            int old = sv[e];
            int nv = rndint(N);
            if (nv == old) continue;
            sv[e] = nv;
            if (dup_dart(e)) { sv[e] = old; continue; }
            set_dart(e);
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bT, tgt, sizeof(int) * (size_t)NDART);
                    memcpy(bS, sv, sizeof(int) * (size_t)NDART);
                }
            } else {
                sv[e] = old;
                set_dart(e);
            }
        }
    }
    memcpy(tgt, bT, sizeof(int) * (size_t)NDART);
    memcpy(sv, bS, sizeof(int) * (size_t)NDART);
    for (int x = 0; x < NDART; x++) set_dart(x);
    rebuild_bd();
    return bestc;
}

/* ------------------------------------------------------------------ candidate pool */

static Cand all[MAXCAND];
static int tried[MAXCAND];
static int na = 0;
static Cand pool[POOL_CAP];
static int np = 0;

static void add_meta(int Nv, int a, Cand *arr, int *cnt) {
    for (int k = 1; k <= Nv / 3 && *cnt < MAXCAND; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 1; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            c.a = a;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

static void enumerate_cands(long lowM, long hiM) {
    static const int mq[5] = {5, 7, 11, 13, 17};
    na = 0;
    for (long M = lowM; M <= hiM; M++) {
        for (int a = 1; a <= AMAX; a++) {
            if (M % a) continue;
            long Nn = M / a;
            if (Nn < d + 2 || Nn > MAXN) continue;
            for (int qi = 0; qi < 5; qi++)
                for (int psl = 0; psl < 2; psl++) {
                    long q = mq[qi];
                    long o = q * (q * q - 1);
                    if (psl) o /= 2;
                    if (o != Nn || na >= MAXCAND) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 1;
                    c.q = (int)q;
                    c.psl = psl;
                    c.N = (int)Nn;
                    c.a = a;
                    all[na++] = c;
                }
            if (na < MAXCAND) add_meta((int)Nn, a, all, &na);
        }
    }
}

/* Fill the pool with untried candidates: matrix groups first, then a random subset of metacyclic ones. */
static void make_pool(void) {
    np = 0;
    for (int i = 0; i < na && np < POOL_CAP; i++) {
        if (tried[i] || all[i].type != 1) continue;
        tried[i] = 1;
        pool[np++] = all[i];
    }
    static int idx[MAXCAND];
    int ni = 0;
    for (int i = 0; i < na; i++)
        if (!tried[i] && all[i].type == 0) idx[ni++] = i;
    for (int t = 0; t < ni && np < POOL_CAP; t++) {
        int r = t + rndint(ni - t);
        int tmp = idx[t];
        idx[t] = idx[r];
        idx[r] = tmp;
        tried[idx[t]] = 1;
        pool[np++] = all[idx[t]];
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (ref > moore) ref = moore;
    long refM = ref / 2;                       /* half the vertex count: M = a*N */
    long lowM = (long)(0.85 * (double)refM);
    if (lowM < 3) lowM = 3;
    long hiM = (long)(1.06 * (double)refM) + 1;
    if (hiM > moore / 2) hiM = moore / 2;
    if (hiM > MAXM) hiM = MAXM;
    if (lowM > hiM) { print_complete(); return 0; }

    enumerate_cands(lowM, hiM);
    if (na == 0) { print_complete(); return 0; }

    static Cand bestC;
    static int oT[MAXDART], oS[MAXDART];
    int have = 0;
    long bestM = 0;
    static double res[POOL_CAP];
    static int alive[POOL_CAP];
    int timeup = 0;

    /* Epochs of successive halving over fresh pools until the time runs out. */
    while (!timeup) {
        double rem0 = t_end - now();
        if (rem0 < 0.5) break;
        make_pool();
        if (np == 0) {
            memset(tried, 0, sizeof tried);
            make_pool();
            if (np == 0) break;
        }
        double slice = rem0 / (3.0 * (double)np);
        if (slice > 2.0) slice = 2.0;
        if (slice < 0.1) slice = 0.1;
        int nalive = np;
        for (int i = 0; i < np; i++) {
            alive[i] = i;
            res[i] = 1e18;
        }
        while (nalive > 0 && !timeup) {
            int nnew = 0;
            for (int a2 = 0; a2 < nalive; a2++) {
                int i = alive[a2];
                Cand *c = &pool[i];
                long Mc = (long)c->a * (long)c->N;
                if (Mc <= bestM) continue;
                double rem = t_end - now();
                if (rem < 0.05) { timeup = 1; break; }
                if (!apply_cand(c)) continue;
                double sl = slice < rem ? slice : rem;
                long bc = climb(now() + sl);
                if (bc == 0) {
                    have = 1;
                    bestM = Mc;
                    bestC = *c;
                    memcpy(oT, tgt, sizeof(int) * (size_t)NDART);
                    memcpy(oS, sv, sizeof(int) * (size_t)NDART);
                    continue;
                }
                res[i] = (double)bc / (double)V;
                alive[nnew++] = i;   /* nnew <= a2, so unread entries are never overwritten */
            }
            if (timeup) break;
            for (int x = 1; x < nnew; x++) {
                int t = alive[x];
                int y = x - 1;
                while (y >= 0 && res[alive[y]] > res[t]) {
                    alive[y + 1] = alive[y];
                    y--;
                }
                alive[y + 1] = t;
            }
            nalive = (nnew + 1) / 2;
            slice *= 2.0;
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&bestC)) { print_complete(); return 0; }
    memcpy(tgt, oT, sizeof(int) * (size_t)NDART);
    memcpy(sv, oS, sizeof(int) * (size_t)NDART);
    for (int e = 0; e < NDART; e++) set_dart(e);
    rebuild_bd();
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %d\n", 2 * MM, MM * d);
    for (int e = 0; e < NDART; e++) {
        int i = e / d;
        for (int x = 0; x < N; x++)
            printf("%d %d\n", i * N + x, MM + tgt[e] * N + Rr[e][x]);
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
