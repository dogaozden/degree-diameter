"""Program: bi-Cayley / voltage lifts over a wider family of groups, with a joint base+voltage climb.

Changes from the parent:
  * New group families in the C engine:
      - GL(2,q) for prime q (orders up to 2016), next to SL(2,q) and PSL(2,q);
      - direct products H x Z_m, with H one of the small matrix groups and m >= 2.
    These are non-metacyclic, non-simple groups the parent never searched.
  * Candidates are ordered purely by vertex count, so the ladder always climbs upward.
    The search window starts at 0.6 * record (not 0.87), so easy small candidates
    succeed in milliseconds and the output is almost never the K_{d,d} fallback.
  * A failed vertex count is not retried with another family of the same size.
  * The climb is the parent's joint search: voltage moves plus row swaps inside one colour
    permutation. Cost is the number of pairs at distance > D, measured from the A- and B-roots
    of each base vertex (left multiplication by G is an automorphism).

Safety: the C engine prints K_{d,d} if nothing is found. Python checks every output with
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
#define MAXH 2400
#define MAXP 8
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 200000
#define IDXM_CAP 100000
#define STALL 3000
#define PPERM 0.2
#define MAXFAIL 4096
#define NQS 6

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

/* ------------------------------------------------------------------ group tables */

static uint16_t T[MAXN * MAXN];      /* current group, stride N */
static uint16_t HT[MAXH * MAXH];     /* base matrix group for direct products, stride H */
static int N = 1, e_id = 0;
static int INV[MAXN];
static int pw_tmp[MAXN];
static int gmat[MAXN][4];
static int idxm[IDXM_CAP];
static int mq = 2, mkind = 0;

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        const uint16_t *row = T + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            if ((int)row[y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    int NN = (int)n;
    pw_tmp[0] = 1 % m;
    for (int b = 1; b < k; b++) pw_tmp[b] = (int)((long)pw_tmp[b - 1] * r % m);
    for (int x = 0; x < NN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < NN; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw_tmp[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * NN + y] = (uint16_t)(aa * k + bb);
        }
    }
    N = NN;
    e_id = 0;
    return 1;
}

static int mkey(int a, int b, int c, int e) {
    return ((a * mq + b) * mq + c) * mq + e;
}

static int mcanon(int a, int b, int c, int e) {
    int k = mkey(a, b, c, e);
    if (mkind != 1) return k;           /* SL and GL: no identification */
    int q = mq;
    int kn = mkey((q - a) % q, (q - b) % q, (q - c) % q, (q - e) % q);  /* PSL: M ~ -M */
    return k < kn ? k : kn;
}

/* kind 0 = SL(2,q), 1 = PSL(2,q), 2 = GL(2,q); q prime.
   Writes the multiplication table into tab with stride equal to the returned order.
   Returns the order, or 0 if it exceeds cap. */
static int build_mat(uint16_t *tab, int cap, int q, int kind, int *ident) {
    mq = q;
    mkind = kind;
    long ks = (long)q * q * q * q;
    if (ks > IDXM_CAP) return 0;
    for (long i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    int det = (((a * e - b * c) % q) + q) % q;
                    if (kind == 2 ? (det == 0) : (det != 1)) continue;
                    int own = mkey(a, b, c, e);
                    if (mcanon(a, b, c, e) != own) continue;
                    if (cnt >= cap || cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    int n = cnt;
    for (int x = 0; x < n; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < n; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            tab[(size_t)x * n + y] = (uint16_t)idxm[mcanon(pa, pb, pc, pe)];
        }
    }
    *ident = idxm[mcanon(1 % q, 0, 0, 1 % q)];
    return n;
}

/* Direct product H x Z_m, element (h,a) coded as h*m + a. Uses HT for H. */
static int build_prod(int H, int m, int eH) {
    long n = (long)H * m;
    if (n > MAXN || m < 2) return 0;
    int NN = (int)n;
    for (int x = 0; x < NN; x++) {
        int h1 = x / m, a1 = x % m;
        for (int y = 0; y < NN; y++) {
            int h2 = y / m, a2 = y % m;
            int hh = (int)HT[(size_t)h1 * H + h2];
            int aa = (a1 + a2) % m;
            T[(size_t)x * NN + y] = (uint16_t)(hh * m + aa);
        }
    }
    N = NN;
    e_id = eH * m;
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;      /* 0 metacyclic, 1 matrix (SL/PSL/GL), 2 matrix x Z_m */
    int q, kind, m, k, r, N, P, tier;
    long V;        /* total vertices = 2 * P * N */
} Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->tier - y->tier;
}

static void push_cand(const Cand *c) {
    if (nc < MAXCAND) CAND[nc++] = *c;
}

static long mat_order(int q, int kind) {
    long o = (long)q * ((long)q * q - 1);     /* |SL(2,q)| */
    if (kind == 1) o /= 2;                    /* |PSL(2,q)| */
    if (kind == 2) o = (long)q * (q - 1) * ((long)q * q - 1);  /* |GL(2,q)| */
    return o;
}

static void gen_candidates(long lowV, long hiV) {
    static const int QS[NQS] = {3, 5, 7, 11, 13, 17};
    nc = 0;
    for (int qi = 0; qi < NQS; qi++) {
        for (int kind = 0; kind < 3; kind++) {
            int q = QS[qi];
            long o = mat_order(q, kind);
            if (o < 2 || o > MAXN) continue;
            /* standalone matrix group */
            for (int Pp = 1; Pp <= MAXP; Pp++) {
                long V = 2L * Pp * o;
                if (V <= lowV || V > hiV || V > MOORE) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = q;
                c.kind = kind;
                c.N = (int)o;
                c.P = Pp;
                c.V = V;
                c.tier = 0;
                push_cand(&c);
            }
            /* direct product with Z_m */
            if (o > MAXH) continue;
            for (long m = 2; o * m <= MAXN; m++) {
                long Nn = o * m;
                for (int Pp = 1; Pp <= MAXP; Pp++) {
                    long V = 2L * Pp * Nn;
                    if (V <= lowV || V > hiV || V > MOORE) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 2;
                    c.q = q;
                    c.kind = kind;
                    c.m = (int)m;
                    c.N = (int)Nn;
                    c.P = Pp;
                    c.V = V;
                    c.tier = 1;
                    push_cand(&c);
                }
            }
        }
    }
    /* metacyclic groups Z_m x| Z_k */
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
                    c.tier = 2;
                    push_cand(&c);
                }
                got++;
            }
        }
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

/* ------------------------------------------------------------------ base shape */

static int P = 1, half = 1, nd = 0;
static int pm[MAXDEG][MAXP];          /* pm[c][i] = B-row hit by A-row i in colour c */
static int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXN];         /* FW[t][x] = x * g_t        (A side -> B side) */
static int BW[MAXDART][MAXN];         /* BW[t][y] = y * g_t^{-1}   (B side -> A side) */

/* Slot t = c*P + i. */
static void set_shape(int Pn) {
    P = Pn;
    half = P * N;
    nd = d * P;
    for (int t = 0; t < nd; t++) dI[t] = t % P;
    for (int i = 0; i < P; i++)
        for (int c = 0; c < d; c++) dA[i][c] = c * P + i;
}

static void sync_base(void) {
    int cb[MAXP];
    memset(cb, 0, sizeof cb);
    for (int c = 0; c < d; c++)
        for (int i = 0; i < P; i++) {
            int t = c * P + i, j = pm[c][i];
            dJ[t] = j;
            dB[j][cb[j]++] = t;
        }
}

static void set_dart(int t) {
    int g = vol[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        FW[t][x] = (int)T[(size_t)x * N + g];
        BW[t][x] = (int)T[(size_t)x * N + gi];
    }
}

/* True if dart t with voltage g clashes with a dart s < upto (s != t) on the same (i,j). */
static int conflict_with(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

static int gen_base(void) {
    int perm[MAXP];
    for (int c = 0; c < d; c++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) pm[c][i] = perm[i];
    }
    sync_base();
    for (int t = 0; t < nd; t++) {
        int g = 0, tries = 0;
        do {
            g = rndint(N);
            tries++;
        } while (conflict_with(t, g, t) && tries < 100000);
        if (tries >= 100000) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

static int apply_cand(const Cand *c) {
    int ok = 0;
    if (c->type == 0) {
        ok = build_meta(c->m, c->k, c->r);
    } else if (c->type == 1) {
        int id = 0;
        int n = build_mat(T, MAXN, c->q, c->kind, &id);
        if (n > 0) { N = n; e_id = id; ok = 1; }
    } else {
        int eh = 0;
        int H = build_mat(HT, MAXH, c->q, c->kind, &eh);
        if (H > 0 && H * c->m == c->N) ok = build_prod(H, c->m, eh);
    }
    if (!ok || N != c->N) return 0;
    finish_inv();
    set_shape(c->P);
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

/* ------------------------------------------------------------------ joint climb */

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
        if (P >= 2 && rnd01() < PPERM) {
            int c = rndint(d);
            int i1 = rndint(P), i2 = rndint(P - 1);
            if (i2 >= i1) i2++;
            int j1 = pm[c][i1], j2 = pm[c][i2];
            int t1 = c * P + i1, t2 = c * P + i2;
            pm[c][i1] = j2;
            pm[c][i2] = j1;
            sync_base();
            if (conflict_with(t1, vol[t1], nd) || conflict_with(t2, vol[t2], nd)) {
                pm[c][i1] = j1;
                pm[c][i2] = j2;
                sync_base();
                stall++;
                continue;
            }
            long c2 = cost_now();
            if (c2 <= cur || rnd01() < 0.01) {
                cur = c2;
            } else {
                pm[c][i1] = j1;
                pm[c][i2] = j2;
                sync_base();
            }
        } else {
            int t = rndint(nd);
            int old = vol[t];
            int g = rndint(N);
            if (g == old || conflict_with(t, g, nd)) { stall++; continue; }
            vol[t] = g;
            set_dart(t);
            long c2 = cost_now();
            if (c2 <= cur || rnd01() < 0.01) {
                cur = c2;
            } else {
                vol[t] = old;
                set_dart(t);
            }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ snapshot / output */

static int sP, sN;
static int spm[MAXDEG][MAXP];
static int svol[MAXDART];

static void snapshot(void) {
    sP = P;
    sN = N;
    memcpy(spm, pm, sizeof pm);
    memcpy(svol, vol, sizeof(int) * (size_t)nd);
}

/* Requires the current group to be the snapshot's group. */
static int restore(void) {
    if (N != sN) return 0;
    set_shape(sP);
    memcpy(pm, spm, sizeof pm);
    memcpy(vol, svol, sizeof(int) * (size_t)nd);
    sync_base();
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
        lowV = (long)(0.6 * (double)ref);
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
    static long failed[MAXFAIL];
    int nf = 0;

    /* Ascending ladder: each candidate gets a slice; a failed vertex count is not retried. */
    for (int i = 0; i < nc; i++) {
        if (t_end - now() < 0.3) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV) continue;
        int skip = 0;
        for (int f = 0; f < nf; f++)
            if (failed[f] == c->V) { skip = 1; break; }
        if (skip) continue;
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
        } else if (nf < MAXFAIL) {
            failed[nf++] = c->V;
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
    # Leave room for C compilation (cached after the first run), Python overhead and parsing.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
