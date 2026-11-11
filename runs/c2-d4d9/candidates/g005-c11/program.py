"""Combined bi-Cayley / voltage-lift search for bipartite degree-diameter graphs.

Engine (C): every candidate is a base graph with P vertices per side (P = 1..4) over a finite
group G of order N, with d darts per base vertex. Dart (i, j, g) joins (i, x) to (P+j, x*g).
Left multiplication by any h in G is an automorphism that is transitive on each fibre, so the
diameter test needs only one BFS per fibre (2P BFS runs). Hill climbing with occasional
uphill moves and restarts searches the voltages.
Groups: metacyclic Z_m x| Z_k (r^k = 1 mod m) and PSL/SL(2,q) for prime q. Candidate orders
2PN are windowed around the reference: a few just below it (secure a valid graph), then the
smallest ones above it (beat it), scheduled with iterative deepening over growing time slices.

Python: algebraic starts (projective plane, Araujo-Pardo-Lopez, generalised quadrangle), then the
C engine. The output is checked with lib.is_valid, and the best valid graph is kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 3200
#define MAXP 4
#define MAXD 32
#define MAXV (2 * MAXP * MAXG)
#define MAXCAND 16384

static int d, D;
static long MOORE;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------------ groups */

/* KIND 0: metacyclic Z_MM x| Z_KK, element (a,b) = a*KK+b, (a,b)(c,e) = (a + r^b c, b+e).
 * KIND 1: matrix group, multiplication table GT (x*GN+y = x*y). */
static int KIND = 0, GN = 0, GE = 0;
static int MM = 1, KK = 1, RR = 1;
static int PW[MAXG];
static uint16_t *GT = NULL;
static size_t GT_cap = 0;
static int MQ = 2, MPSL = 0;
static int *IDXM = NULL;
static int IDXM_cap = 0;
static int GMAT[MAXG][4];
static int loaded_q = -1, loaded_psl = -1, MAT_N = 0, MAT_E = 0;

static void set_meta(int m, int k, int r) {
    KIND = 0;
    MM = m;
    KK = k;
    RR = r;
    GN = m * k;
    GE = 0;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

static int canon_key(int a, int b, int c, int e) {
    int q = MQ;
    int k = ((a * q + b) * q + c) * q + e;
    if (!MPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    loaded_q = -1;
    MQ = q;
    MPSL = psl;
    int ks = q * q * q * q;
    if (ks > IDXM_cap) {
        free(IDXM);
        IDXM = malloc(sizeof(int) * (size_t)ks);
        IDXM_cap = ks;
    }
    for (int i = 0; i < ks; i++) IDXM[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXG) return 0;
                    GMAT[cnt][0] = a;
                    GMAT[cnt][1] = b;
                    GMAT[cnt][2] = c;
                    GMAT[cnt][3] = e;
                    IDXM[own] = cnt;
                    cnt++;
                }
    if (cnt <= 0) return 0;
    size_t need = (size_t)cnt * (size_t)cnt;
    if (need > GT_cap) {
        free(GT);
        GT = malloc(sizeof(uint16_t) * need);
        GT_cap = need;
    }
    for (int x = 0; x < cnt; x++) {
        int a = GMAT[x][0], b = GMAT[x][1], c = GMAT[x][2], e = GMAT[x][3];
        for (int y = 0; y < cnt; y++) {
            int a2 = GMAT[y][0], b2 = GMAT[y][1], c2 = GMAT[y][2], e2 = GMAT[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            GT[(size_t)x * cnt + y] = (uint16_t)IDXM[canon_key(pa, pb, pc, pe)];
        }
    }
    MAT_N = cnt;
    MAT_E = IDXM[canon_key(1, 0, 0, 1)];
    GN = cnt;
    GE = MAT_E;
    KIND = 1;
    loaded_q = q;
    loaded_psl = psl;
    return cnt;
}

static int gmul(int x, int y) {
    if (KIND == 0) {
        int a = x / KK, b = x % KK, c = y / KK, e = y % KK;
        return (int)(((long)a + (long)PW[b] * c) % MM) * KK + (b + e) % KK;
    }
    return (int)GT[(size_t)x * GN + y];
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;     /* 0 metacyclic, 1 matrix */
    int p, V;     /* base size per side, vertex count 2*p*N */
    int N;        /* group order */
    int m, k, r;  /* metacyclic parameters */
    int q, psl;   /* matrix parameters */
} Cand;

static Cand LO[MAXCAND], HI[MAXCAND];
static Cand MATC[64];
static Cand ALL[2 * MAXCAND + 128];
static int nlo = 0, nhi = 0, nmat = 0, nall = 0;

static void push_cand(Cand *arr, int *cnt, const Cand *c) {
    if (*cnt < MAXCAND) arr[(*cnt)++] = *c;
}

/* Metacyclic candidates with 2pN in (wlo, whi]. */
static void gen_meta(long wlo, long whi, Cand *arr, int *cnt) {
    for (int p = 1; p <= MAXP; p++) {
        long Nmin = wlo / (2L * p) + 1, Nmax = whi / (2L * p);
        if (Nmax > MAXG) Nmax = MAXG;
        for (long N = Nmin; N <= Nmax; N++) {
            if (N <= d) continue;
            for (long k = 2; k <= N / 3; k++) {
                if (N % k) continue;
                long m = N / k;
                if (m < 3) continue;
                int got = 0;
                for (long r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1 % m) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.p = p;
                    c.N = (int)N;
                    c.m = (int)m;
                    c.k = (int)k;
                    c.r = (int)r;
                    c.V = (int)(2L * p * N);
                    push_cand(arr, cnt, &c);
                    got++;
                }
            }
        }
    }
}

/* Matrix-group candidates with 2pN in (wlo, whi]. */
static void gen_mat(long wlo, long whi) {
    static const int qs[] = {5, 7, 11, 13, 17};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXG) continue;
            for (int p = 1; p <= MAXP; p++) {
                long V = 2L * p * o;
                if (V <= wlo || V > whi) continue;
                if (nmat >= 64) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.p = p;
                c.N = (int)o;
                c.V = (int)V;
                MATC[nmat++] = c;
            }
        }
}

static int cmp_desc(const void *a, const void *b) {
    int x = ((const Cand *)a)->V, y = ((const Cand *)b)->V;
    return (x < y) - (x > y);
}

static int cmp_asc(const void *a, const void *b) {
    int x = ((const Cand *)a)->V, y = ((const Cand *)b)->V;
    return (x > y) - (x < y);
}

/* Load the group of a candidate. Returns 1 if the group is usable. */
static int apply_cand(const Cand *c) {
    if (c->type == 0) {
        set_meta(c->m, c->k, c->r);
    } else if (c->q == loaded_q && c->psl == loaded_psl) {
        KIND = 1;
        GN = MAT_N;
        GE = MAT_E;
    } else if (build_matrix(c->q, c->psl) <= 0) {
        return 0;
    }
    return GN > d;
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;
static Dart DT[MAXD * MAXP];
static int NDART = 0, P = 1, NV = 0;
static int LADJ[MAXV][MAXD];
static int LDEG[MAXV];
static int SADJ[MAXV][MAXD];
static int SDEG[MAXV];
static int SNV = 0;

/* Random d-regular bipartite base multigraph on P+P vertices (connected when P > 1). */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        if (p == 1) return;
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = (v < p) ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) {
                    seen[u] = 1;
                    ns++;
                    stack[top++] = u;
                }
            }
        }
        if (ns == 2 * p) return;
    }
}

/* A voltage not used by another dart between the same pair of base vertices. */
static int fresh_v(int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int t = 0; t < NDART; t++)
            if (t != skip && DT[t].i == i && DT[t].j == j && DT[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void reinit_darts(void) {
    int M[MAXP][MAXP];
    make_base(P, M);
    NDART = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DT[NDART].i = i;
                DT[NDART].j = j;
                DT[NDART].g = 0;
                NDART++;
                DT[NDART - 1].g = fresh_v(NDART - 1, i, j);
            }
}

static void build_lift(void) {
    int N = GN;
    NV = 2 * P * N;
    for (int v = 0; v < NV; v++) LDEG[v] = 0;
    for (int t = 0; t < NDART; t++) {
        int i = DT[t].i, j = DT[t].j, g = DT[t].g;
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            int v = (P + j) * N + gmul(x, g);
            LADJ[u][LDEG[u]++] = v;
            LADJ[v][LDEG[v]++] = u;
        }
    }
}

static int ball_stamp[MAXV];
static int ball_tick = 0;
static int bq[MAXV];

/* Number of vertices within distance D of vertex s. */
static int ball_count(int s) {
    if (++ball_tick == 0x7fffffff) {
        memset(ball_stamp, 0, sizeof ball_stamp);
        ball_tick = 1;
    }
    int head = 0, tail = 0;
    ball_stamp[s] = ball_tick;
    bq[tail++] = s;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = bq[head];
            for (int i = 0; i < LDEG[v]; i++) {
                int u = LADJ[v][i];
                if (ball_stamp[u] != ball_tick) {
                    ball_stamp[u] = ball_tick;
                    bq[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from one representative per fibre (left multiplication is transitive). */
static long sym_bad(void) {
    long bad = 0;
    for (int u = 0; u < 2 * P; u++) bad += (long)(NV - ball_count(u * GN));
    return bad;
}

/* Hill climbing over the voltages with occasional uphill moves and restarts. */
static int lift_try(double until) {
    reinit_darts();
    build_lift();
    long cur = sym_bad(), best = cur, stall = 0, it = 0;
    long stall_lim = 4000 + 2000L * P;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > stall_lim) {
            reinit_darts();
            build_lift();
            cur = sym_bad();
            best = cur;
            stall = 0;
            continue;
        }
        int t = rndint(NDART);
        int old = DT[t].g;
        DT[t].g = fresh_v(t, DT[t].i, DT[t].j);
        build_lift();
        long nb = sym_bad();
        if (nb <= cur || rnd01() < 0.02) cur = nb;
        else DT[t].g = old;
        if (cur < best) {
            best = cur;
            stall = 0;
        } else {
            stall++;
        }
    }
    build_lift();
    return 1;
}

static void save_best(void) {
    SNV = NV;
    for (int v = 0; v < NV; v++) {
        SDEG[v] = LDEG[v];
        memcpy(SADJ[v], LADJ[v], sizeof(int) * (size_t)LDEG[v]);
    }
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    double usable = limit - 0.8;
    if (usable < 0.5 * limit) usable = 0.5 * limit;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD - 1 || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    if (ref <= 0) ref = MOORE / 4;
    if (ref > MOORE) ref = MOORE;
    long lowV = (long)(0.88 * (double)ref);
    long hiV = (long)(1.15 * (double)ref);
    if (hiV > MOORE) hiV = MOORE;

    gen_mat(lowV, hiV);
    gen_meta(lowV, ref, LO, &nlo);
    gen_meta(ref, hiV, HI, &nhi);
    qsort(LO, (size_t)nlo, sizeof(Cand), cmp_desc);
    qsort(HI, (size_t)nhi, sizeof(Cand), cmp_asc);

    nall = 0;
    for (int i = 0; i < nmat && nall < 2 * MAXCAND; i++) ALL[nall++] = MATC[i];
    for (int i = 0; i < nlo && i < 12; i++) ALL[nall++] = LO[i];
    for (int i = 0; i < nhi && i < 60; i++) ALL[nall++] = HI[i];
    if (nall == 0) { print_complete(); return 0; }

    double avail = t_end - now();
    double base = avail * 0.02;
    if (base < 0.3) base = 0.3;

    long bestV = 0;
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < nall; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &ALL[i];
            if ((long)c->V <= bestV) continue;
            if (!apply_cand(c)) continue;
            P = c->p;
            double slice = base * (double)(1 << round);
            if (slice > rem) slice = rem;
            if (lift_try(now() + slice)) {
                if ((long)NV > bestV) {
                    bestV = (long)NV;
                    save_best();
                }
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (SNV == 0) { print_complete(); return 0; }
    long m = 0;
    for (int u = 0; u < SNV; u++) m += SDEG[u];
    m /= 2;
    printf("%d %ld\n", SNV, m);
    for (int u = 0; u < SNV; u++)
        for (int i = 0; i < SDEG[u]; i++)
            if (u < SADJ[u][i]) printf("%d %d\n", u, SADJ[u][i]);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidate graphs (the caller filters them with lib.is_valid)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))
    if D == 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_try(_gq_w, q))
    return [c for c in out if c is not None]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    ref = REF_VERTICES.get((d, D))
    if ref is None:
        ref = max(best[0], int(0.25 * moore))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                         timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
