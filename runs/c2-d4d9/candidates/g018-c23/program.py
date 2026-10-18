"""Program: multi-base voltage lifts of bipartite base graphs over groups, searched by
simulated annealing with iterative deepening.

Construction:
  * Base graph: P vertices on each side, joined by darts (A_i -> B_j with a voltage g in G).
    The incidence pattern is a circulant with row and column sums d (P = 1 gives the
    bi-Cayley graphs of the parent program as a special case).
  * Lift: vertices (A_i, x) and (B_j, y) for x, y in G; (A_i, x) ~ (B_j, x*g) for each dart.
    That is 2*P*|G| vertices, d-regular, bipartite. Left multiplication is an automorphism,
    so diameter <= D holds iff BFS from (A_i, e) and (B_j, e) reaches everything within D.
  * Distinct voltages inside each (i, j) class keep the lift simple.

Strategy: a larger P with a smaller group gives more freedom and a different search space
from the bi-Cayley case. Candidates are tiered: exactly the record order (secure the
record), then slightly above it (beat it), then further above, then slightly below as
fallback. Within each tier they are shuffled by seed.

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
#define MAXP 5
#define MAXD 8
#define MAXDART (MAXP * MAXD)
#define MAXV (2 * MAXP * MAXN)
#define MAXPAT 64
#define MAXPOOL 8192
#define MAXTIER 400
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

/* ------------------------------------------------------------------ group */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

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
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return 1;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
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
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return 1;
}

/* ------------------------------------------------------------------ base patterns */

static int NPAT = 0;
static int patP[MAXPAT];
static int patW[MAXPAT][MAXP];   /* circulant weights: M[i][j] = w[(j-i) mod P] */
static int cw[MAXP];

static void gen_comp(int Pp, int pos, int rem) {
    if (pos == Pp - 1) {
        cw[pos] = rem;
        if (cw[0] < 1) return;
        for (int k = 1; k < Pp; k++) if (cw[k] > cw[0]) return;
        long g = Pp;
        for (int k = 0; k < Pp; k++) if (cw[k] > 0) g = gcd_l(g, k);
        if (g != 1) return;   /* base graph would be disconnected */
        if (NPAT < MAXPAT) {
            patP[NPAT] = Pp;
            for (int k = 0; k < Pp; k++) patW[NPAT][k] = cw[k];
            NPAT++;
        }
        return;
    }
    for (int v = 0; v <= rem; v++) {
        cw[pos] = v;
        gen_comp(Pp, pos + 1, rem - v);
    }
}

/* ------------------------------------------------------------------ lift state */

static int P = 1;
static int NDART = 0;
static int dsrc[MAXDART], ddst[MAXDART], dv[MAXDART], cls[MAXDART];
static int outD[MAXP][MAXD], inD[MAXP][MAXD];
static int RR[MAXDART][MAXN];   /* RR[t][x] = x * g_t */
static int RI[MAXDART][MAXN];   /* RI[t][y] = y * g_t^{-1} */
static int VN = 0;
static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];
static int bestDV[MAXDART];

static int setup_lift(int Pp, int pat) {
    if (Pp < 1 || Pp > MAXP || N < 2) return 0;
    P = Pp;
    NDART = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++) {
            int mult = patW[pat][((j - i) % P + P) % P];
            for (int c = 0; c < mult; c++) {
                if (NDART >= MAXDART) return 0;
                dsrc[NDART] = i;
                ddst[NDART] = j;
                cls[NDART] = i * P + j;
                NDART++;
            }
        }
    int oc[MAXP] = {0}, ic[MAXP] = {0};
    for (int t = 0; t < NDART; t++) {
        int i = dsrc[t], j = ddst[t];
        if (oc[i] >= d || ic[j] >= d) return 0;
        outD[i][oc[i]++] = t;
        inD[j][ic[j]++] = t;
    }
    for (int i = 0; i < P; i++)
        if (oc[i] != d || ic[i] != d) return 0;
    VN = 2 * P * N;
    if (VN > MAXV) return 0;
    return 1;
}

static void set_dart(int t) {
    int g = dv[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        RR[t][x] = (int)T[(size_t)x * N + g];
        RI[t][x] = (int)T[(size_t)x * N + gi];
    }
}

/* True if g may be used for dart t (distinct voltages inside each (i,j) class). */
static int valid_value(int t, int g) {
    for (int s = 0; s < NDART; s++)
        if (s != t && cls[s] == cls[t] && dv[s] == g) return 0;
    return 1;
}

static void randomize_all(void) {
    for (int t = 0; t < NDART; t++) {
        int g;
        do g = rndint(N); while (!valid_value(t, g));
        dv[t] = g;
        set_dart(t);
    }
}

/* ------------------------------------------------------------------ BFS cost */

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int PN = P * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = outD[i][k];
                    int u = PN + ddst[t] * N + RR[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = inD[j][k];
                    int u = dsrc[t] * N + RI[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base-vertex fibres of the unreached count within D (0 = valid).
   Left multiplication is an automorphism, so the identity of each fibre suffices. */
static long cost_now(void) {
    long c = 0;
    int PN = P * N;
    for (int i = 0; i < P; i++) {
        c += (long)(VN - ball(i * N + e_id, D));
        c += (long)(VN - ball(PN + i * N + e_id, D));
    }
    return c;
}

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves the best valid state. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_all();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bestDV, dv, sizeof(int) * (size_t)NDART);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int t = rndint(NDART);
        int old = dv[t];
        int g;
        do g = rndint(N); while (!valid_value(t, g));
        dv[t] = g;
        set_dart(t);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestDV, dv, sizeof(int) * (size_t)NDART);
            }
        } else {
            dv[t] = old;
            set_dart(t);
        }
    }
    if (bestc != 0) return 0;
    memcpy(dv, bestDV, sizeof(int) * (size_t)NDART);
    for (int t = 0; t < NDART; t++) set_dart(t);
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, P, pat, tot;
} Cand;

static Cand pool[4][MAXPOOL];
static int npool[4];
static Cand list[4 * MAXTIER];

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok) return 0;
    return setup_lift(c->P, c->pat);
}

static int tier_of(long tot, long ref) {
    if (tot == ref) return 0;
    if (tot > ref && tot * 50 <= ref * 51) return 1;    /* within 2% above record */
    if (tot > ref && tot * 100 <= ref * 115) return 2;  /* within 15% above */
    if (tot < ref && tot * 100 >= ref * 95) return 3;   /* fallback just below */
    return -1;
}

static void push_pool(int tr, const Cand *c) {
    if (tr < 0 || tr > 3) return;
    if (npool[tr] < MAXPOOL) pool[tr][npool[tr]++] = *c;
}

static int shuffle_take(Cand *src, int n, Cand *dst, int cap) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = src[i];
        src[i] = src[j];
        src[j] = tmp;
    }
    int m = n < cap ? n : cap;
    if (m > 0) memcpy(dst, src, sizeof(Cand) * (size_t)m);
    return m;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_lift(void) {
    int PN = P * N;
    printf("%d %ld\n", VN, (long)PN * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int t = outD[i][k];
                printf("%d %d\n", i * N + x, PN + ddst[t] * N + RR[t][x]);
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
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();

    /* base patterns: circulant incidence with row and column sums d, for P = 1..MAXP */
    NPAT = 0;
    for (int Pp = 1; Pp <= MAXP; Pp++) gen_comp(Pp, 0, d);

    /* matrix group orders */
    static const int MQ[] = {5, 7, 11, 13, 17, 19};
    static int matO[32], matQ[32], matPsl[32];
    int NMAT = 0;
    for (unsigned qi = 0; qi < sizeof MQ / sizeof MQ[0]; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = MQ[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o >= 2 && o <= MAXN && NMAT < 32) {
                matO[NMAT] = (int)o;
                matQ[NMAT] = (int)q;
                matPsl[NMAT] = psl;
                NMAT++;
            }
        }

    /* candidate generation: every pattern, every group order whose total lies in a tier */
    long ref_lo = (long)(0.95 * (double)ref);
    for (int pi = 0; pi < NPAT; pi++) {
        int Pp = patP[pi];
        long lo = ref_lo / (2L * Pp);
        long hi = (long)(1.15 * (double)ref) / (2L * Pp) + 1;
        if (lo < 2) lo = 2;
        for (long Nv = lo; Nv <= hi; Nv++) {
            if (Nv > MAXN) break;
            long tot = 2L * Pp * Nv;
            if (tot > moore) break;
            int tr = tier_of(tot, ref);
            if (tr < 0) continue;
            /* metacyclic groups Z_m x| Z_k of order Nv */
            for (long k = 2; k <= Nv / 3; k++) {
                if (Nv % k) continue;
                long m = Nv / k;
                if (m < 3) continue;
                int got = 0;
                for (long r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.m = (int)m;
                    c.k = (int)k;
                    c.r = (int)r;
                    c.N = (int)Nv;
                    c.P = Pp;
                    c.pat = pi;
                    c.tot = (int)tot;
                    push_pool(tr, &c);
                    got++;
                }
            }
            /* matrix groups PSL/SL(2,q) of order Nv */
            for (int mi = 0; mi < NMAT; mi++) {
                if (matO[mi] != Nv) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = matQ[mi];
                c.psl = matPsl[mi];
                c.N = (int)Nv;
                c.P = Pp;
                c.pat = pi;
                c.tot = (int)tot;
                push_pool(tr, &c);
            }
        }
    }

    /* priority order: record-equal, then just above, then further above, then just below */
    int nl = 0;
    for (int tr = 0; tr < 4; tr++)
        nl += shuffle_take(pool[tr], npool[tr], list + nl, MAXTIER);

    double budget0 = t_end - now();
    double base = budget0 * 0.02;
    if (base < 0.4) base = 0.4;

    long bestTotal = 0;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bDV[MAXDART];

    for (int round = 0; round < 6; round++) {
        for (int i = 0; i < nl; i++) {
            double remaining = t_end - now();
            if (remaining < 0.3) break;
            Cand *c = &list[i];
            if ((long)c->tot <= bestTotal) continue;
            if (!apply_cand(c)) continue;
            long tot = (long)VN;
            if (tot <= bestTotal) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                bestTotal = tot;
                best = *c;
                have = 1;
                memcpy(bDV, dv, sizeof(int) * (size_t)NDART);
            }
        }
        if (t_end - now() < 0.3) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(dv, bDV, sizeof(int) * (size_t)NDART);
    for (int t = 0; t < NDART; t++) set_dart(t);
    if (cost_now() != 0) { print_complete(); return 0; }
    print_lift();
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
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
