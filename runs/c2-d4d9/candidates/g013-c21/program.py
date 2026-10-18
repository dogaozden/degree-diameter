"""Program: multi-orbit voltage lifts over finite groups, plus PSL/SL(2,q) and metacyclic groups.

New construction (this version):
  * A base bipartite multigraph with P vertices on each side and degree d, lifted over a group G
    of order N. Vertices are (side, base index, g) with 2*P*N in total. Dart k joins A_{a_k}(x) to
    B_{b_k}(x*g_k). P = 1 is the bi-Cayley graph of the previous version. P >= 2 gives many more
    degrees of freedom at the same vertex count.
  * Left multiplication by any h in G is an automorphism, so the diameter is <= D iff the BFS from
    each of the 2*P base sources (u, e) reaches all 2*P*N vertices within D steps.
  * Search moves: change the voltage of one dart, or swap the B-endpoints of two darts. Both keep
    every vertex at degree d. Duplicate edges (same pair and same voltage) are rejected.
  * Candidates: all (group, P) pairs whose vertex count 2*P*N lies just above the record (hi tier,
    smallest first), plus a few just below it (lo tier, used as a quick fallback).

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
#define MAXP 4
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 200
#define TMPCAND 40000
#define STALL 2500
#define PACC 0.02

static int d, D;
static long ref, moore;
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

/* ------------------------------------------------------------------ groups */

static int GN = 0, e_id = 0;
static uint16_t *T = NULL;     /* T[x*GN+y] = x*y */
static int *INV = NULL;        /* INV[x] = x^{-1} */
static int *idxm = NULL;
static int idxm_cap = 0;
static int gmat[MAXN][4];
static int qg, psl_g;

static void alloc_group(int n) {
    free(T);
    free(INV);
    GN = n;
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static int finish_inv(void) {
    for (int x = 0; x < GN; x++) {
        INV[x] = -1;
        for (int y = 0; y < GN; y++) {
            if ((int)T[(size_t)x * GN + y] == e_id) { INV[x] = y; break; }
        }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    alloc_group(n);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * GN + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    return finish_inv() ? GN : 0;
}

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

/* PSL(2,q) or SL(2,q), q prime. */
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
    alloc_group(cnt);
    for (int x = 0; x < GN; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < GN; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * GN + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    return finish_inv() ? GN : 0;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r;
    int ord, P, V;
} Cand;

static Cand tmpArr[TMPCAND];
static int ntmp = 0;
static Cand hiC[MAXCAND], loC[MAXCAND];
static int nhi = 0, nlo = 0;

static void add_tmp(Cand c) {
    if (ntmp < TMPCAND) tmpArr[ntmp++] = c;
}

/* All (group, P) candidates with vlo <= 2*P*|G| <= vhi. */
static void gen_window(long vlo, long vhi) {
    ntmp = 0;
    for (int P_ = 1; P_ <= MAXP; P_++) {
        long step = 2L * P_;
        long Nlo = (vlo + step - 1) / step;
        long Nhi = vhi / step;
        if (Nlo < 3) Nlo = 3;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) {
            if (step * Nv > moore) break;
            for (int k = 2; k <= Nv / 3; k++) {
                if (Nv % k) continue;
                int m = (int)(Nv / k);
                if (m < 3) continue;
                int got = 0;
                for (int r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.m = m;
                    c.k = k;
                    c.r = r;
                    c.ord = (int)Nv;
                    c.P = P_;
                    c.V = (int)(step * Nv);
                    add_tmp(c);
                    got++;
                }
            }
        }
    }
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN || o < 3) continue;
            for (int P_ = 1; P_ <= MAXP; P_++) {
                long V = 2L * P_ * o;
                if (V < vlo || V > vhi) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.ord = (int)o;
                c.P = P_;
                c.V = (int)V;
                add_tmp(c);
            }
        }
    }
}

static int cmp_asc(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->V != b->V) return a->V < b->V ? -1 : 1;
    if (a->P != b->P) return a->P - b->P;
    if (a->type != b->type) return a->type - b->type;
    return 0;
}

static int cmp_desc(const void *x, const void *y) { return cmp_asc(y, x); }

/* ------------------------------------------------------------------ lift state */

static int P = 1, NDART = 0, PN = 0, VN = 0;
static int DB[MAXDART], DG[MAXDART];        /* dart k: A-end = k/d, B-end = DB[k], voltage DG[k] */
static int Rg[MAXDART][MAXN], Ri[MAXDART][MAXN];
static int Bd[MAXP][MAXDEG];                /* darts incident to B-vertex j */

static int bestDB[MAXDART], bestDG[MAXDART];
static Cand bestCand;
static int have = 0;
static int bestV = 0;

/* Load a candidate's group and set P; returns 0 if the group cannot be built. */
static int load_cand(const Cand *c) {
    if (c->P < 1 || c->P > MAXP) return 0;
    P = c->P;
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok) return 0;
    NDART = P * d;
    PN = P * GN;
    VN = 2 * PN;
    return 1;
}

static void set_dart(int k) {
    int gk = DG[k], gi = INV[gk];
    for (int x = 0; x < GN; x++) {
        Rg[k][x] = (int)T[(size_t)x * GN + gk];
        Ri[k][x] = (int)T[(size_t)x * GN + gi];
    }
}

static void rebuild_Bd(void) {
    int cnt[MAXP] = {0, 0, 0, 0};
    for (int k = 0; k < NDART; k++) {
        int j = DB[k];
        if (cnt[j] < d) Bd[j][cnt[j]++] = k;
    }
}

static int dart_conflict(int k) {
    for (int j = 0; j < k; j++)
        if (j / d == k / d && DB[j] == DB[k] && DG[j] == DG[k]) return 1;
    return 0;
}

/* No two darts with the same (A,B) pair may share a voltage (that would make a double edge). */
static int dup_ok(void) {
    for (int i = 0; i < NDART; i++)
        for (int j = i + 1; j < NDART; j++)
            if (i / d == j / d && DB[i] == DB[j] && DG[i] == DG[j]) return 0;
    return 1;
}

static void random_init(void) {
    int pool[MAXDART];
    int c = 0;
    for (int j = 0; j < P; j++)
        for (int t = 0; t < d; t++) pool[c++] = j;
    for (int i = NDART - 1; i > 0; i--) {
        int r = rndint(i + 1);
        int tt = pool[i];
        pool[i] = pool[r];
        pool[r] = tt;
    }
    for (int k = 0; k < NDART; k++) DB[k] = pool[k];
    for (int k = 0; k < NDART; k++) {
        int tries = 0;
        do { DG[k] = rndint(GN); } while (dart_conflict(k) && ++tries < 100000);
    }
    rebuild_Bd();
    for (int k = 0; k < NDART; k++) set_dart(k);
}

/* ------------------------------------------------------------------ cost (BFS from 2P sources) */

static uint32_t stamp[MAXV];
static uint32_t tick = 0;
static int qv[MAXV];

static int ball(int src) {
    if (++tick == 0) {
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
            if (v < PN) {
                int i = v / GN, x = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int k = i * d + t;
                    int u = PN + DB[k] * GN + Rg[k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - PN, j = w / GN, y = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int k = Bd[j][t];
                    int u = (k / d) * GN + Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
        if (tail == VN) break;
    }
    return tail;
}

/* Sum over base sources of unreached vertices. Zero iff the lift has diameter <= D. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++) {
        c += (long)(VN - ball(i * GN + e_id));
        c += (long)(VN - ball(PN + i * GN + e_id));
    }
    return c;
}

static int climb(double until) {
    random_init();
    if (!dup_ok()) return 0;
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            random_init();
            if (!dup_ok()) return 0;
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        if (rndint(100) < 65) {
            /* voltage move */
            int k = rndint(NDART);
            int old = DG[k];
            int ng = rndint(GN);
            if (ng == old) { stall++; continue; }
            DG[k] = ng;
            set_dart(k);
            if (!dup_ok()) {
                DG[k] = old;
                set_dart(k);
                stall++;
                continue;
            }
            long nc = cost_now();
            if (nc <= cur || rnd01() < PACC) cur = nc;
            else {
                DG[k] = old;
                set_dart(k);
            }
        } else {
            /* endpoint swap: keeps the degree of every A and B vertex */
            int k1 = rndint(NDART), k2 = rndint(NDART);
            if (k1 / d == k2 / d || DB[k1] == DB[k2]) { stall++; continue; }
            int tmp = DB[k1];
            DB[k1] = DB[k2];
            DB[k2] = tmp;
            if (!dup_ok()) {
                tmp = DB[k1];
                DB[k1] = DB[k2];
                DB[k2] = tmp;
                stall++;
                continue;
            }
            rebuild_Bd();
            long nc = cost_now();
            if (nc <= cur || rnd01() < PACC) cur = nc;
            else {
                tmp = DB[k1];
                DB[k1] = DB[k2];
                DB[k2] = tmp;
                rebuild_Bd();
            }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ output */

static void record(const Cand *c) {
    have = 1;
    bestV = VN;
    bestCand = *c;
    memcpy(bestDB, DB, sizeof(int) * (size_t)NDART);
    memcpy(bestDG, DG, sizeof(int) * (size_t)NDART);
}

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
    ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2 || ref <= 0) { print_complete(); return 0; }
    moore = moore_bound();

    /* Lo tier: just below the record, descending (quick fallback). */
    gen_window(ref * 85 / 100, ref);
    qsort(tmpArr, (size_t)ntmp, sizeof(Cand), cmp_desc);
    nlo = 0;
    for (int i = 0; i < ntmp && nlo < 12; i++) loC[nlo++] = tmpArr[i];

    /* Hi tier: beat the record, ascending (closest to the record first). */
    gen_window(ref + 1, ref + ref / 5);
    qsort(tmpArr, (size_t)ntmp, sizeof(Cand), cmp_asc);
    nhi = 0;
    for (int i = 0; i < ntmp && nhi < MAXCAND; i++) hiC[nhi++] = tmpArr[i];

    /* Phase A: quick fallback from the lo tier. */
    {
        double budget = t_end - now();
        double fb = budget * 0.01;
        if (fb < 0.4) fb = 0.4;
        for (int i = 0; i < nlo; i++) {
            double rem = t_end - now();
            if (rem < 0.5) break;
            if (!load_cand(&loC[i])) continue;
            double slice = fb < rem ? fb : rem;
            if (climb(now() + slice)) { record(&loC[i]); break; }
        }
    }

    /* Phase B: iterative deepening over the hi tier, slices double per round. */
    {
        int H = nhi < 40 ? nhi : 40;
        double remB = t_end - now();
        double base = H > 0 ? remB / (H * 6.0) : remB;
        if (base < 0.25) base = 0.25;
        for (int round = 0; round < 16; round++) {
            int ran = 0;
            for (int i = 0; i < H; i++) {
                double rem = t_end - now();
                if (rem < 0.2) break;
                Cand *c = &hiC[i];
                if (c->V <= bestV) continue;
                if (!load_cand(c)) continue;
                ran = 1;
                double slice = base * (double)(1L << round);
                if (slice > rem) slice = rem;
                if (climb(now() + slice)) record(c);
            }
            if (!ran || t_end - now() < 0.2) break;
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!load_cand(&bestCand)) { print_complete(); return 0; }
    memcpy(DB, bestDB, sizeof(int) * (size_t)NDART);
    memcpy(DG, bestDG, sizeof(int) * (size_t)NDART);
    rebuild_Bd();
    for (int k = 0; k < NDART; k++) set_dart(k);
    if (cost_now() != 0 || !dup_ok()) { print_complete(); return 0; }

    printf("%d %d\n", VN, PN * d);
    for (int v = 0; v < PN; v++) {
        int i = v / GN, x = v - i * GN;
        for (int t = 0; t < d; t++) {
            int k = i * d + t;
            printf("%d %d\n", v, PN + DB[k] * GN + Rg[k][x]);
        }
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
    ref = REF_VERTICES.get((d, D), 0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)
    if budget > 0.2 and ref > 0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
