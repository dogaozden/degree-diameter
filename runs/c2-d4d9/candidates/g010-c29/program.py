"""Program: multi-vertex voltage lifts over finite groups (bold change from bi-Cayley).

Construction:
  * Base graph with B vertices per side and degree d. Its darts are slots s = u*d + j
    (u = A-side base vertex). Slot s goes from A-vertex s/d to B-vertex SE[s], with
    voltage SG[s] in a group G of order N. Each B-vertex receives exactly d slots.
  * Lift: A(u,x) ~ B(v, x*g) for every dart (u, v, g). The lift is d-regular, bipartite,
    has 2*B*N vertices, and is simple iff the (B-endpoint, voltage) pairs are distinct
    within each A-block.
  * Left multiplication by any h in G is an automorphism, so diameter <= D holds iff a
    BFS from each of the 2B representatives A(u,e), B(v,e) reaches all vertices in D steps.
  * Search: hill-climbing over voltages and over the B-endpoint assignment (swap moves
    keep every B-vertex at degree d). Candidates are (B, group) pairs with 2*B*N near and
    above the record, from metacyclic groups Z_m x| Z_k and from PSL/SL(2,q).
    B = 1 is the old bi-Cayley case.
  * Scheduling: iterative deepening. Each round gives every candidate a slice that
    doubles per round. Candidates above the record are tried first.

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
#define MAXB 16
#define MAXDEG 8
#define MAXS (MAXB * MAXDEG)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 400
#define MAX_ABOVE 300
#define MAX_BELOW 60
#define RAWCAND 60000

typedef struct {
    int type;               /* 0 = metacyclic, 1 = matrix group */
    int B, m, k, r, q, psl, N, V;
} Cand;

static int d, D;
static double t_end;
static long moore_g, R_g;

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
    N = n;
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
    alloc_group(n);
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
    return N;
}

/* PSL(2,q) or SL(2,q), q prime. */
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
    alloc_group(cnt);
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
    return N;
}

/* ------------------------------------------------------------------ candidates */

static Cand *raw = NULL;
static int nraw = 0;
static Cand cands[MAXCAND];

static void push_cand(Cand c) {
    if (nraw < RAWCAND) raw[nraw++] = c;
}

static void push_meta(int Nv, int B) {
    for (int k = 1; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 1; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.B = B;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            c.V = 2 * B * Nv;
            push_cand(c);
            got++;
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    int xa = x->V > R_g, ya = y->V > R_g;
    if (xa != ya) return ya - xa;             /* above-record candidates first */
    if (xa) return (x->V > y->V) - (x->V < y->V);   /* above: ascending */
    return (y->V > x->V) - (y->V < x->V);           /* below: descending */
}

/* ------------------------------------------------------------------ lift state */

static int Bn = 1, NS = 0, BN = 0, VV = 0;   /* base per side, slots, B*N, 2*B*N */
static int SE[MAXS], SG[MAXS];               /* slot: B-endpoint, voltage */
static int VS[MAXB][MAXDEG];                 /* slots entering each B-vertex */
static int Rr[MAXS][MAXN], Ri[MAXS][MAXN];   /* Rr[s][x] = x*g_s, Ri[s][y] = y*g_s^{-1} */
static int stamp[MAXV];
static int qv[MAXV];
static int tick = 0;

static int set_group_cand(const Cand *c) {
    int n = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    return n == c->N ? n : 0;
}

static int prepare(const Cand *c) {
    if (!set_group_cand(c)) return 0;
    Bn = c->B;
    NS = Bn * d;
    BN = Bn * N;
    VV = 2 * BN;
    return 1;
}

static void set_col(int s) {
    int g = SG[s], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rr[s][x] = (int)T[(size_t)x * N + g];
        Ri[s][x] = (int)T[(size_t)x * N + gi];
    }
}

static void rebuild_VS(void) {
    int cnt[MAXB];
    memset(cnt, 0, sizeof cnt);
    for (int s = 0; s < NS; s++) {
        int v = SE[s];
        VS[v][cnt[v]++] = s;
    }
}

/* Slot s is fine if no earlier slot in its block has the same (B-endpoint, voltage). */
static int slot_ok(int s) {
    int u = s / d;
    for (int t = u * d; t < s; t++)
        if (SE[t] == SE[s] && SG[t] == SG[s]) return 0;
    return 1;
}

static int block_ok(int u) {
    for (int s = u * d; s < u * d + d; s++)
        if (!slot_ok(s)) return 0;
    return 1;
}

static int init_state(void) {
    for (int s = 0; s < NS; s++) SE[s] = s % Bn;   /* each B-vertex gets exactly d slots */
    for (int i = NS - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = SE[i]; SE[i] = SE[j]; SE[j] = t;
    }
    for (int s = 0; s < NS; s++) {
        long tries = 0;
        do {
            SG[s] = rndint(N);
            if (++tries > 100000) return 0;
        } while (!slot_ok(s));
        set_col(s);
    }
    rebuild_VS();
    return 1;
}

/* ------------------------------------------------------------------ BFS cost */

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
            if (v < BN) {
                int u = v / N, x = v - u * N;
                for (int j = 0; j < d; j++) {
                    int s = u * d + j;
                    int w = BN + SE[s] * N + Rr[s][x];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            } else {
                int t = v - BN;
                int vb = t / N, y = t - vb * N;
                for (int j = 0; j < d; j++) {
                    int s = VS[vb][j];
                    int w = (s / d) * N + Ri[s][y];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    long c = 0;
    for (int u = 0; u < Bn; u++) c += (long)(VV - ball(u * N + e_id));
    for (int v = 0; v < Bn; v++) c += (long)(VV - ball(BN + v * N + e_id));
    return c;
}

/* ------------------------------------------------------------------ search */

static int climb(double until) {
    if (!init_state()) return 0;
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 4000) {
            if (!init_state()) return 0;
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int kind = (Bn > 1) ? rndint(2) : 0;
        if (kind == 0) {
            /* change one voltage */
            int s = rndint(NS);
            int old = SG[s];
            int ng = rndint(N);
            if (ng != old) {
                SG[s] = ng;
                if (block_ok(s / d)) {
                    set_col(s);
                    long nc = cost_now();
                    if (nc <= cur || rnd01() < 0.02) cur = nc;
                    else { SG[s] = old; set_col(s); }
                } else {
                    SG[s] = old;
                }
            }
        } else {
            /* swap the B-endpoints of two slots (keeps degrees) */
            int s1 = rndint(NS), s2 = rndint(NS);
            if (SE[s1] != SE[s2]) {
                int t = SE[s1]; SE[s1] = SE[s2]; SE[s2] = t;
                if (block_ok(s1 / d) && block_ok(s2 / d)) {
                    rebuild_VS();
                    long nc = cost_now();
                    if (nc <= cur || rnd01() < 0.02) cur = nc;
                    else {
                        t = SE[s1]; SE[s1] = SE[s2]; SE[s2] = t;
                        rebuild_VS();
                    }
                } else {
                    t = SE[s1]; SE[s1] = SE[s2]; SE[s2] = t;
                }
            }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
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
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    moore_g = moore_bound();
    R_g = ref > 0 ? ref : moore_g / 4;
    if (R_g < 4) R_g = 4;
    long lowV = (long)(0.87 * (double)R_g);
    long hiV = (long)(1.13 * (double)R_g);
    if (hiV > moore_g) hiV = moore_g;

    raw = malloc(sizeof(Cand) * RAWCAND);
    if (!raw) { print_complete(); return 0; }
    nraw = 0;

    /* enumerate (B, group) candidates with 2*B*N in the window */
    static const int mq[] = {5, 7, 11, 13, 17, 19};
    for (int B = 1; B <= MAXB; B++) {
        long twoB = 2L * B;
        long Nlo = (lowV + twoB - 1) / twoB;
        long Nhi = hiV / twoB;
        if (Nlo < 3) Nlo = 3;
        if (Nhi > MAXN) Nhi = MAXN;
        if (Nhi > moore_g / twoB) Nhi = moore_g / twoB;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) push_meta((int)Nv, B);
        for (unsigned qi = 0; qi < sizeof mq / sizeof mq[0]; qi++) {
            for (int psl = 0; psl < 2; psl++) {
                long q = mq[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                if (o < Nlo || o > Nhi) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.B = B;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.V = (int)(twoB * o);
                push_cand(c);
            }
        }
    }

    /* shuffle, then keep a bounded sample of above- and below-record candidates */
    for (int i = nraw - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand t = raw[i]; raw[i] = raw[j]; raw[j] = t;
    }
    int nc = 0, na = 0, nb = 0;
    for (int i = 0; i < nraw; i++) {
        if (raw[i].V > R_g) {
            if (na < MAX_ABOVE) { cands[nc++] = raw[i]; na++; }
        } else {
            if (nb < MAX_BELOW) { cands[nc++] = raw[i]; nb++; }
        }
    }
    qsort(cands, (size_t)nc, sizeof(Cand), cmp_cand);

    int have = 0;
    long bestV = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bSE[MAXS], bSG[MAXS];

    /* iterative deepening over candidates */
    double budget0 = t_end - now();
    double base = 0.5 * budget0 / (double)(nc > 0 ? nc : 1);
    if (base < 0.05) base = 0.05;
    for (int round = 0; round < 12; round++) {
        for (int i = 0; i < nc; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[i];
            if ((long)c->V <= bestV || (long)c->V > moore_g) continue;
            if (!prepare(c)) continue;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV = VV;
                best = *c;
                memcpy(bSE, SE, sizeof SE);
                memcpy(bSG, SG, sizeof SG);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have || !prepare(&best)) { print_complete(); return 0; }
    memcpy(SE, bSE, sizeof SE);
    memcpy(SG, bSG, sizeof SG);
    for (int s = 0; s < NS; s++) set_col(s);
    rebuild_VS();
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", VV, (long)NS * N);
    for (int u = 0; u < Bn; u++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < d; j++) {
                int s = u * d + j;
                printf("%d %d\n", u * N + x, BN + SE[s] * N + Rr[s][x]);
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
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
