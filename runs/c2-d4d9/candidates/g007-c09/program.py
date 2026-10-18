"""Program: lift search with a bit-parallel growth phase.

Two stages inside one C engine:
  1. Voltage lifts of small base graphs over groups (SL(2,q), PSL(2,q), PGL(2,q),
     and metacyclic Z_m x| Z_k), ascending in vertex count above the best found so far.
     Each candidate is climbed by hill-climbing on voltages until every orbit representative
     reaches the whole graph within D steps.
  2. Growth. Starting from the best valid d-regular bipartite graph, repeatedly
     (a) insert a pair of new vertices a (A-side) and b (B-side) by removing d edges
     x_i-y_i and joining a to all y_i and b to all x_i (degrees stay exactly d), and
     (b) apply random 2-switches that keep the graph simple and bipartite.
     A move is kept only if an exact all-pairs check (bit-parallel BFS over 64-bit words)
     still reports diameter <= D. Otherwise it is reverted, so the state is always valid.

Safety: the C engine prints K_{d,d} if nothing else is available. Python re-checks the
output with lib.is_valid and keeps the larger valid graph, falling back to the known
start otherwise.
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
#define MAXP 8
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 200000
#define IDXM_CAP 100000
#define STALL 3000
#define GMAX 6400
#define GW ((GMAX + 63) / 64)

static int d, D;
static long MOORE;
static double t_end, t_phase1;

static int N = 1, e_id = 0;
static int P = 1, half = 1, nd = 0;

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

static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y */
static int INV[MAXN];
static int pw_tmp[MAXN];
static int qg, gmode;
static int gmat[MAXN][4];
static int idxm[IDXM_CAP];
static int cache_type = -1, cache_a = 0, cache_b = 0, cache_c = 0;

static int finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    if (cache_type == 0 && cache_a == m && cache_b == k && cache_c == r) return 1;
    cache_type = -1;
    N = (int)n;
    pw_tmp[0] = 1 % m;
    for (int b = 1; b < k; b++) pw_tmp[b] = (int)((long)pw_tmp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw_tmp[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    if (!finish_inv()) return 0;
    cache_type = 0; cache_a = m; cache_b = k; cache_c = r;
    return 1;
}

static int enc4(int a, int b, int c, int e) {
    int q = qg;
    return ((a * q + b) * q + c) * q + e;
}

/* gmode 0 = SL(2,q), 1 = PSL(2,q) (scalars +-1), 2 = PGL(2,q) (all nonzero scalars). */
static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int best = enc4(a, b, c, e);
    if (gmode == 0) return best;
    if (gmode == 1) {
        int kk = enc4((q - a) % q, (q - b) % q, (q - c) % q, (q - e) % q);
        return kk < best ? kk : best;
    }
    for (int l = 2; l < q; l++) {
        int kk = enc4(a * l % q, b * l % q, c * l % q, e * l % q);
        if (kk < best) best = kk;
    }
    return best;
}

static int build_matrix(int q, int mode) {
    long ks = (long)q * q * q * q;
    if (ks > IDXM_CAP) return 0;
    if (cache_type == 1 && cache_a == q && cache_b == mode) return 1;
    cache_type = -1;
    qg = q;
    gmode = mode;
    for (int i = 0; i < (int)ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
    for (int b = 0; b < q; b++)
    for (int c = 0; c < q; c++)
    for (int e = 0; e < q; e++) {
        int det = (((a * e - b * c) % q) + q) % q;
        if (mode == 2) { if (det == 0) continue; }
        else if (det != 1) continue;
        int own = enc4(a, b, c, e);
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
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            int id = idxm[canon_key(pa, pb, pc, pe)];
            if (id < 0) return 0;
            T[(size_t)x * N + y] = (uint16_t)id;
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    if (e_id < 0) return 0;
    if (!finish_inv()) return 0;
    cache_type = 1; cache_a = q; cache_b = mode;
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;      /* 0 = metacyclic, 1 = matrix */
    int q, mode, m, k, r, N, P, tier;
    long V;        /* total vertices = 2 * P * N */
} Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->tier != y->tier) return x->tier - y->tier;
    return 0;
}

static void push_cand(const Cand *c) {
    if (nc < MAXCAND) CAND[nc++] = *c;
}

static void gen_candidates(long lowV, long hiV) {
    static const int qs[] = {5, 7, 11, 13, 17};
    nc = 0;
    for (int Pp = 1; Pp <= MAXP; Pp++)
        for (unsigned qi = 0; qi < 5; qi++)
            for (int mode = 0; mode < 3; mode++) {
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (mode == 1) o /= 2;
                long V = 2L * Pp * o;
                if (o > MAXN || V <= lowV || V > hiV || V > MOORE) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.mode = mode;
                c.N = (int)o;
                c.P = Pp;
                c.V = V;
                c.tier = 0;
                push_cand(&c);
            }
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
                    c.tier = 1;
                    push_cand(&c);
                }
                got++;
            }
        }
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->mode);
    if (!ok || N != c->N) return 0;
    P = c->P;
    half = P * N;
    return 1;
}

/* ------------------------------------------------------------------ voltage lift */

static int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXN];   /* FW[t][x] = x * g_t        */
static int BW[MAXDART][MAXN];   /* BW[t][y] = y * g_t^{-1}   */

static void set_dart(int t) {
    int g = vol[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        FW[t][x] = (int)T[(size_t)x * N + g];
        BW[t][x] = (int)T[(size_t)x * N + gi];
    }
}

static void build_lists(void) {
    int ca[MAXP], cb[MAXP];
    memset(ca, 0, sizeof ca);
    memset(cb, 0, sizeof cb);
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t];
        dA[i][ca[i]++] = t;
        dB[j][cb[j]++] = t;
    }
}

static int conflict(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

static int gen_base(void) {
    int M[MAXP][MAXP];
    int perm[MAXP];
    memset(M, 0, sizeof M);
    for (int c = 0; c < d; c++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) M[i][perm[i]]++;
    }
    nd = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++) {
            if (M[i][j] > N) return 0;
            for (int c = 0; c < M[i][j]; c++) {
                dI[nd] = i;
                dJ[nd] = j;
                nd++;
            }
        }
    build_lists();
    for (int t = 0; t < nd; t++) {
        int g = 0, tries = 0;
        do {
            g = rndint(N);
            tries++;
        } while (conflict(t, g, t) && tries < 100000);
        if (tries >= 100000) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

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
        int t = rndint(nd);
        int old = vol[t];
        int g = rndint(N);
        if (g == old || conflict(t, g, nd)) { stall++; continue; }
        vol[t] = g;
        set_dart(t);
        long nc2 = cost_now();
        if (nc2 <= cur || rnd01() < 0.01) {
            cur = nc2;
        } else {
            vol[t] = old;
            set_dart(t);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ explicit graph state */

static int gn = 0;
static int gadj[GMAX][MAXDEG];
static int gside[GMAX];
static int gfill[GMAX];
static int bak_adj[GMAX][MAXDEG];
static int bak_side[GMAX];
static uint64_t BUFA[GMAX * GW], BUFB[GMAX * GW];

/* Bit-parallel check: every vertex reaches every vertex within D steps. */
static int full_ok(int n) {
    if (n < 1 || n > GMAX) return 0;
    int W = (n + 63) / 64;
    uint64_t *cur = BUFA, *nxt = BUFB;
    for (int v = 0; v < n; v++) {
        uint64_t *row = cur + (size_t)v * GW;
        for (int w = 0; w < W; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * GW;
            const uint64_t *s = cur + (size_t)v * GW;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int k = 0; k < d; k++) {
                const uint64_t *z = cur + (size_t)gadj[v][k] * GW;
                for (int w = 0; w < W; w++) o[w] |= z[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    uint64_t lastmask = (n & 63) ? ((1ULL << (n & 63)) - 1) : ~0ULL;
    for (int v = 0; v < n; v++) {
        const uint64_t *s = cur + (size_t)v * GW;
        for (int w = 0; w < W - 1; w++)
            if (s[w] != ~0ULL) return 0;
        if (s[W - 1] != lastmask) return 0;
    }
    return 1;
}

static int export_lift(void) {
    int n = 2 * half;
    if (n > GMAX || n < 2) return 0;
    for (int v = 0; v < n; v++) gfill[v] = 0;
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++) {
            int v = i * N + x;
            for (int k = 0; k < d; k++) {
                int t = dA[i][k];
                int u = half + dJ[t] * N + FW[t][x];
                if (gfill[v] >= d || gfill[u] >= d) return 0;
                gadj[v][gfill[v]++] = u;
                gadj[u][gfill[u]++] = v;
            }
        }
    gn = n;
    for (int v = 0; v < n; v++) {
        gside[v] = (v >= half) ? 1 : 0;
        if (gfill[v] != d) return 0;
    }
    return 1;
}

/* Climb one candidate; on success replace the explicit state if the result is valid. */
static int try_lift(const Cand *c, double until) {
    if (!apply_cand(c)) return 0;
    if (!climb(until)) return 0;
    memcpy(bak_adj, gadj, sizeof gadj);
    memcpy(bak_side, gside, sizeof gside);
    int saved_n = gn;
    if (export_lift() && full_ok(gn)) return 1;
    memcpy(gadj, bak_adj, sizeof gadj);
    memcpy(gside, bak_side, sizeof gside);
    gn = saved_n;
    return 0;
}

static void init_kdd(void) {
    gn = 2 * d;
    for (int a = 0; a < d; a++)
        for (int k = 0; k < d; k++) {
            gadj[a][k] = d + k;
            gadj[d + k][a] = a;
        }
    for (int v = 0; v < gn; v++) gside[v] = (v >= d) ? 1 : 0;
}

static int has_nb(int v, int u) {
    for (int k = 0; k < d; k++)
        if (gadj[v][k] == u) return 1;
    return 0;
}

static void replace_in(int v, int old, int nw) {
    for (int k = 0; k < d; k++)
        if (gadj[v][k] == old) { gadj[v][k] = nw; return; }
}

/* Insert a new A-vertex a and B-vertex b; d removed edges (x_i,y_i) are rewired. */
static int try_insert(void) {
    if (gn + 2 > GMAX) return 0;
    int X[MAXDEG], Y[MAXDEG];
    int cnt = 0, tries = 0;
    while (cnt < d && tries < 400) {
        tries++;
        int x = rndint(gn);
        if (gside[x] != 0) continue;
        int y = gadj[x][rndint(d)];
        int ok = 1;
        for (int s = 0; s < cnt; s++)
            if (X[s] == x || Y[s] == y) { ok = 0; break; }
        if (!ok) continue;
        X[cnt] = x;
        Y[cnt] = y;
        cnt++;
    }
    if (cnt < d) return 0;
    int a = gn, b = gn + 1;
    for (int i = 0; i < d; i++) {
        replace_in(X[i], Y[i], b);
        replace_in(Y[i], X[i], a);
        gadj[a][i] = Y[i];
        gadj[b][i] = X[i];
    }
    gside[a] = 0;
    gside[b] = 1;
    gn += 2;
    if (full_ok(gn)) return 1;
    gn -= 2;
    for (int i = 0; i < d; i++) {
        replace_in(X[i], b, Y[i]);
        replace_in(Y[i], a, X[i]);
    }
    return 0;
}

/* Random 2-switch between A-vertices x1,x2: (x1,y1),(x2,y2) -> (x1,y2),(x2,y1). */
static int try_switch(void) {
    int x1 = -1, x2 = -1;
    for (int tries = 0; tries < 200 && (x1 < 0 || x2 < 0); tries++) {
        int v = rndint(gn);
        if (gside[v]) continue;
        if (x1 < 0) x1 = v;
        else if (v != x1) x2 = v;
    }
    if (x1 < 0 || x2 < 0) return 0;
    int k1 = rndint(d), k2 = rndint(d);
    int y1 = gadj[x1][k1], y2 = gadj[x2][k2];
    if (y1 == y2 || has_nb(x1, y2) || has_nb(x2, y1)) return 0;
    gadj[x1][k1] = y2;
    gadj[x2][k2] = y1;
    replace_in(y1, x1, x2);
    replace_in(y2, x2, x1);
    if (full_ok(gn)) return 1;
    gadj[x1][k1] = y1;
    gadj[x2][k2] = y2;
    replace_in(y1, x2, x1);
    replace_in(y2, x1, x2);
    return 0;
}

static void grow(void) {
    while (now() < t_end) {
        if (rnd01() < 0.5) try_insert();
        else try_switch();
    }
}

static void print_graph(void) {
    long m = 0;
    for (int v = 0; v < gn; v++)
        for (int k = 0; k < d; k++)
            if (gadj[v][k] > v) m++;
    printf("%d %ld\n", gn, m);
    for (int v = 0; v < gn; v++)
        for (int k = 0; k < d; k++)
            if (gadj[v][k] > v) printf("%d %d\n", v, gadj[v][k]);
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
    t_phase1 = t0 + 0.55 * usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 1) { printf("1 0\n"); return 0; }
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }

    MOORE = moore_bound();
    long lowV, hiV;
    if (ref <= 0) {
        lowV = 2L * d;
        hiV = MOORE;
    } else {
        lowV = (long)(0.87 * (double)ref);
        if (lowV < 2L * d) lowV = 2L * d;
        hiV = (long)(1.25 * (double)ref);
        if (hiV > MOORE) hiV = MOORE;
    }
    gen_candidates(lowV, hiV);

    /* Safe start: K_{d,d}, valid for D >= 2. */
    init_kdd();

    double budget1 = t_phase1 - now();
    long bestV = 0;

    /* Floor: SL(2,13), one base vertex (bi-Cayley, 4368 vertices for d = 4). */
    Cand fb;
    memset(&fb, 0, sizeof fb);
    fb.type = 1;
    fb.q = 13;
    fb.mode = 0;
    fb.N = 2184;
    fb.P = 1;
    fb.V = 2L * 2184;
    if (fb.V <= MOORE) {
        double slice = 0.3 * budget1;
        double rem = t_phase1 - now();
        if (slice > rem) slice = rem;
        if (slice > 0.2 && try_lift(&fb, now() + slice)) bestV = fb.V;
    }

    /* Ladder: ascending vertex count above the best lift found so far. */
    for (int i = 0; i < nc; i++) {
        if (now() > t_phase1) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV) continue;
        if (c->type == 1 && c->q == 13 && c->mode == 0 && c->P == 1) continue;
        double rem = t_phase1 - now();
        double slice = (c->type == 1 ? 0.2 : 0.05) * budget1;
        if (slice > rem) slice = rem;
        if (slice < 0.2) break;
        if (try_lift(c, now() + slice)) bestV = c->V;
    }

    /* Growth from the best valid graph found. */
    if (full_ok(gn)) grow();
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        ref = REF_VERTICES.get((d, D), best[0])
        for attempt in range(2):
            t_attempt = time.monotonic()
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed + attempt, round(budget, 3), ref],
                                 timeout=budget + 6)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
                break
            except Exception:
                # Retry once only if the failure came early and time remains.
                spent = time.monotonic() - t_attempt
                budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
                if spent > 0.5 * budget or budget < 15:
                    break
    return best
