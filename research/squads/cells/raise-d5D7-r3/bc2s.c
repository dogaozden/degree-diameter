/* bc2s: orbit-symmetric annealing over bi-Cayley lifts with K orbits per side (see bc2.c for the graph and cost).
 *
 * Symmetry: alpha is an automorphism of G of order 3 (given as a permutation AUT of G).  The voltage sets are
 * unions of alpha-orbits: each block S[i][j] has M[i][j] orbits of size 3 and f[i][j] = DEG - 3 M fixed points.
 * Then alpha acts on the lift, (side,i,g) -> (side,i,alpha(g)), and the search space is the set of such unions.
 * Moves replace one orbit (or fixed point) of a block by another unit of the same size not yet in that block.
 * The identity is pinned as the first fixed point of S[0][0] (normalisation, as in bc2).
 *
 * Environment: GROUP, DEG, M, AUT (file with n integers), D (default 7), SECS, SEED, T0, T1, PHASE, PROGRESS, OUT.
 * Output line: RESULT ... best <cost> ... [FOUND].  Solution file as bc2 (bcheck.py reads it).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXDEG 16

static int K, n, D, Delta, V;
static int *mul, *inv_;
static int deg[MAXK][MAXK], m3[MAXK][MAXK], nfix[MAXK][MAXK];
static int BS[MAXK][MAXK][MAXDEG];           /* expanded element sets used by the BFS */
static int BU[MAXK][MAXK][MAXDEG];           /* unit ids: units 0..nfix_total-1 are fixed points, then 3-orbits */
static int nunits_fix, nunits3;
static int *unit_el;                         /* unit u: elements unit_el[3u..3u+2] (size 1 units use the first slot) */
static int *unit_sz;
static int *unit_of;                         /* element -> unit id */
static int *fixed_units, *orbit3_units;
static int32_t *mark, *queue;
static int32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int idslot_unit;                      /* unit id of the identity fixed point */

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void make_group(const char *spec) {
    char kind[16]; int a = 0;
    sscanf(spec, "%15s %d", kind, &a);
    if (!strcmp(kind, "file")) {
        char path[512]; sscanf(spec, "%*s %511s", path);
        FILE *f = fopen(path, "r");
        if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad group file\n"); exit(1); }
        mul = malloc(sizeof(int) * n * n); inv_ = malloc(sizeof(int) * n);
        for (int x = 0; x < n * n; x++) if (fscanf(f, "%d", &mul[x]) != 1) { fprintf(stderr, "short table\n"); exit(1); }
        fclose(f);
    } else { fprintf(stderr, "only file groups\n"); exit(1); }
    for (int x = 0; x < n; x++) {
        inv_[x] = -1;
        for (int y = 0; y < n; y++) if (mul[x * n + y] == 0) inv_[x] = y;
        if (inv_[x] < 0) { fprintf(stderr, "not a group\n"); exit(1); }
    }
}

/* Number of vertices at distance > D from source v0. */
static int far_from(int v0) {
    int head = 0, tail = 0, level_end;
    stamp++;
    mark[v0] = stamp; queue[tail++] = v0;
    for (int d = 0; d < D; d++) {
        level_end = tail;
        while (head < level_end) {
            int v = queue[head++];
            int side = v / (K * n), rem = v % (K * n), i = rem / n, g = rem % n;
            if (side == 0) {
                for (int j = 0; j < K; j++) for (int p = 0; p < deg[i][j]; p++) {
                    int w = ((K + j) * n) + mul[g * n + BS[i][j][p]];
                    if (mark[w] != stamp) { mark[w] = stamp; queue[tail++] = w; }
                }
            } else {
                for (int i2 = 0; i2 < K; i2++) for (int p = 0; p < deg[i2][i]; p++) {
                    int x = mul[g * n + inv_[BS[i2][i][p]]];
                    int w = i2 * n + x;
                    if (mark[w] != stamp) { mark[w] = stamp; queue[tail++] = w; }
                }
            }
        }
    }
    return V - tail;
}

static int cost(void) {
    int c = 0;
    for (int s = 0; s < 2; s++) for (int i = 0; i < K; i++) c += far_from((s * K + i) * n);
    return c;
}

/* expand the unit list of block (i,j) into BS */
static void expand(int i, int j) {
    int p = 0;
    for (int q = 0; q < m3[i][j] + nfix[i][j]; q++) {
        int u = BU[i][j][q];
        int sz = unit_sz[u];
        for (int t = 0; t < sz; t++) BS[i][j][p++] = unit_el[3 * u + t];
    }
}

static int unit_in_block(int i, int j, int u, int upto) {
    for (int q = 0; q < upto; q++) if (BU[i][j][q] == u) return 1;
    return 0;
}

int main(void) {
    const char *gs = getenv("GROUP"), *ds = getenv("DEG"), *ms = getenv("M"), *as = getenv("AUT");
    if (!gs || !ds || !ms || !as) { fprintf(stderr, "need GROUP DEG M AUT\n"); return 1; }
    make_group(gs);
    /* DEG and M: K*K integers */
    {
        int v[MAXK * MAXK], w[MAXK * MAXK], cv = 0, cw = 0; char buf[256];
        strncpy(buf, ds, 255); buf[255] = 0;
        for (char *tok = strtok(buf, " ,"); tok && cv < 16; tok = strtok(NULL, " ,")) v[cv++] = atoi(tok);
        strncpy(buf, ms, 255); buf[255] = 0;
        for (char *tok = strtok(buf, " ,"); tok && cw < 16; tok = strtok(NULL, " ,")) w[cw++] = atoi(tok);
        K = cv == 1 ? 1 : cv == 4 ? 2 : cv == 9 ? 3 : cv == 16 ? 4 : 0;
        if (!K || cw != cv) { fprintf(stderr, "DEG and M must be K*K integers\n"); return 1; }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
            deg[i][j] = v[i * K + j]; m3[i][j] = w[i * K + j];
            nfix[i][j] = deg[i][j] - 3 * m3[i][j];
            if (nfix[i][j] < 0) { fprintf(stderr, "M too large for DEG\n"); return 1; }
        }
        Delta = 0; for (int j = 0; j < K; j++) Delta += deg[0][j];
        for (int i = 0; i < K; i++) {
            int rs_ = 0, cs = 0;
            for (int j = 0; j < K; j++) { rs_ += deg[i][j]; cs += deg[j][i]; }
            if (rs_ != Delta || cs != Delta) { fprintf(stderr, "DEG not biregular\n"); return 1; }
        }
    }
    /* alpha: read the permutation and build its orbits */
    int *alpha = malloc(sizeof(int) * n);
    {
        FILE *f = fopen(as, "r");
        if (!f) { fprintf(stderr, "no AUT\n"); return 1; }
        for (int x = 0; x < n; x++) if (fscanf(f, "%d", &alpha[x]) != 1) { fprintf(stderr, "short AUT\n"); return 1; }
        fclose(f);
        for (int x = 0; x < n; x++) {
            int y = x, k = 0;
            do { y = alpha[y]; k++; } while (y != x && k <= 3);
            if (k != 1 && k != 3) { fprintf(stderr, "alpha does not have order dividing 3 (cycle %d)\n", k); return 1; }
        }
    }
    unit_of = malloc(sizeof(int) * n);
    unit_el = malloc(sizeof(int) * 3 * n);   /* at most n units */
    unit_sz = malloc(sizeof(int) * n);
    fixed_units = malloc(sizeof(int) * n);
    orbit3_units = malloc(sizeof(int) * n);
    nunits_fix = 0; nunits3 = 0;
    {
        int *seen = calloc(n, sizeof(int));
        int nu = 0;
        for (int x = 0; x < n; x++) if (!seen[x]) {
            int y = x, sz = 0; int els[3];
            do { els[sz++] = y; seen[y] = 1; y = alpha[y]; } while (y != x);
            int u = nu++;
            unit_sz[u] = sz;
            for (int t = 0; t < sz; t++) { unit_el[3 * u + t] = els[t]; unit_of[els[t]] = u; }
            if (sz == 1) fixed_units[nunits_fix++] = u; else orbit3_units[nunits3++] = u;
        }
        /* keep fixed units and 3-units in unit-id order; identity unit id */
        idslot_unit = unit_of[0];
        if (unit_sz[idslot_unit] != 1) { fprintf(stderr, "identity not fixed by alpha\n"); return 1; }
        free(seen);
    }
    if (nunits_fix == 0 && nunits3 == 0) return 1;

    V = 2 * K * n;
    mark = calloc(V, sizeof(int32_t));
    queue = malloc(sizeof(int32_t) * V);

    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60;
    rs ^= (uint64_t)(getenv("SEED") ? atoll(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long phase = getenv("PHASE") ? atol(getenv("PHASE")) : 100000;
    double progress = getenv("PROGRESS") ? atof(getenv("PROGRESS")) : 30;
    D = getenv("D") ? atoi(getenv("D")) : 7;
    const char *outp = getenv("OUT");

    /* random initial state: distinct units per block; identity pinned as the first fixed unit of block (0,0) */
    static int BUbest[MAXK][MAXK][MAXDEG];
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        int nu = m3[i][j] + nfix[i][j];
        for (int q = 0; q < nu; q++) {
            int u, tries = 0;
            do {
                if (q < m3[i][j]) {
                    if (nunits3 == 0) { fprintf(stderr, "no 3-orbits\n"); return 1; }
                    u = orbit3_units[rnd() % nunits3];
                } else {
                    u = fixed_units[rnd() % nunits_fix];
                }
                if (i == 0 && j == 0 && q == m3[0][0]) u = idslot_unit;
                tries++;
            } while (unit_in_block(i, j, u, q) && tries < 100000 && !(i == 0 && j == 0 && q == m3[0][0] && 0));
            BU[i][j][q] = u;
        }
        expand(i, j);
    }
    /* identity unit must sit in (0,0); if not in the first fixed slot, the pinned slot is q = m3[0][0] */
    if (nfix[0][0] == 0) { fprintf(stderr, "DEG(0,0) needs a fixed point for the identity\n"); return 1; }
    memcpy(BUbest, BU, sizeof(BU));

    int cur = cost(), best = cur, found = 0;
    double t_start = now(), t_prog = t_start;
    long steps = 0;
    fprintf(stderr, "K=%d n=%d D=%d Delta=%d V=%d fixed-units=%d orbit3-units=%d start cost %d\n",
            K, n, D, Delta, V, nunits_fix, nunits3, cur);

    int nb = 0; int bi[MAXK * MAXK], bj[MAXK * MAXK];
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (nfix[i][j] + m3[i][j] > 0) { bi[nb] = i; bj[nb] = j; nb++; }

    while (cur > 0) {
        double t_now = now();
        if (t_now - t_start > secs) break;
        if (t_now - t_prog > progress) {
            fprintf(stderr, "  t=%.0f steps=%ld cur=%d best=%d\n", t_now - t_start, steps, cur, best);
            t_prog = t_now;
        }
        double lf = log(T1 / T0);
        for (long s = 0; s < phase && cur > 0; s++) {
            if ((s & 4095) == 0 && now() - t_start > secs) break;
            double T = T0 * exp(lf * (double)s / (double)phase);
            int b = rnd() % nb; int i = bi[b], j = bj[b];
            int nu = m3[i][j] + nfix[i][j];
            int q = rnd() % nu;
            int is3 = q < m3[i][j];
            if (i == 0 && j == 0 && q == m3[0][0]) continue;   /* the identity slot */
            int old = BU[i][j][q], u, tries = 0;
            do {
                u = is3 ? orbit3_units[rnd() % nunits3] : fixed_units[rnd() % nunits_fix];
                tries++;
            } while ((unit_in_block(i, j, u, nu)) && tries < 1000);
            if (unit_in_block(i, j, u, nu)) continue;
            BU[i][j][q] = u;
            expand(i, j);
            int nc = cost();
            steps++;
            int delta = nc - cur;
            if (delta <= 0 || urand() < exp(-delta / T)) {
                cur = nc;
                if (cur < best) { best = cur; memcpy(BUbest, BU, sizeof(BU)); }
            } else {
                BU[i][j][q] = old;
                expand(i, j);
            }
        }
        memcpy(BU, BUbest, sizeof(BU));
        for (int a = 0; a < K; a++) for (int c = 0; c < K; c++) expand(a, c);
        cur = best;
        if (now() - t_start > secs) break;
    }

    double secs_used = now() - t_start;
    if (cur == 0) {
        found = 1;
        if (outp) {
            FILE *f = fopen(outp, "w");
            if (f) {
                fprintf(f, "%d %d %d %d\n", K, n, D, Delta);
                for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
                    fprintf(f, "%d", deg[i][j]);
                    for (int p = 0; p < deg[i][j]; p++) fprintf(f, " %d", BS[i][j][p]);
                    fprintf(f, "\n");
                }
                fclose(f);
            }
        }
    }
    printf("RESULT K %d n %d D %d Delta %d V %d best %d steps %ld secs %.1f%s\n",
           K, n, D, Delta, V, best, steps, secs_used, found ? " FOUND" : "");
    return 0;
}
