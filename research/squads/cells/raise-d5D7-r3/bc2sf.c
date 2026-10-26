/* bc2sf: bc2s (orbit-symmetric 2+2 annealing, see bc2s.c) with the bc2f speedups: adjacency columns per block
 * position, and pruned acceptance (the Metropolis threshold is drawn first; the cost is abandoned once it exceeds it).
 * Same environment, output line and solution format as bc2s.  Symmetry: AUT is an order-3 automorphism of G (a
 * permutation file, n integers), each block is a union of M[i][j] alpha-orbits of size 3 and DEG-3M fixed points.
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
static int BS[MAXK][MAXK][MAXDEG];   /* expanded elements of each block */
static int BU[MAXK][MAXK][MAXDEG];   /* unit ids of each block: first m3 are 3-orbits, then fixed points */
static int nunits_fix, nunits3, idslot_unit;
static int *unit_el, *unit_sz, *unit_of, *fixed_units, *orbit3_units;
static int *colA, *colB;             /* [((i*K+j)*MAXDEG + p) * n + x] */
static int32_t *mark, *queue;
static int32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void make_group(const char *spec) {
    char kind[16]; sscanf(spec, "%15s", kind);
    if (strcmp(kind, "file")) { fprintf(stderr, "only file groups\n"); exit(1); }
    char path[512]; sscanf(spec, "%*s %511s", path);
    FILE *f = fopen(path, "r");
    if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad group file\n"); exit(1); }
    mul = malloc(sizeof(int) * n * n); inv_ = malloc(sizeof(int) * n);
    for (int x = 0; x < n * n; x++) if (fscanf(f, "%d", &mul[x]) != 1) { fprintf(stderr, "short table\n"); exit(1); }
    fclose(f);
    for (int x = 0; x < n; x++) {
        inv_[x] = -1;
        for (int y = 0; y < n; y++) if (mul[x * n + y] == 0) inv_[x] = y;
        if (inv_[x] < 0) { fprintf(stderr, "not a group\n"); exit(1); }
    }
}

static void set_col(int i, int j, int p) {
    int t = BS[i][j][p], ti = inv_[t];
    int *cA = colA + ((i * K + j) * MAXDEG + p) * n;
    int *cB = colB + ((i * K + j) * MAXDEG + p) * n;
    for (int g = 0; g < n; g++) { cA[g] = mul[g * n + t]; cB[g] = mul[g * n + ti]; }
}

static void set_block(int i, int j) {
    int p = 0;
    for (int q = 0; q < m3[i][j] + nfix[i][j]; q++) {
        int u = BU[i][j][q];
        for (int t = 0; t < unit_sz[u]; t++) BS[i][j][p++] = unit_el[3 * u + t];
    }
    for (int q = 0; q < deg[i][j]; q++) set_col(i, j, q);
}

static int far_from_limited(int v0) {
    int head = 0, tail = 0, level_end;
    stamp++;
    mark[v0] = stamp; queue[tail++] = v0;
    for (int d = 0; d < D; d++) {
        level_end = tail;
        while (head < level_end) {
            int v = queue[head++];
            if (v < K * n) {
                int i = v / n, g = v % n;
                for (int j = 0; j < K; j++) for (int p = 0; p < deg[i][j]; p++) {
                    int w = K * n + j * n + colA[((i * K + j) * MAXDEG + p) * n + g];
                    if (mark[w] != stamp) { mark[w] = stamp; queue[tail++] = w; }
                }
            } else {
                int r = v - K * n, j = r / n, h = r % n;
                for (int i = 0; i < K; i++) for (int p = 0; p < deg[i][j]; p++) {
                    int w = i * n + colB[((i * K + j) * MAXDEG + p) * n + h];
                    if (mark[w] != stamp) { mark[w] = stamp; queue[tail++] = w; }
                }
            }
        }
    }
    return V - tail;
}

static int cost_limited(int limit) {
    int c = 0;
    for (int s = 0; s < 2 * K; s++) {
        c += far_from_limited(s * n);
        if (c > limit) return c;
    }
    return c;
}

static int unit_in_block(int i, int j, int u, int upto) {
    for (int q = 0; q < upto; q++) if (BU[i][j][q] == u) return 1;
    return 0;
}

int main(void) {
    const char *gs = getenv("GROUP"), *ds = getenv("DEG"), *ms = getenv("M"), *as = getenv("AUT");
    if (!gs || !ds || !ms || !as) { fprintf(stderr, "need GROUP DEG M AUT\n"); return 1; }
    make_group(gs);
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
    int *alpha = malloc(sizeof(int) * n);
    {
        FILE *f = fopen(as, "r");
        if (!f) { fprintf(stderr, "no AUT\n"); return 1; }
        for (int x = 0; x < n; x++) if (fscanf(f, "%d", &alpha[x]) != 1) { fprintf(stderr, "short AUT\n"); return 1; }
        fclose(f);
        for (int x = 0; x < n; x++) {
            int y = x, k = 0;
            do { y = alpha[y]; k++; } while (y != x && k <= 3);
            if (k != 1 && k != 3) { fprintf(stderr, "alpha does not have order dividing 3\n"); return 1; }
        }
    }
    unit_of = malloc(sizeof(int) * n);
    unit_el = malloc(sizeof(int) * 3 * n);
    unit_sz = malloc(sizeof(int) * n);
    fixed_units = malloc(sizeof(int) * n);
    orbit3_units = malloc(sizeof(int) * n);
    {
        int *seen = calloc(n, sizeof(int));
        int nu = 0;
        for (int x = 0; x < n; x++) if (!seen[x]) {
            int y = x, sz = 0, els[3];
            do { els[sz++] = y; seen[y] = 1; y = alpha[y]; } while (y != x);
            int u = nu++;
            unit_sz[u] = sz;
            for (int t = 0; t < sz; t++) { unit_el[3 * u + t] = els[t]; unit_of[els[t]] = u; }
            if (sz == 1) fixed_units[nunits_fix++] = u; else orbit3_units[nunits3++] = u;
        }
        idslot_unit = unit_of[0];
        if (unit_sz[idslot_unit] != 1) { fprintf(stderr, "identity not fixed by alpha\n"); return 1; }
        free(seen);
    }
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (m3[i][j] > 0 && nunits3 == 0) { fprintf(stderr, "no 3-orbits\n"); return 1; }
    if (nfix[0][0] == 0) { fprintf(stderr, "DEG(0,0) needs a fixed point for the identity\n"); return 1; }

    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60;
    rs ^= (uint64_t)(getenv("SEED") ? atoll(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long phase = getenv("PHASE") ? atol(getenv("PHASE")) : 100000;
    double progress = getenv("PROGRESS") ? atof(getenv("PROGRESS")) : 30;
    D = getenv("D") ? atoi(getenv("D")) : 7;
    const char *outp = getenv("OUT");

    V = 2 * K * n;
    mark = calloc(V, sizeof(int32_t));
    queue = malloc(sizeof(int32_t) * V);
    colA = malloc(sizeof(int) * K * K * MAXDEG * n);
    colB = malloc(sizeof(int) * K * K * MAXDEG * n);

    static int BUbest[MAXK][MAXK][MAXDEG];
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        int nu = m3[i][j] + nfix[i][j];
        for (int q = 0; q < nu; q++) {
            int u, tries = 0;
            do {
                if (i == 0 && j == 0 && q == m3[0][0]) u = idslot_unit;
                else if (q < m3[i][j]) u = orbit3_units[rnd() % nunits3];
                else u = fixed_units[rnd() % nunits_fix];
                tries++;
            } while (unit_in_block(i, j, u, q) && tries < 100000);
            BU[i][j][q] = u;
        }
        set_block(i, j);
    }
    memcpy(BUbest, BU, sizeof(BU));

    int cur = cost_limited(1 << 30), best = cur, found = 0;
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
            if (i == 0 && j == 0 && q == m3[0][0]) continue;
            int old = BU[i][j][q], u, tries = 0;
            do {
                u = is3 ? orbit3_units[rnd() % nunits3] : fixed_units[rnd() % nunits_fix];
                tries++;
            } while (unit_in_block(i, j, u, nu) && tries < 1000);
            if (unit_in_block(i, j, u, nu)) continue;
            double thr = cur - T * log(urand() + 1e-300);
            int limit = (int)floor(thr);
            BU[i][j][q] = u;
            set_block(i, j);
            int nc = cost_limited(limit);
            steps++;
            if (nc <= limit) {
                cur = nc;
                if (cur < best) { best = cur; memcpy(BUbest, BU, sizeof(BU)); }
            } else {
                BU[i][j][q] = old;
                set_block(i, j);
            }
        }
        memcpy(BU, BUbest, sizeof(BU));
        for (int a = 0; a < K; a++) for (int c = 0; c < K; c++) set_block(a, c);
        cur = best;
        if (now() - t_start > secs) break;
    }

    double secs_used = now() - t_start;
    if (cur == 0) {
        found = 1;
        for (int a = 0; a < K; a++) for (int c = 0; c < K; c++) set_block(a, c);
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
