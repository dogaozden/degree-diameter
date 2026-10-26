/* bc2f: bc2 (same CLI, same cost, same solution format) with two speedups that do not change the search:
 *   - adjacency tables colA[i][j][p][g] = index of the B_j neighbour of (A_i, g) through position p, and
 *     colB[i][j][p][h] = index of the A_i neighbour of (B_j, h); a move rebuilds only its own position (2n lookups);
 *   - pruned acceptance: the Metropolis threshold of a move is drawn before the move is evaluated, and the cost is
 *     summed source by source and abandoned as soon as it exceeds that threshold (the rejected candidate needs no
 *     exact value).  Accepted moves are evaluated exactly.
 * Trajectories differ from bc2 only through the random stream (the threshold is drawn first); the cost is exact.
 * Environment as in bc2.  Output line as bc2.
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
static int deg[MAXK][MAXK];
static int BS[MAXK][MAXK][MAXDEG];
static int *colA, *colB;          /* [((i*K+j)*MAXDEG + p) * n + x] */
static int32_t *mark, *queue;
static int32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void make_group(const char *spec) {
    char kind[16]; int a = 0;
    sscanf(spec, "%15s %d", kind, &a);
    if (!strcmp(kind, "cyc")) {
        n = a;
        mul = malloc(sizeof(int) * n * n); inv_ = malloc(sizeof(int) * n);
        for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) mul[x * n + y] = (x + y) % n;
    } else if (!strcmp(kind, "file")) {
        char path[512]; sscanf(spec, "%*s %511s", path);
        FILE *f = fopen(path, "r");
        if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad group file\n"); exit(1); }
        mul = malloc(sizeof(int) * n * n); inv_ = malloc(sizeof(int) * n);
        for (int x = 0; x < n * n; x++) if (fscanf(f, "%d", &mul[x]) != 1) { fprintf(stderr, "short table\n"); exit(1); }
        fclose(f);
    } else { fprintf(stderr, "unknown group\n"); exit(1); }
    for (int x = 0; x < n; x++) {
        inv_[x] = -1;
        for (int y = 0; y < n; y++) if (mul[x * n + y] == 0) inv_[x] = y;
        if (inv_[x] < 0) { fprintf(stderr, "not a group\n"); exit(1); }
    }
}

/* Position p of block (i,j) holds element t: rebuild its adjacency columns. */
static void set_col(int i, int j, int p) {
    int t = BS[i][j][p], ti = inv_[t];
    int *cA = colA + ((i * K + j) * MAXDEG + p) * n;
    int *cB = colB + ((i * K + j) * MAXDEG + p) * n;
    for (int g = 0; g < n; g++) {
        cA[g] = mul[g * n + t];          /* (A_i,g) ~ (B_j, g t) */
        cB[g] = mul[g * n + ti];         /* (B_j,g) ~ (A_i, g t^-1) */
    }
}

/* Vertices: A_i element g is i*n+g; B_j element h is K*n + j*n + h. */
static int far_from_limited(int v0, int limit) {
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
    (void)limit;
    return V - tail;
}

/* Exact cost, or a value > limit as soon as the partial sum exceeds limit. */
static int cost_limited(int limit) {
    int c = 0;
    for (int s = 0; s < 2 * K; s++) {
        c += far_from_limited(s * n, limit);
        if (c > limit) return c;
    }
    return c;
}

static int in_block(int i, int j, int t) {
    for (int q = 0; q < deg[i][j]; q++) if (BS[i][j][q] == t) return 1;
    return 0;
}

static void random_state(void) {
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        int d = deg[i][j];
        for (int p = 0; p < d; p++) {
            int t, ok;
            do {
                t = rnd() % n; ok = 1;
                if (i == 0 && j == 0 && p == 0) t = 0;
                for (int q = 0; q < p; q++) if (BS[i][j][q] == t) ok = 0;
                if (i == 0 && j == 0 && p > 0 && t == 0) ok = 0;
            } while (!ok);
            BS[i][j][p] = t;
        }
        for (int p = 0; p < d; p++) set_col(i, j, p);
    }
}

int main(void) {
    const char *gs = getenv("GROUP"), *ds = getenv("DEG");
    if (!gs || !ds) { fprintf(stderr, "need GROUP and DEG\n"); return 1; }
    make_group(gs);
    {
        int v[MAXK * MAXK], cnt = 0; char buf[256];
        strncpy(buf, ds, 255); buf[255] = 0;
        for (char *tok = strtok(buf, " ,"); tok && cnt < MAXK * MAXK; tok = strtok(NULL, " ,")) v[cnt++] = atoi(tok);
        K = cnt == 1 ? 1 : cnt == 4 ? 2 : cnt == 9 ? 3 : cnt == 16 ? 4 : 0;
        if (!K) { fprintf(stderr, "DEG must be K*K integers\n"); return 1; }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) deg[i][j] = v[i * K + j];
        Delta = 0; for (int j = 0; j < K; j++) Delta += deg[0][j];
        for (int i = 0; i < K; i++) {
            int rs_ = 0, cs = 0;
            for (int j = 0; j < K; j++) { rs_ += deg[i][j]; cs += deg[j][i]; }
            if (rs_ != Delta || cs != Delta) { fprintf(stderr, "DEG not biregular\n"); return 1; }
        }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (deg[i][j] > MAXDEG) { fprintf(stderr, "deg too big\n"); return 1; }
    }
    D = getenv("D") ? atoi(getenv("D")) : 7;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60;
    rs ^= (uint64_t)(getenv("SEED") ? atoll(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long phase = getenv("PHASE") ? atol(getenv("PHASE")) : 200000;
    double progress = getenv("PROGRESS") ? atof(getenv("PROGRESS")) : 30;
    const char *outp = getenv("OUT");
    const char *inp = getenv("IN");

    V = 2 * K * n;
    mark = calloc(V, sizeof(int32_t));
    queue = malloc(sizeof(int32_t) * V);
    colA = malloc(sizeof(int) * K * K * MAXDEG * n);
    colB = malloc(sizeof(int) * K * K * MAXDEG * n);

    static int BSbest[MAXK][MAXK][MAXDEG];
    if (inp) {
        FILE *f = fopen(inp, "r");
        int kk, nn, dd, dl;
        if (!f || fscanf(f, "%d %d %d %d", &kk, &nn, &dd, &dl) != 4 || kk != K || nn != n) { fprintf(stderr, "bad IN\n"); return 1; }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
            int d; if (fscanf(f, "%d", &d) != 1 || d != deg[i][j]) { fprintf(stderr, "bad IN degrees\n"); return 1; }
            for (int p = 0; p < d; p++) if (fscanf(f, "%d", &BS[i][j][p]) != 1) { fprintf(stderr, "bad IN set\n"); return 1; }
            for (int p = 0; p < d; p++) set_col(i, j, p);
        }
        fclose(f);
    } else random_state();
    memcpy(BSbest, BS, sizeof(BS));

    int cur = cost_limited(1 << 30), best = cur;
    int found = 0;
    double t_start = now(), t_prog = t_start;
    long steps = 0;
    fprintf(stderr, "K=%d n=%d D=%d Delta=%d V=%d start cost %d\n", K, n, D, Delta, V, cur);

    int nb = 0; int bi[MAXK * MAXK], bj[MAXK * MAXK];
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (deg[i][j] > 0) { bi[nb] = i; bj[nb] = j; nb++; }

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
            int d = deg[i][j];
            int p = rnd() % d;
            if (i == 0 && j == 0) { if (d == 1) continue; p = 1 + rnd() % (d - 1); }
            int old = BS[i][j][p], t;
            do { t = rnd() % n; } while (in_block(i, j, t) || (i == 0 && j == 0 && t == 0));
            /* Metropolis threshold drawn first: accept iff new cost <= thr */
            double thr = cur - T * log(urand() + 1e-300);
            int limit = (int)floor(thr);
            BS[i][j][p] = t;
            set_col(i, j, p);
            int nc = cost_limited(limit);
            steps++;
            if (nc <= limit) {
                cur = nc;
                if (cur < best) { best = cur; memcpy(BSbest, BS, sizeof(BS)); }
            } else {
                BS[i][j][p] = old;
                set_col(i, j, p);
            }
        }
        /* restart the next phase from the best state seen so far */
        memcpy(BS, BSbest, sizeof(BS));
        for (int a = 0; a < K; a++) for (int c = 0; c < K; c++) for (int q = 0; q < deg[a][c]; q++) set_col(a, c, q);
        cur = best;
        if (now() - t_start > secs) break;
    }

    double secs_used = now() - t_start;
    if (cur == 0) {
        memcpy(BS, BSbest, sizeof(BS));
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
