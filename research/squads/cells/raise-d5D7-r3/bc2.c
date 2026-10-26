/* bc2: simulated annealing over bi-Cayley (voltage) lifts with K orbits per side, for diameter D.
 *
 * Vertices (side, i, g): side 0 = A, 1 = B, i in [0,K), g in G (|G| = n, identity = 0).
 * Edges: (A,i,g) ~ (B,j,g*t) for t in S[i][j].  Left multiplication by G is an automorphism, so the
 * eccentricity of (side,i,g) equals that of (side,i,e).  The diameter is therefore the max over the 2K sources
 * (side,i,e).  Degrees: row sums and column sums of the degree matrix DEG all equal Delta.
 * Haar graphs are the K = 1 case.
 *
 * Cost = sum over the 2K sources of the number of vertices at distance > D.  Cost 0 <=> diameter <= D.
 * Normalisation: element 0 (the identity) is kept in S[0][0] (right-relabelling of the B_0 fibre).
 *
 * Environment:
 *   GROUP   "cyc n" or "file path" (m, then the m*m table, identity = 0)
 *   DEG     K*K integers, row-major, e.g. "1 4 4 1" (K = 2, Delta = 5)
 *   D       diameter target (default 7)
 *   SECS    wall-clock limit (default 60);  SEED (default 1)
 *   T0, T1  geometric cooling from T0 to T1 within each phase (defaults 2, 0.05)
 *   PHASE   steps per cooling phase (default 200000); each phase restarts from the best state seen so far
 *   OUT     solution file (written when cost 0);  IN  start from a solution file
 *   PROGRESS seconds between progress lines (default 30)
 * Solution file: "K n D Delta" line, then K*K lines "deg_ij t_1 ... t_deg".
 * Output line: RESULT K n D Delta V best <best cost> steps <steps> secs <secs> [FOUND]
 * usage: bc2   (all settings by env)
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
static int BS[MAXK][MAXK][MAXDEG], BSbest[MAXK][MAXK][MAXDEG];
static int32_t *mark, *queue;
static int32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void make_group(const char *spec) {
    char kind[16]; int a = 0;
    sscanf(spec, "%15s %d", kind, &a);
    if (!strcmp(kind, "cyc")) {
        n = a;
        mul = malloc(sizeof(int) * n * n);
        inv_ = malloc(sizeof(int) * n);
        for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) mul[x * n + y] = (x + y) % n;
    } else if (!strcmp(kind, "file")) {
        char path[512]; sscanf(spec, "%*s %511s", path);
        FILE *f = fopen(path, "r");
        if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad group file\n"); exit(1); }
        mul = malloc(sizeof(int) * n * n);
        inv_ = malloc(sizeof(int) * n);
        for (int x = 0; x < n * n; x++) if (fscanf(f, "%d", &mul[x]) != 1) { fprintf(stderr, "short table\n"); exit(1); }
        fclose(f);
    } else { fprintf(stderr, "unknown group\n"); exit(1); }
    for (int x = 0; x < n; x++) {
        inv_[x] = -1;
        for (int y = 0; y < n; y++) if (mul[x * n + y] == 0) inv_[x] = y;
        if (inv_[x] < 0) { fprintf(stderr, "not a group (no inverse)\n"); exit(1); }
    }
}

static int member(int i, int j, int t, int len) {
    for (int p = 0; p < len; p++) if (BS[i][j][p] == t) return 1;
    return 0;
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
                    /* B_i vertex g is adjacent to A_{i2} vertex g * t^-1 for t in S[i2][i] */
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
    }
}

int main(void) {
    const char *gs = getenv("GROUP");
    const char *ds = getenv("DEG");
    if (!gs || !ds) { fprintf(stderr, "need GROUP and DEG\n"); return 1; }
    make_group(gs);
    {
        int v[MAXK * MAXK]; int cnt = 0; char buf[256]; strncpy(buf, ds, 255); buf[255] = 0;
        char *tok = strtok(buf, " ,");
        while (tok && cnt < MAXK * MAXK) { v[cnt++] = atoi(tok); tok = strtok(NULL, " ,"); }
        K = 0;
        if (cnt == 1) K = 1; else if (cnt == 4) K = 2; else if (cnt == 9) K = 3; else if (cnt == 16) K = 4;
        if (!K || cnt != K * K) { fprintf(stderr, "DEG must be K*K integers\n"); return 1; }
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

    if (inp) {
        FILE *f = fopen(inp, "r");
        int kk, nn, dd, dl;
        if (!f || fscanf(f, "%d %d %d %d", &kk, &nn, &dd, &dl) != 4 || kk != K || nn != n) { fprintf(stderr, "bad IN\n"); return 1; }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
            int d; if (fscanf(f, "%d", &d) != 1 || d != deg[i][j]) { fprintf(stderr, "bad IN degrees\n"); return 1; }
            for (int p = 0; p < d; p++) if (fscanf(f, "%d", &BS[i][j][p]) != 1) { fprintf(stderr, "bad IN set\n"); return 1; }
        }
        fclose(f);
    } else random_state();
    memcpy(BSbest, BS, sizeof(BS));

    int cur = cost(), best = cur;
    int found = 0;
    double t_start = now(), t_prog = t_start;
    long steps = 0;
    fprintf(stderr, "K=%d n=%d D=%d Delta=%d V=%d start cost %d\n", K, n, D, Delta, V, cur);

    /* blocks that can move: all (i,j) with deg>0, excluding the fixed identity in S[0][0] */
    int nb = 0; int bi[MAXK * MAXK], bj[MAXK * MAXK];
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (deg[i][j] > 0) { bi[nb] = i; bj[nb] = j; nb++; }

    while (cur > 0) {
        double t_now = now();
        if (t_now - t_start > secs) break;
        if (t_now - t_prog > progress) {
            fprintf(stderr, "  t=%.0f steps=%ld cur=%d best=%d\n", t_now - t_start, steps, cur, best);
            t_prog = t_now;
        }
        /* one phase: geometric cooling from T0 to T1 */
        double T = T0, lf = log(T1 / T0);
        for (long s = 0; s < phase && cur > 0; s++) {
            if ((s & 4095) == 0 && now() - t_start > secs) break;
            T = T0 * exp(lf * (double)s / (double)phase);
            int b = rnd() % nb; int i = bi[b], j = bj[b];
            int d = deg[i][j];
            int p = rnd() % d;
            if (i == 0 && j == 0) { if (d == 1) continue; p = 1 + rnd() % (d - 1); }
            int old = BS[i][j][p], t;
            do { t = rnd() % n; } while (member(i, j, t, d) || (i == 0 && j == 0 && t == 0));
            BS[i][j][p] = t;
            int nc = cost();
            steps++;
            int delta = nc - cur;
            if (delta <= 0 || urand() < exp(-delta / T)) {
                cur = nc;
                if (cur < best) {
                    best = cur; memcpy(BSbest, BS, sizeof(BS));
                }
            } else {
                BS[i][j][p] = old;
            }
        }
        /* restart the next phase from the best state seen so far */
        memcpy(BS, BSbest, sizeof(BS));
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
