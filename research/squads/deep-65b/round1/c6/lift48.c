/* lift48.c (card c6): simulated annealing over voltage lifts of a 4+4 bipartite base with row and column sums 6.
 * Lift by a group G (table file, m then m rows of m ints, tab[g][h] = g*h, identity 0):
 *   vertices A_i,g = i*m+g (i<4), B_j,g = (4+j)*m+g; edges (A_i,g)-(B_j, g*v) for each v in V_ij, |V_ij| = M_ij, distinct.
 * The lift is bipartite, simple, 6-regular, n = 8m. G acts by left multiplication, so every sheet is vertex-transitive
 * under the automorphisms and it is enough to BFS from the 8 sheet identities (depth 5).
 * S = sum over the 8 identities of (#vertices at distance > 5); bad unordered pairs = m*S/2 (checked against score65).
 * usage: lift48 TAB M16 SEED SECONDS OUTPREFIX     (M16: 16 comma-separated ints, row = A_i, column = B_j)
 *        SECONDS < 0: one random state, writes OUTPREFIX.edges only (calibration against score65).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXM 256
#define MAXN (8*MAXM)
static int m, N;
static int tab[MAXM * MAXM];
static int inv_[MAXM];
static int Mx[4][4];
static int V[4][4][6], Vi[4][4][6];
static int bestV[4][4][6];
static int visst[MAXN], qb[MAXN], curst = 0;
static unsigned long long rs = 88172645463325252ULL;

static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int bfs_far(int src) {
    curst++;
    int head = 0, tail = 0;
    qb[tail++] = src; visst[src] = curst;
    for (int depth = 0; depth < 5 && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int x = qb[head++];
            int s = x / m, r = x - s * m;
            if (s < 4) {
                const int *row = tab + r * m;
                for (int j = 0; j < 4; j++)
                    for (int k = 0; k < Mx[s][j]; k++) {
                        int y = (4 + j) * m + row[V[s][j][k]];
                        if (visst[y] != curst) { visst[y] = curst; qb[tail++] = y; }
                    }
            } else {
                int j = s - 4;
                const int *row = tab + r * m;
                for (int i = 0; i < 4; i++)
                    for (int k = 0; k < Mx[i][j]; k++) {
                        int y = i * m + row[Vi[i][j][k]];
                        if (visst[y] != curst) { visst[y] = curst; qb[tail++] = y; }
                    }
            }
        }
    }
    return N - tail;
}

static long S_of(void) {
    long s = 0;
    for (int t = 0; t < 8; t++) s += bfs_far(t * m);
    return s;
}

static void set_inv(void) {
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) for (int k = 0; k < Mx[i][j]; k++)
        Vi[i][j][k] = inv_[V[i][j][k]];
}

static void random_init(void) {
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) for (int k = 0; k < Mx[i][j]; k++) {
        int w, ok;
        do {
            w = (int)(rnd() % m); ok = 1;
            for (int q = 0; q < k; q++) if (V[i][j][q] == w) ok = 0;
        } while (!ok);
        V[i][j][k] = w;
    }
    set_inv();
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    int ne = 0;
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) ne += Mx[i][j] * m;
    fprintf(f, "%d\n", N);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) for (int k = 0; k < Mx[i][j]; k++)
        for (int g = 0; g < m; g++)
            fprintf(f, "%d %d\n", i * m + g, (4 + j) * m + tab[g * m + V[i][j][k]]);
    fclose(f);
}

static void write_volt(const char *fn, long bad) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "m %d bad %ld\n", m, bad);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
        fprintf(f, "%d %d :", i, j);
        for (int k = 0; k < Mx[i][j]; k++) fprintf(f, " %d", V[i][j][k]);
        fprintf(f, "\n");
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lift48 TAB M16 SEED SECONDS OUTPREFIX\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) { fprintf(stderr, "bad table\n"); return 2; }
    for (int g = 0; g < m * m; g++) if (fscanf(f, "%d", &tab[g]) != 1) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    N = 8 * m;
    for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) if (tab[g * m + h] == 0) inv_[g] = h;
    {
        char buf[256]; strncpy(buf, argv[2], 255); buf[255] = 0;
        int idx = 0;
        for (char *p = strtok(buf, ","); p && idx < 16; p = strtok(NULL, ",")) { Mx[idx / 4][idx % 4] = atoi(p); idx++; }
        if (idx != 16) { fprintf(stderr, "M16 needs 16 entries\n"); return 2; }
        for (int a = 0; a < 4; a++) {
            int rs_ = 0, cs = 0;
            for (int b = 0; b < 4; b++) { rs_ += Mx[a][b]; cs += Mx[b][a]; }
            if (rs_ != 6 || cs != 6) { fprintf(stderr, "row/col sums must be 6\n"); return 2; }
        }
    }
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    for (int t = 0; t < 10; t++) rnd();
    double secs = atof(argv[4]);
    const char *out = argv[5];
    int pi[16], pj[16], np = 0;
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (Mx[i][j] > 0) { pi[np] = i; pj[np] = j; np++; }

    random_init();
    if (argc >= 7) {   /* optional INIT.volt from an earlier run (same group and base) */
        FILE *fi = fopen(argv[6], "r");
        int i, j, v0, nread = 0;
        if (fi) {
            char line[1024];
            if (!fgets(line, sizeof line, fi)) line[0] = 0;   /* header */
            while (fgets(line, sizeof line, fi)) {
                char *q = line; int off;
                if (sscanf(q, "%d %d :%n", &i, &j, &off) != 2) continue;
                q += off; int k = 0;
                while (k < Mx[i][j] && sscanf(q, "%d%n", &v0, &off) == 1) { V[i][j][k++] = v0; q += off; }
                nread++;
            }
            fclose(fi);
        }
        if (nread != np) { fprintf(stderr, "bad INIT file\n"); return 2; }
        set_inv();
    }
    if (secs < 0) {
        long S = S_of();
        char fn[512]; snprintf(fn, sizeof fn, "%s.edges", out);
        write_edges(fn);
        printf("CALIB seed=%llu m=%d n=%d S=%ld bad=%ld\n", seed, m, N, S, (long)m * S / 2);
        return 0;
    }

    long cur = S_of(), best = cur;
    memcpy(bestV, V, sizeof V);
    double t0 = now();
    double T0 = 3.0, T1 = 0.12;
    long epoch = 150000;
    if (getenv("T0")) T0 = atof(getenv("T0"));
    if (getenv("T1")) T1 = atof(getenv("T1"));
    if (getenv("EPOCH")) epoch = atol(getenv("EPOCH"));
    long iters = 0;
    int done = 0;
    while (!done) {
        for (long t = 0; t < epoch; t++) {
            double T = T0 * pow(T1 / T0, (double)t / (double)epoch);
            int p = (int)(rnd() % np), i = pi[p], j = pj[p];
            int k = (int)(rnd() % Mx[i][j]);
            int old = V[i][j][k], w, ok;
            do {
                w = (int)(rnd() % m); ok = 1;
                for (int q = 0; q < Mx[i][j]; q++) if (V[i][j][q] == w) ok = 0;
            } while (!ok);
            V[i][j][k] = w; Vi[i][j][k] = inv_[w];
            long nw = S_of();
            long d = nw - cur;
            iters++;
            if (d <= 0 || urand() < exp(-(double)d / T)) {
                cur = nw;
                if (cur < best) { best = cur; memcpy(bestV, V, sizeof V); }
            } else {
                V[i][j][k] = old; Vi[i][j][k] = inv_[old];
            }
            if (best == 0) { done = 1; break; }
            if ((iters & 1023) == 0 && now() - t0 > secs) { done = 1; break; }
        }
        /* restart each epoch from the best state */
        memcpy(V, bestV, sizeof V); set_inv(); cur = best;
        if (now() - t0 > secs) done = 1;
    }
    memcpy(V, bestV, sizeof V); set_inv();
    long Sb = S_of();
    long bad = (long)m * Sb / 2;
    char fn[512];
    snprintf(fn, sizeof fn, "%s.edges", out); write_edges(fn);
    snprintf(fn, sizeof fn, "%s.volt", out); write_volt(fn, bad);
    printf("RESULT seed=%llu m=%d n=%d bad=%ld S=%ld iters=%ld secs=%.1f\n", seed, m, N, bad, Sb, iters, now() - t0);
    return 0;
}
