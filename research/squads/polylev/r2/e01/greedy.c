/* e01: randomized greedy partial spread of totally singular lines of Q(6,11).
 *
 * Lines through a point p: pick the pivot k0 = first nonzero coordinate of p (normalised, p_k0 = 1).
 * Every totally singular line through p meets the hyperplane x_k0 = 0 in exactly one point y (besides p),
 * and conversely each singular y in x_k0 = 0 with b(p,y) = 0 gives the line {p} u {y + t p : t in F_11}.
 * Points are identified by a base-11 code of their normalised coordinates (first nonzero entry = 1);
 * PIDT maps code -> row id of research/theorems/polylev/hex/hex_q11.bin (the hexagon point ids).
 *
 * Usage: greedy HEXBIN SEED OUTTXT [TIMELIMIT_SEC]
 * Greedy: uncovered points in random order; a point with no free line through it is dead for good
 * (coverage only grows in this phase). Writes OUTTXT: one line per solution line, 12 point ids.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define Q 11
#define D 7
#define NMAX 177156
#define MAXLINES 16000
#define CODESZ 19487171 /* 11^7 */

static const int INV[Q] = {0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10};
static int POW[D];
static int N;
static uint8_t NRM[NMAX][D];
static int32_t *PIDT;
static int32_t *HK[D];
static int HN[D];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

/* code of the projective point of v (entries in 0..Q-1, not all zero) */
static inline int code_norm(const int *v) {
    int f = 0;
    while (v[f] == 0) f++;
    int c = INV[v[f]];
    int code = 0;
    for (int j = 0; j < D; j++) code += (v[j] * c % Q) * POW[j];
    return code;
}

static inline int bform(const uint8_t *x, const uint8_t *y) {
    int s = x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3];
    s %= Q;
    if (s < 0) s += Q;
    return s;
}

/* pid of the j-th point (j = 0..Q-1) of the line through p with hyperplane point y; j = Q means p itself */
static inline int line_point(int p, int y, int t) {
    int v[D];
    for (int j = 0; j < D; j++) v[j] = (NRM[y][j] + t * NRM[p][j]) % Q;
    return PIDT[code_norm(v)];
}

static int32_t OWN[NMAX];
static int32_t LP[MAXLINES][Q + 1];
static int K = 0;
static uint8_t DEAD[NMAX];

static int32_t freeY[2000];

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: greedy HEXBIN SEED OUTTXT [TIMELIMIT]\n");
        return 1;
    }
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    double tlim = argc > 4 ? atof(argv[4]) : 1e9;
    clock_t t0 = clock();
    time_t w0 = time(NULL);

    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("hex"); return 1; }
    int hdr[3];
    if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0];
    N = hdr[1];
    int L = hdr[2];
    if (q != Q || N > NMAX) { fprintf(stderr, "bad file\n"); return 1; }
    fseek(f, 12 + 4L * L * (Q + 1), SEEK_SET);
    uint8_t *raw = malloc((size_t)N * D);
    if (fread(raw, 1, (size_t)N * D, f) != (size_t)N * D) return 1;
    fclose(f);

    POW[0] = 1;
    for (int j = 1; j < D; j++) POW[j] = POW[j - 1] * Q;

    /* normalise rows (first nonzero -> 1) and sanity check Q(x) = 0 */
    for (int i = 0; i < N; i++) {
        int v[D];
        for (int j = 0; j < D; j++) v[j] = raw[i * D + j];
        int f0 = 0;
        while (v[f0] == 0) f0++;
        int c = INV[v[f0]];
        for (int j = 0; j < D; j++) NRM[i][j] = (uint8_t)(v[j] * c % Q);
        int qq = (NRM[i][0] * NRM[i][4] + NRM[i][1] * NRM[i][5] + NRM[i][2] * NRM[i][6] - NRM[i][3] * NRM[i][3]) % Q;
        if (qq < 0) qq += Q;
        if (qq != 0) { fprintf(stderr, "point %d not singular\n", i); return 1; }
    }
    free(raw);

    PIDT = malloc(sizeof(int32_t) * (size_t)CODESZ);
    memset(PIDT, 0xff, sizeof(int32_t) * (size_t)CODESZ);
    for (int i = 0; i < N; i++) {
        int v[D];
        for (int j = 0; j < D; j++) v[j] = NRM[i][j];
        int cd = code_norm(v);
        if (PIDT[cd] != -1) { fprintf(stderr, "duplicate point\n"); return 1; }
        PIDT[cd] = i;
    }
    for (int k = 0; k < D; k++) {
        HK[k] = malloc(sizeof(int32_t) * N);
        HN[k] = 0;
        for (int i = 0; i < N; i++)
            if (NRM[i][k] == 0) HK[k][HN[k]++] = i;
    }
    fprintf(stderr, "loaded N=%d, |H_k|=%d, setup %.1fs\n", N, HN[0], (double)(clock() - t0) / CLOCKS_PER_SEC);

    /* sanity: lines through a point */
    {
        int p = 0;
        int k0 = 0;
        while (NRM[p][k0] == 0) k0++;
        int cnt = 0;
        for (int a = 0; a < HN[k0]; a++)
            if (bform(NRM[p], NRM[HK[k0][a]]) == 0) cnt++;
        fprintf(stderr, "sanity: lines through point 0 = %d (expect 1464)\n", cnt);
    }

    for (int i = 0; i < N; i++) OWN[i] = -1;

    /* random order of points */
    int32_t *perm = malloc(sizeof(int32_t) * N);
    for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint64_t)(i + 1));
        int32_t tmp = perm[i];
        perm[i] = perm[j];
        perm[j] = tmp;
    }

    long processed = 0;
    for (int idx = 0; idx < N; idx++) {
        int p = perm[idx];
        if (OWN[p] >= 0 || DEAD[p]) continue;
        if (K >= MAXLINES) break;
        if ((idx & 1023) == 0 && difftime(time(NULL), w0) > tlim) {
            fprintf(stderr, "time limit reached at idx %d\n", idx);
            break;
        }
        processed++;
        int k0 = 0;
        while (NRM[p][k0] == 0) k0++;
        int nfree = 0;
        for (int a = 0; a < HN[k0]; a++) {
            int y = HK[k0][a];
            if (bform(NRM[p], NRM[y]) != 0) continue;
            int ok = 1;
            if (OWN[p] >= 0) ok = 0;
            for (int t = 0; t < Q && ok; t++)
                if (OWN[line_point(p, y, t)] >= 0) ok = 0;
            if (ok) freeY[nfree++] = y;
        }
        if (nfree == 0) { DEAD[p] = 1; continue; }
        int y = freeY[rnd() % (uint64_t)nfree];
        LP[K][Q] = p;
        OWN[p] = K;
        for (int t = 0; t < Q; t++) {
            int pt = line_point(p, y, t);
            LP[K][t] = pt;
            OWN[pt] = K;
        }
        K++;
        if (K % 1000 == 0) fprintf(stderr, "K=%d processed=%ld idx=%d time=%.0fs\n", K, processed, idx,
                                   (double)(clock() - t0) / CLOCKS_PER_SEC);
    }

    int uncovered = 0;
    for (int i = 0; i < N; i++) if (OWN[i] < 0) uncovered++;
    fprintf(stderr, "K=%d lines, covered %d of %d points (%.2f%%), uncovered %d, bound %d, time %.1fs\n", K,
            N - uncovered, N, 100.0 * (N - uncovered) / N, uncovered, N / (Q + 1),
            (double)(clock() - t0) / CLOCKS_PER_SEC);
    FILE *o = fopen(argv[3], "w");
    for (int l = 0; l < K; l++) {
        for (int t = 0; t <= Q; t++) fprintf(o, "%d%c", LP[l][t], t == Q ? '\n' : ' ');
    }
    fclose(o);
    printf("%d\n", K);
    return 0;
}
