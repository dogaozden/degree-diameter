/* exh3m: exh3s with the metacyclic table Z_m x|_r Z_k built in C (element (a,j) = a + m*j).
 * exh3m m k r D OUTPREFIX [TLIM=90] [SAMPLE=0] [SEED=1]
 * exh3s: early-exit, time-limited variant of research/frontier/beyond/cubic/exh3.c for H(G,{e,x,y}).
 * Same cost definition (0 iff diameter <= D). Differences: (1) ball from (e,A) computed first; the ball from (e,B)
 * is only computed if the first covers everything; (2) stops at the first cost-0 pair and writes its edge list;
 * (3) TLIM seconds wall limit; (4) SAMPLE>0: y sampled uniformly (SAMPLE values per x) instead of all y.
 * Usage: exh3s TABLE.bin D OUTPREFIX [TLIM=90] [SAMPLE=0] [SEED=1]
 * Output: GROUP line (N, reps, pairs tested, cost0 found, secs) and RESULT FOUND x y n / RESULT NONE / RESULT TIMEOUT. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int N, D;
static uint16_t *T;
static int *inv;
static unsigned char *visA, *visB;
static int *fr, *nf;

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int ball(const int *S, int ns, int startside) {
    int reached = 0;
    memset(visA, 0, N); memset(visB, 0, N);
    int nfr = 0;
    if (startside == 0) { visA[0] = 1; fr[nfr++] = 0; } else { visB[0] = 1; fr[nfr++] = N; }
    reached = 1;
    int sinv[3];
    for (int i = 0; i < ns; i++) sinv[i] = inv[S[i]];
    for (int lev = 0; lev < D && nfr > 0; lev++) {
        int nn = 0;
        for (int k = 0; k < nfr; k++) {
            int v = fr[k];
            if (v < N) {
                for (int i = 0; i < ns; i++) {
                    int b = T[(size_t)S[i] * N + v];
                    if (!visB[b]) { visB[b] = 1; nf[nn++] = N + b; reached++; }
                }
            } else {
                int b = v - N;
                for (int i = 0; i < ns; i++) {
                    int a = T[(size_t)sinv[i] * N + b];
                    if (!visA[a]) { visA[a] = 1; nf[nn++] = a; reached++; }
                }
            }
        }
        int *t = fr; fr = nf; nf = t; nfr = nn;
    }
    return reached;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: exh3m m k r D OUTPREFIX [TLIM] [SAMPLE] [SEED]\n"); return 2; }
    int m = atoi(argv[1]), k = atoi(argv[2]), r = atoi(argv[3]);
    N = m * k;
    D = atoi(argv[4]);
    const char *outp = argv[5];
    double tlim = argc > 6 ? atof(argv[6]) : 90.0;
    int sample = argc > 7 ? atoi(argv[7]) : 0;
    unsigned seed = argc > 8 ? (unsigned)atoi(argv[8]) : 1u;
    srand(seed);
    int *rp = malloc(sizeof(int) * k); rp[0] = 1 % m;
    for (int j = 1; j < k; j++) rp[j] = (int)((long long)rp[j - 1] * r % m);
    if ((long long)rp[k - 1] * r % m != 1 % m) { printf("BADR\n"); return 2; }
    T = malloc((size_t)N * N * 2);
    for (int g1 = 0; g1 < N; g1++) {
        int a1 = g1 % m, j1 = g1 / m;
        for (int g2 = 0; g2 < N; g2++) {
            int a2 = g2 % m, j2 = g2 / m;
            int a = (int)((a1 + (long long)rp[j1] * a2) % m), j = (j1 + j2) % k;
            T[(size_t)g1 * N + g2] = (uint16_t)(a + m * j);
        }
    }
    inv = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { inv[g] = h; break; }
    unsigned char *mark = calloc(N, 1);
    int *reps = malloc(sizeof(int) * N); int nrep = 0;
    for (int g = 1; g < N; g++) {
        if (mark[g]) continue;
        reps[nrep++] = g;
        for (int h = 0; h < N; h++) { int c = T[(size_t)T[(size_t)h * N + g] * N + inv[h]]; mark[c] = 1; }
    }
    visA = malloc(N); visB = malloc(N); fr = malloc(sizeof(int) * 2 * N + 8); nf = malloc(sizeof(int) * 2 * N + 8);
    double t0 = now();
    long long pairs = 0, zero = 0; int fx = -1, fy = -1; int timedout = 0;
    if (sample > 0) {  /* total of SAMPLE random pairs (random class rep x, random y) */
        for (long long it = 0; it < sample && fx < 0; it++) {
            int x = reps[rand() % nrep];
            int y = 1 + rand() % (N - 1);
            if (y == x) continue;
            int S[3] = {0, x, y};
            pairs++;
            int ra = ball(S, 3, 0);
            if (ra == 2 * N) { int rb = ball(S, 3, 1); if (rb == 2 * N) { zero++; fx = x; fy = y; } }
            if ((it & 255) == 0 && now() - t0 > tlim) { timedout = 1; break; }
        }
    } else {
    for (int r = 0; r < nrep && fx < 0 && !timedout; r++) {
        int x = reps[r];
        for (int y = 1; y < N; y++) {
            if (y == x) continue;
            int S[3] = {0, x, y};
            pairs++;
            int ra = ball(S, 3, 0);
            if (ra == 2 * N) {
                int rb = ball(S, 3, 1);
                if (rb == 2 * N) { zero++; if (fx < 0) { fx = x; fy = y; break; } }
            }
            if ((pairs & 1023) == 0 && now() - t0 > tlim) { timedout = 1; break; }
        }
    }
    }
    printf("GROUP N=%d 2N=%d D=%d reps=%d pairs=%lld cost0=%lld secs=%.1f sample=%d\n",
           N, 2 * N, D, nrep, pairs, zero, now() - t0, sample);
    if (fx >= 0) {
        char fn[512]; snprintf(fn, sizeof fn, "%s_n%d.edges", outp, 2 * N);
        FILE *o = fopen(fn, "w"); fprintf(o, "%d\n", 2 * N);
        int S[3] = {0, fx, fy};
        for (int i = 0; i < 3; i++) for (int g = 0; g < N; g++) fprintf(o, "%d %d\n", g, N + T[(size_t)S[i] * N + g]);
        fclose(o);
        printf("RESULT FOUND x=%d y=%d n=%d file=%s\n", fx, fy, 2 * N, fn);
    } else printf("RESULT %s\n", timedout ? "TIMEOUT" : "NONE");
    return 0;
}
