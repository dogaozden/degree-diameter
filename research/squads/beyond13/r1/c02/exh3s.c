/* exh3s: early-exit, time-limited variant of research/frontier/beyond/cubic/exh3.c for H(G,{e,x,y}).
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
    if (argc < 4) { fprintf(stderr, "usage: exh3s TABLE.bin D OUTPREFIX [TLIM] [SAMPLE] [SEED]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { fprintf(stderr, "no table\n"); return 2; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 2; N = n32;
    T = malloc((size_t)N * N * 2); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    D = atoi(argv[2]);
    const char *outp = argv[3];
    double tlim = argc > 4 ? atof(argv[4]) : 90.0;
    int sample = argc > 5 ? atoi(argv[5]) : 0;
    unsigned seed = argc > 6 ? (unsigned)atoi(argv[6]) : 1u;
    srand(seed);
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
    for (int r = 0; r < nrep && fx < 0 && !timedout; r++) {
        int x = reps[r];
        int cnt = sample > 0 ? sample : N - 1;
        for (int j = 0; j < cnt; j++) {
            int y = sample > 0 ? 1 + rand() % (N - 1) : 1 + j;
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
