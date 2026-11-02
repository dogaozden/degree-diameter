/* e02: exhaustive cubic Haar graphs H(G,{e,x,y}) for a group G given as a table (groups.py format).
 * Vertices (g,A)=g, (g,B)=N+g.  Edges (g,A)~(s g,B) for s in S={e,x,y}.  Left-multiplication by s is row s of T.
 * Right multiplication by G is an automorphism, transitive on each side, so diameter <= D iff the radius-D balls
 * around (e,A) and (e,B) cover everything.  cost = unreached(eA) + unreached(eB)  (0 iff diameter <= D).
 * Up to isomorphism x runs over conjugacy-class representatives (S -> c S c^-1 is an isomorphism), y over all others.
 * Usage: exh3 TABLE.bin D [OUTPREFIX]   (writes the first cost-0 edge list to OUTPREFIX_n<2N>.edges if given)
 * Output: one line per group: N, classes, pairs, min cost, #cost-0 pairs, best pair; then RESULT lines. */
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

/* BFS radius D from (e,side); returns number of reached vertices (both sides) */
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
            if (v < N) {               /* A vertex g -> B vertices s g */
                for (int i = 0; i < ns; i++) {
                    int b = T[(size_t)S[i] * N + v];
                    if (!visB[b]) { visB[b] = 1; nf[nn++] = N + b; reached++; }
                }
            } else {                   /* B vertex b -> A vertices s^-1 b */
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
    if (argc < 3) { fprintf(stderr, "usage: exh3 TABLE.bin D [OUTPREFIX]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { fprintf(stderr, "no table\n"); return 2; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 2; N = n32;
    T = malloc((size_t)N * N * 2); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    D = atoi(argv[2]);
    const char *outp = argc > 3 ? argv[3] : NULL;
    inv = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { inv[g] = h; break; }
    /* conjugacy class representatives of non-identity elements */
    unsigned char *mark = calloc(N, 1);
    int *reps = malloc(sizeof(int) * N); int nrep = 0;
    for (int g = 1; g < N; g++) {
        if (mark[g]) continue;
        reps[nrep++] = g;
        for (int h = 0; h < N; h++) {  /* h g h^-1 */
            int c = T[(size_t)T[(size_t)h * N + g] * N + inv[h]];
            mark[c] = 1;
        }
    }
    visA = malloc(N); visB = malloc(N); fr = malloc(sizeof(int) * 2 * N + 8); nf = malloc(sizeof(int) * 2 * N + 8);
    long long pairs = 0, zero = 0; int mincost = 1 << 30; int bx = -1, by = -1; long long hist_min_count = 0;
    int firstx = -1, firsty = -1;
    clock_t t0 = clock();
    int allx = getenv("ALLX") ? atoi(getenv("ALLX")) : 0;   /* 1: every x (cross-check of the class reduction) */
    if (allx) { nrep = 0; for (int g = 1; g < N; g++) reps[nrep++] = g; }
    for (int r = 0; r < nrep; r++) {
        int x = reps[r];
        for (int y = 1; y < N; y++) {
            if (y == x) continue;
            int S[3] = {0, x, y};
            int ra = ball(S, 3, 0), rb = ball(S, 3, 1);
            int cost = (2 * N - ra) + (2 * N - rb);
            pairs++;
            if (cost < mincost) { mincost = cost; bx = x; by = y; hist_min_count = 0; }
            if (cost == mincost) hist_min_count++;
            if (cost == 0) {
                zero++;
                if (firstx < 0) { firstx = x; firsty = y; }
            }
        }
    }
    printf("GROUP N=%d 2N=%d D=%d classes=%d pairs=%lld mincost=%d at (x=%d,y=%d) ties_at_min=%lld cost0_pairs=%lld secs=%.1f\n",
           N, 2 * N, D, nrep, pairs, mincost, bx, by, hist_min_count, zero, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (firstx >= 0) {
        printf("RESULT FOUND x=%d y=%d n=%d\n", firstx, firsty, 2 * N);
        if (outp) {
            char fn[512]; snprintf(fn, sizeof fn, "%s_n%d.edges", outp, 2 * N);
            FILE *o = fopen(fn, "w"); fprintf(o, "%d\n", 2 * N);
            int S[3] = {0, firstx, firsty};
            for (int i = 0; i < 3; i++) for (int g = 0; g < N; g++) fprintf(o, "%d %d\n", g, N + T[(size_t)S[i] * N + g]);
            fclose(o); printf("WROTE %s\n", fn);
        }
    } else printf("RESULT NONE\n");
    return 0;
}
