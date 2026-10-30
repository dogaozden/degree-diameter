/* dcenum.c: exhaustive search over bi-coset graphs exported by dc_export.g.
 * Input (.dc): "nA nB ndc", then per double coset "contrib nedges" and its edges "a b" (A-point, B-point).
 * Every union S of double cosets with total contribution DELTA gives a DELTA-regular bipartite graph on nA + nB
 * vertices (|H| = |K|). G is transitive on each side, so diameter <= D iff the A-point 0 and the B-point 0 both
 * reach every vertex within D. Cost = number of vertices missed by the two BFS. Prints the best cost and every
 * cost-0 union, and writes the first cost-0 graph (or the best one) as an edge list.
 * usage: dcenum FILE.dc DELTA [D=5] [OUT.edges] [MAXSETS]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int nA, nB, ndc, DELTA, D = 5;
static int quiet = 0;
static int *contrib, *nE, **EA, **EB;
static int chosen[64], nch;
static long long tested = 0, nsol = 0, maxsets = 0;
static long bestcost = 1L << 40;
static int bestset[64], nbest;
static int *adj, *deg;   /* vertices 0..nA-1 A, nA..nA+nB-1 B */
static int *dist, *q;
static const char *outpath;

static int bfs(int s) {
    int n = nA + nB; for (int i = 0; i < n; i++) dist[i] = -1;
    int h = 0, t = 0; dist[s] = 0; q[t++] = s;
    while (h < t) { int x = q[h++]; if (dist[x] == D) continue;
        for (int i = 0; i < deg[x]; i++) { int y = adj[x * DELTA + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
    return n - t;
}
static void write_graph(int *set, int k) {
    if (!outpath) return;
    FILE *f = fopen(outpath, "w"); fprintf(f, "%d\n", nA + nB);
    for (int j = 0; j < k; j++) { int d = set[j]; for (int e = 0; e < nE[d]; e++) fprintf(f, "%d %d\n", EA[d][e], nA + EB[d][e]); }
    fclose(f);
}
static void test(void) {
    tested++;
    int n = nA + nB; memset(deg, 0, sizeof(int) * n);
    for (int j = 0; j < nch; j++) { int d = chosen[j];
        for (int e = 0; e < nE[d]; e++) { int a = EA[d][e], b = nA + EB[d][e];
            if (deg[a] >= DELTA || deg[b] >= DELTA) { fprintf(stderr, "degree overflow\n"); exit(1); }
            adj[a * DELTA + deg[a]++] = b; adj[b * DELTA + deg[b]++] = a; } }
    long c = bfs(0); c += bfs(nA);
    if (c < bestcost) { bestcost = c; nbest = nch; memcpy(bestset, chosen, sizeof(int) * nch); if (!nsol && !quiet) write_graph(chosen, nch); }
    if (c == 0) { nsol++; printf("SOL"); for (int j = 0; j < nch; j++) printf(" %d", chosen[j]); printf("\n"); fflush(stdout);
        if (nsol == 1) write_graph(chosen, nch); }
}
static void rec(int start, int left) {
    if (maxsets && tested >= maxsets) return;
    if (left == 0) { test(); return; }
    for (int d = start; d < ndc; d++) if (contrib[d] <= left) { chosen[nch++] = d; rec(d + 1, left - contrib[d]); nch--; }
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    DELTA = atoi(argv[2]); if (argc > 3) D = atoi(argv[3]); if (argc > 4) outpath = argv[4]; if (argc > 5) maxsets = atoll(argv[5]);
    int len = strlen(argv[1]);
    if (len > 4 && !strcmp(argv[1] + len - 4, ".dc2")) {
        FILE *f = fopen(argv[1], "r"); int ng; if (!f || fscanf(f, "%d %d %d %d", &nA, &nB, &ng, &ndc) != 4) return 2;
        int **gA = malloc(sizeof(int *) * ng), **gB = malloc(sizeof(int *) * ng);
        for (int s = 0; s < ng; s++) { gA[s] = malloc(sizeof(int) * nA); gB[s] = malloc(sizeof(int) * nB);
            for (int a = 0; a < nA; a++) if (fscanf(f, "%d", &gA[s][a]) != 1) return 2;
            for (int b = 0; b < nB; b++) if (fscanf(f, "%d", &gB[s][b]) != 1) return 2; }
        /* Schreier tree on A-points: permB[a] = B-image map of an element sending A-point 0 to a */
        int *permB = malloc(sizeof(int) * (size_t)nA * nB), *seen = calloc(nA, sizeof(int)), *qq = malloc(sizeof(int) * nA);
        for (int b = 0; b < nB; b++) permB[b] = b;
        int h = 0, t = 0; seen[0] = 1; qq[t++] = 0;
        while (h < t) { int a = qq[h++];
            for (int s = 0; s < ng; s++) { int a2 = gA[s][a]; if (seen[a2]) continue; seen[a2] = 1; qq[t++] = a2;
                for (int b = 0; b < nB; b++) permB[(size_t)a2 * nB + b] = gB[s][permB[(size_t)a * nB + b]]; } }
        if (t != nA) { fprintf(stderr, "not transitive on A\n"); return 2; }
        contrib = malloc(sizeof(int) * ndc); nE = malloc(sizeof(int) * ndc); EA = malloc(sizeof(int *) * ndc); EB = malloc(sizeof(int *) * ndc);
        for (int d = 0; d < ndc; d++) { int c; if (fscanf(f, "%d", &c) != 1) return 2; int bs[256];
            for (int k = 0; k < c; k++) if (fscanf(f, "%d", &bs[k]) != 1) return 2;
            contrib[d] = c; nE[d] = c * nA; EA[d] = malloc(sizeof(int) * nE[d]); EB[d] = malloc(sizeof(int) * nE[d]);
            int e = 0; for (int a = 0; a < nA; a++) for (int k = 0; k < c; k++) { EA[d][e] = a; EB[d][e] = permB[(size_t)a * nB + bs[k]]; e++; } }
        fclose(f);
        goto loaded;
    }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d %d", &nA, &nB, &ndc) != 3) return 2;
    contrib = malloc(sizeof(int) * ndc); nE = malloc(sizeof(int) * ndc); EA = malloc(sizeof(int *) * ndc); EB = malloc(sizeof(int *) * ndc);
    for (int d = 0; d < ndc; d++) { if (fscanf(f, "%d %d", &contrib[d], &nE[d]) != 2) return 2;
        EA[d] = malloc(sizeof(int) * nE[d]); EB[d] = malloc(sizeof(int) * nE[d]);
        for (int e = 0; e < nE[d]; e++) if (fscanf(f, "%d %d", &EA[d][e], &EB[d][e]) != 2) return 2; }
    fclose(f);
  loaded:;
    int n = nA + nB; adj = malloc(sizeof(int) * n * DELTA); deg = malloc(sizeof(int) * n); dist = malloc(sizeof(int) * n); q = malloc(sizeof(int) * n);
    int hist[64] = {0}; for (int d = 0; d < ndc; d++) if (contrib[d] < 64) hist[contrib[d]]++;
    fprintf(stderr, "%s: nA %d nB %d double cosets %d; contributions", argv[1], nA, nB, ndc);
    for (int c = 1; c < 64; c++) if (hist[c]) fprintf(stderr, " %dx%d", hist[c], c); fprintf(stderr, "\n");

    if (getenv("TABU")) {   /* tabu search: best-improvement over all single same-contribution swaps */
        quiet = 1;
        double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
        int TT = getenv("TT") ? atoi(getenv("TT")) : 10;
        long STAG = getenv("STAG") ? atol(getenv("STAG")) : 200;
        uint64_t rs = 88172645463325252ULL ^ (getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0);
        #define RND() (rs ^= rs << 13, rs ^= rs >> 7, rs ^= rs << 17, rs)
        int *in = calloc(ndc, sizeof(int)); long *tabu = calloc(ndc, sizeof(long));
        clock_t t0 = clock(); long gbest = 1L << 40; int rst = 0;
        while ((double)(clock() - t0) / CLOCKS_PER_SEC < SECS && gbest > 0) {
            memset(in, 0, sizeof(int) * ndc); nch = 0; int left = DELTA, tries = 0;
            while (left > 0 && tries < 100000) { int d = RND() % ndc; tries++; if (in[d] || contrib[d] > left) continue; in[d] = 1; chosen[nch++] = d; left -= contrib[d]; }
            if (left) continue;
            memset(tabu, 0, sizeof(long) * ndc);
            tested = 0; bestcost = 1L << 40; test(); long cur = bestcost; long lbest = cur; long since = 0;
            for (long k = 1; since < STAG && cur > 0; k++) {
                if ((double)(clock() - t0) / CLOCKS_PER_SEC > SECS) break;
                long bc = 1L << 40; int bj = -1, bd = -1, nt = 0;
                for (int j = 0; j < nch; j++) { int d0 = chosen[j];
                    for (int d1 = 0; d1 < ndc; d1++) {
                        if (in[d1] || contrib[d1] != contrib[d0]) continue;
                        chosen[j] = d1; bestcost = 1L << 40; test(); long c = bestcost; chosen[j] = d0;
                        if (tabu[d1] > k && !(c < gbest)) continue;
                        if (c < bc) { bc = c; bj = j; bd = d1; nt = 1; }
                        else if (c == bc) { nt++; if (RND() % nt == 0) { bj = j; bd = d1; } }
                    } }
                if (bj < 0) break;
                int d0 = chosen[bj]; chosen[bj] = bd; in[d0] = 0; in[bd] = 1;
                tabu[d0] = k + TT + (long)(RND() % (uint64_t)(TT + 1));
                cur = bc;
                if (cur < lbest) { lbest = cur; since = 0; } else since++;
                if (cur < gbest) { gbest = cur; nbest = nch; memcpy(bestset, chosen, sizeof(int) * nch);
                    if (outpath) write_graph(chosen, nch); fprintf(stderr, "restart %d step %ld best %ld\n", rst, k, gbest); }
            }
            rst++;
        }
        bestcost = gbest;
        printf("RESULT %s TABU restarts %d best %ld vertices %d set", argv[1], rst, bestcost, n);
        for (int j = 0; j < nbest; j++) printf(" %d", bestset[j]); printf("\n");
        return 0;
    }
    if (getenv("SA")) {   /* annealing over unions: swap one chosen double coset for an unchosen one of equal size */
        double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 3,
               T1 = getenv("T1") ? atof(getenv("T1")) : 0.3; long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 20000;
        uint64_t rs = 88172645463325252ULL ^ (getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0);
        #define RND() (rs ^= rs << 13, rs ^= rs >> 7, rs ^= rs << 17, rs)
        int *in = calloc(ndc, sizeof(int)); clock_t t0 = clock(); long gbest = 1L << 40;
        for (int run = 0; (double)(clock() - t0) / CLOCKS_PER_SEC < SECS && gbest > 0; run++) {
            /* random start: add random double cosets until degree DELTA */
            memset(in, 0, sizeof(int) * ndc); nch = 0; int left = DELTA, tries = 0;
            while (left > 0 && tries < 100000) { int d = RND() % ndc; tries++; if (in[d] || contrib[d] > left) continue; in[d] = 1; chosen[nch++] = d; left -= contrib[d]; }
            if (left) continue;
            long cur; tested = 0; bestcost = 1L << 40; test(); cur = bestcost;
            for (long it = 0; it < ITERS && cur > 0; it++) {
                if ((it & 63) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > SECS) break;
                double T = T0 * pow(T1 / T0, (double)it / ITERS);
                int j = RND() % nch, d0 = chosen[j], d1 = RND() % ndc;
                if (in[d1] || contrib[d1] != contrib[d0]) continue;
                chosen[j] = d1; long before = bestcost; bestcost = 1L << 40; test(); long c = bestcost; bestcost = before;
                if (c <= cur || (double)(RND() >> 11) / 9007199254740992.0 < exp(-(c - cur) / T)) { cur = c; in[d0] = 0; in[d1] = 1;
                    if (c < gbest) { gbest = c; nbest = nch; memcpy(bestset, chosen, sizeof(int) * nch); if (outpath) write_graph(chosen, nch); } }
                else chosen[j] = d0;
            }
            if (cur < gbest) { gbest = cur; nbest = nch; memcpy(bestset, chosen, sizeof(int) * nch); }
        }
        bestcost = gbest;
        printf("RESULT %s SA solutions %lld best %ld vertices %d set", argv[1], nsol, bestcost, n);
        for (int j = 0; j < nbest; j++) printf(" %d", bestset[j]); printf("\n");
        return 0;
    }
    rec(0, DELTA);
    printf("RESULT %s tested %lld solutions %lld best %ld vertices %d set", argv[1], tested, nsol, bestcost, n);
    for (int j = 0; j < nbest; j++) printf(" %d", bestset[j]); printf("\n");
    return 0;
}
