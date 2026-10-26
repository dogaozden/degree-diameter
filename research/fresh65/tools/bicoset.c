/* Exhaustive scan of bi-coset graphs B(G; L, R; D) exported by bicoset.g (job fresh-6-5).
 *
 * Every union N0 of L-orbits on G/R whose sizes add up to d is a candidate: A-vertex a is joined to
 * T[a][x] for x in N0. G is transitive on each side, so BFS from the two base vertices gives the exact
 * diameter. cost = number of (base, vertex) pairs at distance > D (0 = diameter <= D).
 *
 * usage: bicoset FILE d D [OUTPREFIX] [MAXCAND]
 *   env MAXFIX=f: use at most f orbits of size 1 (for orbit-symmetric Haar: at most f alpha-fixed letters).
 *   prints a cost histogram and every cost-0 candidate (orbit indices); with OUTPREFIX, writes the first
 *   cost-0 graph as OUTPREFIX.edges (first line n, then "u v"; A = 0..nA-1, B = nA..nA+nB-1) for apsp.c.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int nA, nB, baseA, baseB, nOrb, d, D;
static int *T;            /* nA x nB */
static int *osz, **opts;  /* orbit sizes and points */
static int *N0, n0;       /* chosen B-points */
static int *adjA, *adjB, *degB, degBmax;
static int *dist, *queue;
static long ncand, maxcand, hist[4096], nvalid;
static int chosen[64], nch;
static char label[256];
static const char *outpre;
static int maxfix = 99, nfix;   /* env MAXFIX: at most this many size-1 orbits in a candidate */

static int bfs(int src, int nV) { /* returns #vertices with dist > D; vertices 0..nA-1 A, nA.. B */
    for (int i = 0; i < nV; i++) dist[i] = -1;
    int h = 0, t = 0, reached = 0;
    dist[src] = 0; queue[t++] = src;
    while (h < t) {
        int x = queue[h++]; reached++;
        if (dist[x] == D) continue;
        if (x < nA) {
            for (int i = 0; i < d; i++) { int y = nA + adjA[x * d + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } }
        } else {
            int b = x - nA;
            for (int i = 0; i < degB[b]; i++) { int y = adjB[b * degBmax + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } }
        }
    }
    return nV - reached;
}

static void evaluate(void) {
    ncand++;
    for (int a = 0; a < nA; a++) for (int i = 0; i < n0; i++) adjA[a * d + i] = T[(long)a * nB + N0[i]];
    memset(degB, 0, nB * sizeof(int));
    for (int a = 0; a < nA; a++) for (int i = 0; i < d; i++) {
        int b = adjA[a * d + i];
        if (degB[b] >= degBmax) return;   /* B side over the degree cap (only if |L| != |R|) */
        adjB[b * degBmax + degB[b]++] = a;
    }
    int nV = nA + nB;
    int c = bfs(baseA, nV) + bfs(nA + baseB, nV);
    hist[c < 4095 ? c : 4095]++;
    if (c == 0) {
        nvalid++;
        printf("VALID %s n=%d orbits", label, nV);
        for (int i = 0; i < nch; i++) printf(" %d", chosen[i]);
        printf(" points");
        for (int i = 0; i < n0; i++) printf(" %d", N0[i]);
        printf("\n");
        if (outpre && nvalid == 1) {
            char fn[512]; snprintf(fn, sizeof fn, "%s.edges", outpre);
            FILE *f = fopen(fn, "w");
            fprintf(f, "%d\n", nV);
            for (int a = 0; a < nA; a++) for (int i = 0; i < d; i++) fprintf(f, "%d %d\n", a, nA + adjA[a * d + i]);
            fclose(f);
        }
        fflush(stdout);
    }
}

static void rec(int start, int left) {
    if (maxcand && ncand >= maxcand) return;
    if (left == 0) { evaluate(); return; }
    for (int o = start; o < nOrb; o++) {
        if (osz[o] > left) continue;
        if (osz[o] == 1 && nfix >= maxfix) continue;
        nfix += osz[o] == 1;
        chosen[nch++] = o;
        for (int i = 0; i < osz[o]; i++) N0[n0++] = opts[o][i];
        rec(o + 1, left - osz[o]);
        n0 -= osz[o]; nch--; nfix -= osz[o] == 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: bicoset FILE d D [OUTPREFIX] [MAXCAND]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    d = atoi(argv[2]); D = atoi(argv[3]);
    outpre = argc > 4 && strcmp(argv[4], "-") ? argv[4] : NULL;
    maxcand = argc > 5 ? atol(argv[5]) : 0;
    if (fscanf(f, "%255s", label) != 1) return 2;
    if (fscanf(f, "%d %d %d %d", &nA, &nB, &baseA, &baseB) != 4) return 2;
    T = malloc((long)nA * nB * sizeof(int));
    for (long i = 0; i < (long)nA * nB; i++) if (fscanf(f, "%d", &T[i]) != 1) return 2;
    if (fscanf(f, "%d", &nOrb) != 1) return 2;
    osz = malloc(nOrb * sizeof(int)); opts = malloc(nOrb * sizeof(int *));
    for (int o = 0; o < nOrb; o++) {
        if (fscanf(f, "%d", &osz[o]) != 1) return 2;
        opts[o] = malloc(osz[o] * sizeof(int));
        for (int i = 0; i < osz[o]; i++) if (fscanf(f, "%d", &opts[o][i]) != 1) return 2;
    }
    fclose(f);
    if (getenv("MAXFIX")) maxfix = atoi(getenv("MAXFIX"));
    degBmax = d;  /* max degree cap on side B (equal to d when |L| = |R|) */
    N0 = malloc(d * sizeof(int)); adjA = malloc((long)nA * d * sizeof(int));
    adjB = malloc((long)nB * degBmax * sizeof(int)); degB = malloc(nB * sizeof(int));
    dist = malloc((nA + nB) * sizeof(int)); queue = malloc((nA + nB) * sizeof(int));
    rec(0, d);
    printf("DONE %s nA=%d nB=%d orbits=%d candidates=%ld valid=%ld hist", label, nA, nB, nOrb, ncand, nvalid);
    int mn = -1, shown = 0;
    for (int c = 0; c < 4096; c++) if (hist[c]) { if (mn < 0) mn = c; if (shown++ < 6) printf(" %d:%ld", c, hist[c]); }
    printf(" min=%d%s\n", mn, (maxcand && ncand >= maxcand) ? " TRUNCATED" : "");
    return 0;
}
