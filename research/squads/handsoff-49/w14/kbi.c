/* kbi (w14): exhaustive search over S = union of (K,H)-double cosets, the two-subgroup bi-coset family.
 * Input BIN: int32 M, int32 nD; uint16 T[M*M] with T[i*M+j] = id of the double coset K y_j x_i^-1 K-H,
 *   where A_i = H x_i (right cosets of H), B_j = K y_j (right cosets of K), |H| = |K|;
 *   uint8 delta[nD] = |D|/|K| for each double coset D (its degree contribution); 0 or >4 = unusable.
 * Graph: A_i ~ B_j iff T[i*M+j] in S. Each vertex has degree sum(delta over S) = 4 (checked).
 * Cost = far(A_0) + far(B_0), far = distance > 9 or unreachable; cost 0 = diameter <= 9 (both sides are
 * vertex-transitive, so two roots suffice).
 * Usage: kbi BIN info | kbi BIN exh [LIMIT] [OUT.edges] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int M, nD;
static uint16_t *T;
static uint8_t *delta;
static int *L[5], nL[5];
static int **Aadj, **Badj;               /* per usable double coset D: M*delta entries */
static int *adjA, *adjB, *vis, *q, stamp = 0;
static long long nev = 0, limit = 0;
static int bestcost = 1 << 30, bestS[4], bestns = 0;
static double t0;
static int stopflag = 0;
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }
static void die(const char *m) { fprintf(stderr, "kbi: %s\n", m); exit(1); }

static int reach9(int root) {
    stamp++;
    int qh = 0, qt = 0, d = 0;
    q[qt++] = root; vis[root] = stamp;
    while (qh < qt && d < 9) {
        int end = qt;
        while (qh < end) {
            int v = q[qh++];
            if (v < M) {
                for (int k = 0; k < 4; k++) { int w = M + adjA[4 * v + k]; if (vis[w] != stamp) { vis[w] = stamp; q[qt++] = w; } }
            } else {
                int j = v - M;
                for (int k = 0; k < 4; k++) { int w = adjB[4 * j + k]; if (vis[w] != stamp) { vis[w] = stamp; q[qt++] = w; } }
            }
        }
        d++;
    }
    return qt;
}

/* fill adjacency for the chosen double cosets S[0..ns-1]; returns 0 if degrees are not 4 */
static int build(const int *S, int ns) {
    for (int i = 0; i < M; i++) {
        int c = 0;
        for (int u = 0; u < ns; u++) {
            int D = S[u], dl = delta[D];
            for (int t = 0; t < dl; t++) adjA[4 * i + c++] = Aadj[D][i * dl + t];
        }
        if (c != 4) return 0;
    }
    for (int j = 0; j < M; j++) {
        int c = 0;
        for (int u = 0; u < ns; u++) {
            int D = S[u], dl = delta[D];
            for (int t = 0; t < dl; t++) adjB[4 * j + c++] = Badj[D][j * dl + t];
        }
        if (c != 4) return 0;
    }
    return 1;
}

static int evalS(const int *S, int ns) {
    if (!build(S, ns)) return -1;
    int r1 = reach9(0), r2 = reach9(M);
    nev++;
    return (2 * M - r1) + (2 * M - r2);
}

static void consider(const int *S, int ns) {
    int c = evalS(S, ns);
    if (c < 0) return;
    if (c < bestcost) {
        bestcost = c; bestns = ns; memcpy(bestS, S, sizeof(int) * ns);
        fprintf(stderr, "  new best cost %d S={", c);
        for (int u = 0; u < ns; u++) fprintf(stderr, "%d%s", S[u], u + 1 < ns ? "," : "");
        fprintf(stderr, "} t=%.1fs nev=%lld\n", now() - t0, nev);
    }
    if (limit > 0 && nev >= limit) stopflag = 1;
}

int main(int argc, char **argv) {
    if (argc < 3) die("usage: kbi BIN info|exh [LIMIT] [OUT.edges]");
    t0 = now();
    FILE *f = fopen(argv[1], "rb");
    if (!f) die("cannot open");
    int32_t hd[2];
    if (fread(hd, 4, 2, f) != 2) die("header");
    M = hd[0]; nD = hd[1];
    T = malloc((size_t)M * M * 2);
    if (fread(T, 2, (size_t)M * M, f) != (size_t)M * M) die("T");
    delta = malloc(nD);
    if (fread(delta, 1, nD, f) != (size_t)nD) die("delta");
    fclose(f);
    adjA = malloc(4 * M * sizeof(int)); adjB = malloc(4 * M * sizeof(int));
    vis = calloc(2 * M, sizeof(int)); q = malloc(2 * M * sizeof(int));
    for (int s = 0; s <= 4; s++) { L[s] = malloc((nD + 1) * sizeof(int)); nL[s] = 0; }
    Aadj = calloc(nD, sizeof(int *)); Badj = calloc(nD, sizeof(int *));
    for (int D = 0; D < nD; D++) {
        if (delta[D] >= 1 && delta[D] <= 4) {
            L[delta[D]][nL[delta[D]]++] = D;
            Aadj[D] = malloc((size_t)M * delta[D] * sizeof(int));
            Badj[D] = malloc((size_t)M * delta[D] * sizeof(int));
        }
    }
    int *cntA = calloc((size_t)nD * M, sizeof(int)), *cntB = calloc((size_t)nD * M, sizeof(int));
    if (!cntA || !cntB) die("mem");
    for (int i = 0; i < M; i++) for (int j = 0; j < M; j++) {
        int D = T[(size_t)i * M + j];
        if (D >= nD) die("bad id");
        int dl = delta[D];
        if (dl >= 1 && dl <= 4) {
            int pa = cntA[(size_t)D * M + i]++, pb = cntB[(size_t)D * M + j]++;
            if (pa < dl) Aadj[D][i * dl + pa] = j;
            if (pb < dl) Badj[D][j * dl + pb] = i;
        }
    }
    for (int D = 0; D < nD; D++) if (delta[D] >= 1 && delta[D] <= 4) {
        for (int i = 0; i < M; i++) if (cntA[(size_t)D * M + i] != delta[D]) die("A degree mismatch");
        for (int j = 0; j < M; j++) if (cntB[(size_t)D * M + j] != delta[D]) die("B degree mismatch");
    }
    free(cntA); free(cntB);
    if (strcmp(argv[2], "info") == 0) {
        fprintf(stderr, "M=%d n=%d nD=%d usable by delta: 1:%d 2:%d 3:%d 4:%d\n", M, 2 * M, nD, nL[1], nL[2], nL[3], nL[4]);
        return 0;
    }
    limit = argc > 3 ? atoll(argv[3]) : 0;
    int S[4];
    for (int a = 0; a < nL[4] && !stopflag; a++) { S[0] = L[4][a]; consider(S, 1); }
    for (int a = 0; a < nL[3] && !stopflag; a++) for (int b = 0; b < nL[1] && !stopflag; b++) {
        S[0] = L[3][a]; S[1] = L[1][b]; consider(S, 2); }
    for (int a = 0; a < nL[2] && !stopflag; a++) for (int b = a + 1; b < nL[2] && !stopflag; b++) {
        S[0] = L[2][a]; S[1] = L[2][b]; consider(S, 2); }
    for (int a = 0; a < nL[2] && !stopflag; a++) for (int b = 0; b < nL[1] && !stopflag; b++)
    for (int c = b + 1; c < nL[1] && !stopflag; c++) {
        S[0] = L[2][a]; S[1] = L[1][b]; S[2] = L[1][c]; consider(S, 3); }
    for (int a = 0; a < nL[1] && !stopflag; a++) for (int b = a + 1; b < nL[1] && !stopflag; b++)
    for (int c = b + 1; c < nL[1] && !stopflag; c++) for (int d = c + 1; d < nL[1] && !stopflag; d++) {
        S[0] = L[1][a]; S[1] = L[1][b]; S[2] = L[1][c]; S[3] = L[1][d]; consider(S, 4); }
    fprintf(stderr, "kbi: evals=%lld best_cost=%d time=%.1fs\n", nev, bestcost, now() - t0);
    printf("RESULT_KBI M=%d n=%d evals=%lld best_cost=%d S=", M, 2 * M, nev, bestcost);
    for (int u = 0; u < bestns; u++) printf("%d%s", bestS[u], u + 1 < bestns ? "," : "");
    printf("\n");
    if (argc > 4 && bestcost < (1 << 30)) {
        build(bestS, bestns);
        FILE *g = fopen(argv[4], "w");
        if (!g) die("cannot write edges");
        fprintf(g, "%d\n", 2 * M);
        for (int i = 0; i < M; i++) for (int k = 0; k < 4; k++) fprintf(g, "%d %d\n", i, M + adjA[4 * i + k]);
        fclose(g);
    }
    return 0;
}
