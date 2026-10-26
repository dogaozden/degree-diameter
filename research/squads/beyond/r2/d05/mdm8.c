/* d05: anneal nu (flag parities) and sigma_1, sigma_2 (point -> line bijections) for the k = 2 multi-doubled-matching
 * lift of W(q) over Z2 x Z5 (M = 5), with condition (A) relaxed by length-4 routes.
 * Cost = number of unordered opposite same-colour pairs (v,u) such that all q+1 base geodesics have the same nu-parity
 * AND no route exists.  A route: a walk of length exactly 4 in base + matchings (jumps +i on point->line, -i on
 * line->point, i in {1,2}) with jump sum = 0 mod 5, at least one jump, ending at u.  Both Z2 classes then reachable.
 * usage: mdm8 q.  env: SEED ITERS ROUNDS SMOVES T0 T1 OUT IN EDGES
 *   OUT: writes "q N" / sigma1 line / sigma2 line / nu line of the best state (cost 0 or the best found).
 *   IN : same format, start state.  EDGES: writes the lift edge list (apsp input, n = 4*5*N) of the best state.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, Q1, N, L, V, F, G, P;
static int *pl, *lineOf, *flagIdx, *adjB, *linesOfPt, *pairId, *geoFlags, *geoPair, *flStart, *flList, *pairA, *pairB;
static int sig[2][1024], sinv[2][1024];
static uint8_t *par, *route, *bad, *nu, *bestNu, *concur;
static int *cnt, *stamp, *touched, *oldBad, curStamp = 0, total = 0;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static inline int isBad(int p) { return (cnt[p] == 0 || cnt[p] == Q1) && !route[p]; }

static void addGeo(int f1, int f2, int f3, int f4, int pid) {
    int g = G++;
    geoFlags[4 * g] = f1; geoFlags[4 * g + 1] = f2; geoFlags[4 * g + 2] = f3; geoFlags[4 * g + 3] = f4; geoPair[g] = pid;
}

static void buildGeo(void) {
    V = 2 * N; F = L * Q1;
    pl = malloc(sizeof(int) * L * Q1);
    FILE *f = NULL; char fn[256]; sprintf(fn, "gq/gq_q%d.bin", q); f = fopen(fn, "rb");
    if (!f) { fprintf(stderr, "no %s\n", fn); exit(1); }
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) exit(1);
    int32_t *tmp = malloc(4L * L * Q1); if (fread(tmp, 4, (size_t)L * Q1, f) != (size_t)L * Q1) exit(1); fclose(f);
    for (int i = 0; i < L * Q1; i++) pl[i] = tmp[i]; free(tmp);
    lineOf = malloc(sizeof(int) * N * N); for (int i = 0; i < N * N; i++) lineOf[i] = -1;
    flagIdx = malloc(sizeof(int) * N * L); for (int i = 0; i < N * L; i++) flagIdx[i] = -1;
    adjB = malloc(sizeof(int) * V * Q1); linesOfPt = malloc(sizeof(int) * N * Q1);
    int *dg = calloc(V, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k]; flagIdx[p * L + l] = l * Q1 + k;
        adjB[p * Q1 + dg[p]] = N + l; dg[p]++;
        adjB[(N + l) * Q1 + dg[N + l]] = p; dg[N + l]++;
        linesOfPt[p * Q1 + (dg[p] - 1)] = l;
    }
    for (int l = 0; l < L; l++) for (int a = 0; a < Q1; a++) for (int b = 0; b < Q1; b++) if (a != b)
        lineOf[pl[l * Q1 + a] * N + pl[l * Q1 + b]] = l;
    /* concurrent lines */
    concur = calloc((size_t)L * L, 1);
    for (int p = 0; p < N; p++) for (int a = 0; a < Q1; a++) for (int b = 0; b < Q1; b++)
        concur[(size_t)linesOfPt[p * Q1 + a] * L + linesOfPt[p * Q1 + b]] = 1;
    /* pairs */
    pairId = malloc(sizeof(int) * V * V); for (int i = 0; i < V * V; i++) pairId[i] = -1;
    int maxP = 2 * N * N / 2 + 10;
    pairA = malloc(sizeof(int) * maxP); pairB = malloc(sizeof(int) * maxP);
    P = 0;
    for (int v = 0; v < N; v++) for (int u = v + 1; u < N; u++) if (lineOf[v * N + u] < 0) {
        pairA[P] = v; pairB[P] = u; pairId[v * V + u] = pairId[u * V + v] = P; P++; }
    for (int a = 0; a < L; a++) for (int b = a + 1; b < L; b++) if (!concur[(size_t)a * L + b]) {
        pairA[P] = N + a; pairB[P] = N + b; pairId[(N + a) * V + N + b] = pairId[(N + b) * V + N + a] = P; P++; }
    geoFlags = malloc(sizeof(int) * 4 * (size_t)P * Q1); geoPair = malloc(sizeof(int) * (size_t)P * Q1); G = 0;
    for (int pid = 0; pid < P; pid++) {
        int x = pairA[pid], y = pairB[pid];
        if (x < N) { /* points v=x, u=y: geodesics v - l - w - m - u */
            int v = x, u = y;
            for (int k = 0; k < Q1; k++) {
                int l = linesOfPt[v * Q1 + k], w = -1;
                for (int j = 0; j < Q1; j++) { int c = pl[l * Q1 + j]; if (c != v && lineOf[c * N + u] >= 0) { w = c; break; } }
                if (w < 0) { fprintf(stderr, "no w\n"); exit(1); }
                int m = lineOf[w * N + u];
                addGeo(flagIdx[v * L + l], flagIdx[w * L + l], flagIdx[w * L + m], flagIdx[u * L + m], pid);
            }
        } else { /* lines a = x-N, b = y-N: geodesics a - p - m - z - b */
            int a = x - N, b = y - N;
            for (int k = 0; k < Q1; k++) {
                int p = pl[a * Q1 + k], z = -1;
                for (int j = 0; j < Q1; j++) { int c = pl[b * Q1 + j]; if (lineOf[p * N + c] >= 0) { z = c; break; } }
                if (z < 0) { fprintf(stderr, "no z\n"); exit(1); }
                int m = lineOf[p * N + z];
                addGeo(flagIdx[p * L + a], flagIdx[p * L + m], flagIdx[z * L + m], flagIdx[z * L + b], pid);
            }
        }
    }
    /* flag -> geodesic lists */
    flStart = calloc(F + 1, sizeof(int));
    for (int i = 0; i < 4 * G; i++) flStart[geoFlags[i] + 1]++;
    for (int f = 0; f < F; f++) flStart[f + 1] += flStart[f];
    flList = malloc(sizeof(int) * 4 * (size_t)G);
    int *fill = calloc(F, sizeof(int));
    for (int g = 0; g < G; g++) for (int t = 0; t < 4; t++) { int f = geoFlags[4 * g + t];
        flList[flStart[f] + fill[f]++] = g; }
    free(fill); free(dg);
    par = malloc(G); cnt = calloc(P, sizeof(int)); route = calloc(P, 1); bad = calloc(P, 1);
    nu = calloc(F, 1); bestNu = calloc(F, 1); stamp = calloc(P, sizeof(int));
    int maxL = 0; for (int f = 0; f < F; f++) if (flStart[f + 1] - flStart[f] > maxL) maxL = flStart[f + 1] - flStart[f];
    touched = malloc(sizeof(int) * (maxL + 8)); oldBad = malloc(sizeof(int) * (maxL + 8));
    fprintf(stderr, "W(%d): N=%d lines=%d pairs=%d geodesics=%d maxflaglist=%d\n", q, N, L, P, G, maxL);
    if (G != P * Q1) { fprintf(stderr, "geodesic count mismatch\n"); exit(1); }
}

static void recomputeCnt(void) {
    for (int p = 0; p < P; p++) cnt[p] = 0;
    for (int g = 0; g < G; g++) {
        int x = nu[geoFlags[4 * g]] ^ nu[geoFlags[4 * g + 1]] ^ nu[geoFlags[4 * g + 2]] ^ nu[geoFlags[4 * g + 3]];
        par[g] = x; cnt[geoPair[g]] += x;
    }
}
static void recomputeBad(void) {
    total = 0;
    for (int p = 0; p < P; p++) { bad[p] = isBad(p); total += bad[p]; }
}

static inline uint16_t shiftm(uint16_t m, int dj) {
    uint16_t r = 0;
    for (int s5 = 0; s5 < 5; s5++) for (int jf = 0; jf < 2; jf++)
        if ((m >> (s5 * 2 + jf)) & 1) r |= (uint16_t)1 << ((((s5 + dj) % 5) * 2) + 1);
    return r;
}

/* route bits: walks of exact length 4 from s with jump sum 0 mod 5 and >= 1 jump, reaching u */
static void computeRoutes(void) {
    memset(route, 0, P);
    uint16_t *cur = malloc(2 * V), *nxt = malloc(2 * V);
    for (int s = 0; s < V; s++) {
        memset(cur, 0, 2 * V); cur[s] = 1;
        for (int step = 0; step < 4; step++) {
            memset(nxt, 0, 2 * V);
            for (int x = 0; x < V; x++) if (cur[x]) {
                uint16_t m = cur[x];
                for (int k = 0; k < Q1; k++) nxt[adjB[x * Q1 + k]] |= m;
                for (int i = 0; i < 2; i++) {
                    int y, dj;
                    if (x < N) { y = N + sig[i][x]; dj = i + 1; }
                    else { y = sinv[i][x - N]; dj = (5 - (i + 1)) % 5; }
                    nxt[y] |= shiftm(m, dj);
                }
            }
            uint16_t *t = cur; cur = nxt; nxt = t;
        }
        for (int u = 0; u < V; u++) if (u != s && (cur[u] & 2)) {
            int pid = pairId[s * V + u]; if (pid >= 0) route[pid] = 1; }
        /* bit 1 = (sum 0, jumped) */
    }
    free(cur); free(nxt);
}

/* flip nu[f]; returns change of total bad */
static int flip(int f) {
    curStamp++;
    int nt = 0;
    for (int idx = flStart[f]; idx < flStart[f + 1]; idx++) {
        int g = flList[idx], p = geoPair[g];
        if (stamp[p] != curStamp) { stamp[p] = curStamp; touched[nt] = p; oldBad[nt] = bad[p]; nt++; }
        par[g] ^= 1; cnt[p] += par[g] ? 1 : -1;
    }
    int d = 0;
    for (int t = 0; t < nt; t++) { int p = touched[t]; int nb = isBad(p); d += nb - oldBad[t]; bad[p] = nb; }
    nu[f] ^= 1; total += d;
    return d;
}

static void anneal(long iters, double T0, double T1) {
    int best = total;
    memcpy(bestNu, nu, F);
    for (long it = 0; it < iters && total > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int f = (int)(rnd() % F);
        int d = flip(f);
        if (d > 0 && urand() >= exp(-d / T)) flip(f);
        if (total < best) { best = total; memcpy(bestNu, nu, F); }
    }
    /* restore best */
    if (best < total) { for (int f = 0; f < F; f++) if (nu[f] != bestNu[f]) flip(f); }
}

static void writeState(const char *fn, int *s1, int *s2, uint8_t *n) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d\n", q, N);
    for (int i = 0; i < N; i++) fprintf(f, "%d ", s1[i]); fprintf(f, "\n");
    for (int i = 0; i < N; i++) fprintf(f, "%d ", s2[i]); fprintf(f, "\n");
    for (int i = 0; i < F; i++) fprintf(f, "%d ", n[i]); fprintf(f, "\n");
    fclose(f);
}

static void writeEdges(const char *fn, int *s1, int *s2, uint8_t *n) {
    int M = 5; long nv = 2L * N * 2 * M;
    FILE *f = fopen(fn, "w"); fprintf(f, "%ld\n", nv);
    #define VID(v, a, b) ((long)((v) * 2 + (a)) * M + (b))
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k]; int nv1 = n[l * Q1 + k];
        for (int a = 0; a < 2; a++) for (int b = 0; b < M; b++)
            fprintf(f, "%ld %ld\n", VID(p, a, b), VID(N + l, a ^ nv1, b));
    }
    int *sg[2] = {s1, s2};
    for (int i = 0; i < 2; i++) for (int p = 0; p < N; p++)
        for (int a = 0; a < 2; a++) for (int b = 0; b < M; b++) for (int c = 0; c < 2; c++)
            fprintf(f, "%ld %ld\n", VID(p, a, b), VID(N + sg[i][p], a ^ c, (b + i + 1) % M));
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: mdm8 q\n"); return 1; }
    q = atoi(argv[1]); Q1 = q + 1; N = q * q * q * 0 + 0;
    /* N = (q+1)(q^2+1) points, L = N lines */
    N = (q + 1) * (q * q + 1); L = N;
    char *e;
    rs ^= (uint64_t)(e = getenv("SEED")) ? atoll(e) * 2654435761ULL + 1 : 7;
    long ITERS = (e = getenv("ITERS")) ? atol(e) : 2000000;
    int ROUNDS = (e = getenv("ROUNDS")) ? atoi(e) : 20;
    int SMOVES = (e = getenv("SMOVES")) ? atoi(e) : 20;
    double T0 = (e = getenv("T0")) ? atof(e) : 0.5, T1 = (e = getenv("T1")) ? atof(e) : 0.05;
    const char *OUT = getenv("OUT"), *IN = getenv("IN"), *EDG = getenv("EDGES");
    buildGeo();
    int s1[1024], s2[1024];
    if (IN) {
        FILE *f = fopen(IN, "r"); int qq, nn; if (fscanf(f, "%d %d", &qq, &nn) != 2 || qq != q || nn != N) { fprintf(stderr, "bad IN\n"); return 1; }
        for (int i = 0; i < N; i++) if (fscanf(f, "%d", &s1[i]) != 1) return 1;
        for (int i = 0; i < N; i++) if (fscanf(f, "%d", &s2[i]) != 1) return 1;
        for (int i = 0; i < F; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; nu[i] = x; }
        fclose(f);
    } else {
        for (int i = 0; i < N; i++) { s1[i] = i; s2[i] = i; }
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = s1[i]; s1[i] = s1[j]; s1[j] = t; }
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = s2[i]; s2[i] = s2[j]; s2[j] = t; }
        for (int i = 0; i < F; i++) nu[i] = rnd() & 1;
    }
    for (int i = 0; i < N; i++) { sig[0][i] = s1[i]; sig[1][i] = s2[i]; }
    for (int i = 0; i < 2; i++) for (int p = 0; p < N; p++) sinv[i][sig[i][p]] = p;
    computeRoutes(); recomputeCnt(); recomputeBad();
    fprintf(stderr, "start total=%d routes=%d\n", total, 0);
    int bestTotal = total; uint8_t *bestN = malloc(F); memcpy(bestN, nu, F);
    int *bs1 = malloc(sizeof(int) * N), *bs2 = malloc(sizeof(int) * N);
    memcpy(bs1, s1, sizeof(int) * N); memcpy(bs2, s2, sizeof(int) * N);
    for (int r = 0; r < ROUNDS && bestTotal > 0; r++) {
        anneal(ITERS, T0, T1);
        if (total < bestTotal) { bestTotal = total; memcpy(bestN, nu, F); memcpy(bs1, sig[0], sizeof(int) * N); memcpy(bs2, sig[1], sizeof(int) * N); }
        fprintf(stderr, "round %d nu-anneal total=%d best=%d\n", r, total, bestTotal);
        if (bestTotal == 0) break;
        /* sigma moves: swap two images of sigma_i; accept if not worse (or SA-like) */
        for (int t = 0; t < SMOVES; t++) {
            int i = rnd() & 1, x = rnd() % N, y = rnd() % N; if (x == y) continue;
            int oldTotal = total;
            int tmp = sig[i][x]; sig[i][x] = sig[i][y]; sig[i][y] = tmp;
            sinv[i][sig[i][x]] = x; sinv[i][sig[i][y]] = y;
            computeRoutes(); recomputeBad();
            if (total > oldTotal && urand() >= exp(-(total - oldTotal) / 0.3)) {
                tmp = sig[i][x]; sig[i][x] = sig[i][y]; sig[i][y] = tmp;
                sinv[i][sig[i][x]] = x; sinv[i][sig[i][y]] = y;
                computeRoutes(); recomputeBad();
            }
            if (total < bestTotal) { bestTotal = total; memcpy(bestN, nu, F); memcpy(bs1, sig[0], sizeof(int) * N); memcpy(bs2, sig[1], sizeof(int) * N); }
            if (bestTotal == 0) break;
        }
        fprintf(stderr, "round %d sigma-moves total=%d best=%d\n", r, total, bestTotal);
    }
    printf("RESULT q=%d best_far_pairs=%d\n", q, bestTotal);
    /* restore the best state and write it */
    for (int i = 0; i < N; i++) { sig[0][i] = bs1[i]; sig[1][i] = bs2[i]; }
    for (int i = 0; i < 2; i++) for (int p = 0; p < N; p++) sinv[i][sig[i][p]] = p;
    memcpy(nu, bestN, F);
    computeRoutes(); recomputeCnt(); recomputeBad();
    printf("check total=%d\n", total);
    if (OUT) writeState(OUT, bs1, bs2, bestN);
    if (EDG) writeEdges(EDG, bs1, bs2, bestN);
    return 0;
}
