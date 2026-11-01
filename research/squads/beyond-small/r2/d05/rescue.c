/* rescue: pack A-hubs and B-hubs on the (16,5) graph G with hub-hub edges (card d05).
 *
 * A hub h (side A) is a new vertex joined to N(h) ⊆ B-old (16 vertices, one spare slot). A hub-hub edge joins an
 * A-hub h to a B-hub g (each hub uses at most one spare slot, so the matching M pairs hubs of opposite sides).
 * Pair rules (diameter 5):
 *   A-pair (h,h') is fine if compat (some x in N(h), x' in N(h') at distance <= 2, N's disjoint), or if
 *   M(h)=g and some y in N(h') is adjacent to some x in N(g) (path h-g-x-y-h'), or symmetrically via M(h').
 *   B-pairs: the same with the roles of the sides exchanged. Disjointness of N's is always required.
 * Search: simulated annealing over (S_A, S_B, M) with score |S_A|+|S_B| - lambda * (#unrescued pairs);
 * the best state with zero unrescued pairs is written out.
 *
 * usage: rescue EDGES POOLA POOLB ITERS T0 T1 LAMBDA SEED OUTPREFIX
 *   POOLA: candidate A-hubs (lines "k id1..idk", B-local ids), POOLB: candidate B-hubs (A-local ids), from hubpack. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define H 16896
#define W 264
static int adjA[H][16], adjB[H][16];
static uint64_t *d2B, *d2A;
static int nA, nB, (*NA)[16], (*NB)[16], *szA, *szB;
static unsigned char *CA, *OA, *CB, *OB, *RA, *RB;   /* RA[j*nA+i]: B-hub j rescues A-pair (.,i); RB[i*nB+j] */
static int *pA, *pB, *inA, *inB, *memA, *memB, *posA, *posB, nmA, nmB, *flA, *flB;
static int V;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int violA(int i, int k) {
    if (CA[(size_t)i * nA + k]) return 0;
    if (pA[i] >= 0 && RA[(size_t)pA[i] * nA + k]) return 0;
    if (pA[k] >= 0 && RA[(size_t)pA[k] * nA + i]) return 0;
    return 1;
}
static int violB(int j, int k) {
    if (CB[(size_t)j * nB + k]) return 0;
    if (pB[j] >= 0 && RB[(size_t)pB[j] * nB + k]) return 0;
    if (pB[k] >= 0 && RB[(size_t)pB[k] * nB + j]) return 0;
    return 1;
}
static int touchSide(int *T, int nt, int side) {
    int c = 0, *mem = side ? memB : memA, nm = side ? nmB : nmA, *fl = side ? flB : flA;
    for (int a = 0; a < nt; a++) { int t = T[a]; if (!(side ? inB[t] : inA[t])) continue;
        for (int m = 0; m < nm; m++) { int k = mem[m]; if (k == t) continue; if (fl[k] && k < t) continue;
            if (side ? violB(t, k) : violA(t, k)) c++; } }
    return c;
}
static int evalTouch(int *TA, int nTA, int *TB, int nTB) {
    for (int a = 0; a < nTA; a++) flA[TA[a]] = 1;
    for (int b = 0; b < nTB; b++) flB[TB[b]] = 1;
    int c = touchSide(TA, nTA, 0) + touchSide(TB, nTB, 1);
    for (int a = 0; a < nTA; a++) flA[TA[a]] = 0;
    for (int b = 0; b < nTB; b++) flB[TB[b]] = 0;
    return c;
}
static void memAdd(int side, int x) { int *mem = side ? memB : memA, *pos = side ? posB : posA, *nm = side ? &nmB : &nmA;
    if (side) inB[x] = 1; else inA[x] = 1; pos[x] = *nm; mem[(*nm)++] = x; }
static void memDel(int side, int x) { int *mem = side ? memB : memA, *pos = side ? posB : posA, *nm = side ? &nmB : &nmA;
    if (side) inB[x] = 0; else inA[x] = 0; int p = pos[x]; int y = mem[--(*nm)]; mem[p] = y; pos[y] = p; }

static int overlapsAny(int side, int x) {
    int *mem = side ? memB : memA, nm = side ? nmB : nmA; unsigned char *O = side ? OB : OA; int n = side ? nB : nA;
    for (int m = 0; m < nm; m++) if (O[(size_t)x * n + mem[m]]) return 1;
    return 0;
}

static void unmatch(int i, int side) {   /* clears the matching of hub i (side) */
    if (side == 0) { if (pA[i] >= 0) { pB[pA[i]] = -1; pA[i] = -1; } }
    else { if (pB[i] >= 0) { pA[pB[i]] = -1; pB[i] = -1; } }
}

static void readpool(const char *fn, int **sz, int (**out)[16], int *n) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    int nc; if (fscanf(f, "%d", &nc) != 1) exit(2);
    *out = malloc(sizeof(int[16]) * nc); *sz = malloc(4 * nc);
    for (int i = 0; i < nc; i++) { int k; if (fscanf(f, "%d", &k) != 1) exit(2); (*sz)[i] = k;
        for (int a = 0; a < k; a++) if (fscanf(f, "%d", &(*out)[i][a]) != 1) exit(2); }
    fclose(f); *n = nc;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: rescue EDGES POOLA POOLB ITERS T0 T1 LAMBDA SEED OUTPREFIX\n"); return 2; }
    long iters = atol(argv[4]); double T0 = atof(argv[5]), T1 = atof(argv[6]), lam = atof(argv[7]);
    rs ^= (unsigned long long)atoll(argv[8]) * 0x9E3779B97F4A7C15ULL; for (int k = 0; k < 10; k++) rnd64();
    char *outp = argv[9]; (void)outp;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    /* distance-2 sets on each side */
    d2B = calloc((size_t)H * W, 8); d2A = calloc((size_t)H * W, 8);
    for (int y = 0; y < H; y++) { uint64_t *dd = d2B + (size_t)y * W; dd[y >> 6] |= 1ULL << (y & 63);
        for (int i = 0; i < 16; i++) { int x = adjB[y][i]; for (int j = 0; j < 16; j++) { int y2 = adjA[x][j]; dd[y2 >> 6] |= 1ULL << (y2 & 63); } } }
    for (int x = 0; x < H; x++) { uint64_t *dd = d2A + (size_t)x * W; dd[x >> 6] |= 1ULL << (x & 63);
        for (int i = 0; i < 16; i++) { int y = adjA[x][i]; for (int j = 0; j < 16; j++) { int x2 = adjB[y][j]; dd[x2 >> 6] |= 1ULL << (x2 & 63); } } }
    readpool(argv[2], &szA, &NA, &nA);
    readpool(argv[3], &szB, &NB, &nB);
    double t0 = now();
    /* bitsets of the N's and rescue sets */
    uint64_t *bitA = calloc((size_t)nA * W, 8), *bitB = calloc((size_t)nB * W, 8);   /* A-cand N's over B; B-cand N's over A */
    uint64_t *R2A = calloc((size_t)nA * W, 8), *R2B = calloc((size_t)nB * W, 8);
    uint64_t *NbB = calloc((size_t)nB * W, 8), *NaA = calloc((size_t)nA * W, 8);
    for (int i = 0; i < nA; i++) for (int a = 0; a < szA[i]; a++) { int y = NA[i][a]; bitA[(size_t)i * W + (y >> 6)] |= 1ULL << (y & 63);
        uint64_t *dd = d2B + (size_t)y * W, *r = R2A + (size_t)i * W; for (int w = 0; w < W; w++) r[w] |= dd[w];
        uint64_t *na = NaA + (size_t)i * W; for (int b = 0; b < 16; b++) { int x = adjB[y][b]; na[x >> 6] |= 1ULL << (x & 63); } }
    for (int j = 0; j < nB; j++) for (int a = 0; a < szB[j]; a++) { int x = NB[j][a]; bitB[(size_t)j * W + (x >> 6)] |= 1ULL << (x & 63);
        uint64_t *dd = d2A + (size_t)x * W, *r = R2B + (size_t)j * W; for (int w = 0; w < W; w++) r[w] |= dd[w];
        uint64_t *nb = NbB + (size_t)j * W; for (int b = 0; b < 16; b++) { int y = adjA[x][b]; nb[y >> 6] |= 1ULL << (y & 63); } }
    CA = calloc((size_t)nA * nA, 1); OA = calloc((size_t)nA * nA, 1); CB = calloc((size_t)nB * nB, 1); OB = calloc((size_t)nB * nB, 1);
    RA = calloc((size_t)nA * nB, 1); RB = calloc((size_t)nA * nB, 1);
    for (int i = 0; i < nA; i++) for (int k = 0; k < nA; k++) if (i != k) {
        int ov = 0, meet = 0;
        for (int w = 0; w < W && !ov; w++) ov |= (bitA[(size_t)i * W + w] & bitA[(size_t)k * W + w]) != 0;
        for (int a = 0; a < szA[k]; a++) { int y = NA[k][a]; if ((R2A[(size_t)i * W + (y >> 6)] >> (y & 63)) & 1) { meet = 1; break; } }
        OA[(size_t)i * nA + k] = ov; CA[(size_t)i * nA + k] = (!ov && meet); }
    for (int j = 0; j < nB; j++) for (int k = 0; k < nB; k++) if (j != k) {
        int ov = 0, meet = 0;
        for (int w = 0; w < W && !ov; w++) ov |= (bitB[(size_t)j * W + w] & bitB[(size_t)k * W + w]) != 0;
        for (int a = 0; a < szB[k]; a++) { int x = NB[k][a]; if ((R2B[(size_t)j * W + (x >> 6)] >> (x & 63)) & 1) { meet = 1; break; } }
        OB[(size_t)j * nB + k] = ov; CB[(size_t)j * nB + k] = (!ov && meet); }
    /* RA[j][i]: N(A-cand i) meets NbB[j];  RB[i][j]: N(B-cand j) meets NaA[i] */
    for (int j = 0; j < nB; j++) for (int i = 0; i < nA; i++) {
        int hit = 0; for (int a = 0; a < szA[i] && !hit; a++) { int y = NA[i][a]; hit = (NbB[(size_t)j * W + (y >> 6)] >> (y & 63)) & 1; }
        RA[(size_t)j * nA + i] = hit;
        hit = 0; for (int a = 0; a < szB[j] && !hit; a++) { int x = NB[j][a]; hit = (NaA[(size_t)i * W + (x >> 6)] >> (x & 63)) & 1; }
        RB[(size_t)i * nB + j] = hit; }
    long cA = 0, cB = 0, rA = 0, rB = 0; for (long q = 0; q < (long)nA * nA; q++) cA += CA[q]; for (long q = 0; q < (long)nB * nB; q++) cB += CB[q];
    for (long q = 0; q < (long)nA * nB; q++) { rA += RA[q]; rB += RB[q]; }
    fprintf(stderr, "pools A %d B %d; compat density A %.4f B %.4f; rescue density A %.4f B %.4f (%.1fs)\n", nA, nB,
            (double)cA / ((double)nA * nA), (double)cB / ((double)nB * nB), (double)rA / ((double)nA * nB), (double)rB / ((double)nA * nB), now() - t0);
    pA = malloc(4 * nA); pB = malloc(4 * nB); inA = calloc(nA, 4); inB = calloc(nB, 4); memA = malloc(4 * nA); memB = malloc(4 * nB);
    posA = malloc(4 * nA); posB = malloc(4 * nB); flA = calloc(nA, 4); flB = calloc(nB, 4);
    for (int i = 0; i < nA; i++) pA[i] = -1;
    for (int j = 0; j < nB; j++) pB[j] = -1;
    nmA = nmB = 0; V = 0;
    int bestSz = 0, bestNA = 0, bestNB = 0, *bestMA = malloc(4 * nA), *bestMB = malloc(4 * nB), *bestPA = malloc(4 * nA);
    int cur = 0;
    double lastrep = now();
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        if (rnd64() % 10 < 4) {   /* toggle a candidate (on a random side) */
            int side = rnd64() & 1;
            int x = rnd64() % (side ? nB : nA);
            int in = side ? inB[x] : inA[x];
            if (!in && overlapsAny(side, x)) continue;
            int p = in ? (side ? pB[x] : pA[x]) : -1;   /* partner of x (other side) */
            int TA[2], TB[2], nTA = 0, nTB = 0;
            if (side) { TB[nTB++] = x; if (p >= 0) TA[nTA++] = p; } else { TA[nTA++] = x; if (p >= 0) TB[nTB++] = p; }
            int before = evalTouch(TA, nTA, TB, nTB);
            if (in) { unmatch(x, side); if (side) memDel(1, x); else memDel(0, x); }
            else { if (side) memAdd(1, x); else memAdd(0, x); }
            int after = evalTouch(TA, nTA, TB, nTB);
            int dV = after - before, dS = in ? -1 : 1;
            double dsc = dS - lam * dV;
            if (dsc >= 0 || rnd01() < exp(dsc / T)) { V += dV; cur += dS; }
            else {   /* revert */
                if (in) { if (side) memAdd(1, x); else memAdd(0, x); if (p >= 0) { if (side) { pB[x] = p; pA[p] = x; } else { pA[x] = p; pB[p] = x; } } }
                else { if (side) memDel(1, x); else memDel(0, x); }
            }
        } else {                  /* match a random A-member i with a random B-member j */
            if (nmA == 0 || nmB == 0) continue;
            int i = memA[rnd64() % nmA], j = memB[rnd64() % nmB];
            if (pA[i] == j) continue;
            if (szA[i] != 16 || szB[j] != 16) continue;   /* only hubs with one spare slot can take a hub-hub edge */
            int i0 = pA[i], j0 = pB[j];          /* old partners: i0 (B-hub) of i, j0 (A-hub) of j */
            int TA[2], TB[2], nTA = 0, nTB = 0;
            TA[nTA++] = i; if (j0 >= 0) TA[nTA++] = j0;
            TB[nTB++] = j; if (i0 >= 0) TB[nTB++] = i0;
            int before = evalTouch(TA, nTA, TB, nTB);
            if (i0 >= 0) pB[i0] = -1;
            if (j0 >= 0) pA[j0] = -1;
            pA[i] = j; pB[j] = i;
            int after = evalTouch(TA, nTA, TB, nTB);
            int dV = after - before;
            if (dV <= 0 || rnd01() < exp(-lam * dV / T)) { V += dV; }
            else {   /* revert */
                pA[i] = i0; pB[j] = j0; if (j0 >= 0) pA[j0] = j; if (i0 >= 0) pB[i0] = i;
            }
        }
        if (V == 0 && cur > bestSz) {
            bestSz = cur; bestNA = nmA; bestNB = nmB;
            memcpy(bestMA, memA, 4 * nmA); memcpy(bestMB, memB, 4 * nmB);
            for (int m = 0; m < nmA; m++) bestPA[m] = pA[memA[m]];
            fprintf(stderr, "feasible: |A|=%d |B|=%d total %d (it %ld, %.1fs)\n", nmA, nmB, bestSz, it, now() - t0);
        }
        if (now() - lastrep > 10) { lastrep = now(); fprintf(stderr, "it %ld T %.3f |A|=%d |B|=%d V=%d best %d\n", it, T, nmA, nmB, V, bestSz); }
    }
    if (bestSz > 0) {
        char fn[512];
        snprintf(fn, sizeof fn, "%s_A.txt", outp); FILE *g = fopen(fn, "w");
        for (int m = 0; m < bestNA; m++) { int i = bestMA[m]; for (int a = 0; a < szA[i]; a++) fprintf(g, "%d ", NA[i][a] + H); fprintf(g, "\n"); }
        fclose(g);
        snprintf(fn, sizeof fn, "%s_B.txt", outp); g = fopen(fn, "w");
        for (int m = 0; m < bestNB; m++) { int j = bestMB[m]; for (int a = 0; a < szB[j]; a++) fprintf(g, "%d ", NB[j][a]); fprintf(g, "\n"); }
        fclose(g);
        snprintf(fn, sizeof fn, "%s_HH.txt", outp); g = fopen(fn, "w");
        for (int m = 0; m < bestNA; m++) { int i = bestMA[m]; int j = bestPA[m]; if (j < 0) continue;
            int pos = -1; for (int q = 0; q < bestNB; q++) if (bestMB[q] == j) { pos = q; break; }
            if (pos >= 0) fprintf(g, "%d %d\n", m, pos); }
        fclose(g);
    }
    printf("best feasible total %d (A and B of the best state: see %s_A.txt %s_B.txt)\n", bestSz, outp, outp);
    return 0;
}
