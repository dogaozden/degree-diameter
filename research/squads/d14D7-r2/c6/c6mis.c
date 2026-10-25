/* c6mis.c (card c6): exact / heuristic maximum flag packings for GH(q) (one matching).
   Flags = incident pairs (p,l). Two flags conflict iff their point zones or their line zones meet
   (zone definitions as in ../../../cell147/units/pack.c). A packing = independent set in the conflict graph.
   Build: gcc -O3 -march=native -o c6mis c6mis.c -lm
   Usage: c6mis GHFILE MODE SECONDS SEED OUTFLAGS [INIT]
     MODE ils : iterated local search (ARW-style: (1,2)-swaps, perturbation, acceptance) ; writes best found
     MODE bb  : exact branch and bound (max clique in the compatibility graph, BBMC-style colouring bound),
                flag 0 forced into the packing (flag-transitivity of G2(q)); INIT (optional) gives the lower bound
                file: best known packing whose size is used as the starting target (search for size > |INIT|).
                Prints "BB-DONE exhaustive=1 max=..." if the search space was exhausted within SECONDS.
   Output lines: "p l". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int P, q, Q1, ZN, NF, W, ZL_CNT;
static int32_t *LP, *PL, *fp, *fl, *ZPt, *ZLn;
static uint64_t *adj;               /* conflict graph, NF rows of W words */
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static inline int isconf(int u, int v) { return (adj[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1; }
static inline void setconf(int u, int v) { adj[(size_t)u * W + (v >> 6)] |= 1ULL << (v & 63); }

static int zoneP(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue; for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zoneL(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue; for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }

/* ---------------- ILS state ---------------- */
static char *inS; static int *tight; static int *Slist, nS = 0; static int *posS;
static void addv(int v) { inS[v] = 1; posS[v] = nS; Slist[nS++] = v;
    for (int w = 0; w < W; w++) { uint64_t x = adj[(size_t)v * W + w]; while (x) { int b = __builtin_ctzll(x); x &= x - 1; tight[w * 64 + b]++; } } }
static void remv(int v) { inS[v] = 0; int i = posS[v]; Slist[i] = Slist[--nS]; posS[Slist[i]] = i;
    for (int w = 0; w < W; w++) { uint64_t x = adj[(size_t)v * W + w]; while (x) { int b = __builtin_ctzll(x); x &= x - 1; tight[w * 64 + b]--; } } }
static void clearS(void) { while (nS) remv(Slist[nS - 1]); }
static int localsearch(void) {
    int improved = 1;
    while (improved) {
        improved = 0;
        int off = rndi(NF);
        for (int i = 0; i < NF; i++) { int v = (i + off) % NF; if (!inS[v] && tight[v] == 0) { addv(v); improved = 1; } }
        if (improved) continue;
        /* (1,2)-swaps */
        int start = rndi(nS > 0 ? nS : 1);
        for (int k = 0; k < nS && !improved; k++) {
            int x = Slist[(k + start) % nS];
            int L[4096], nl = 0;
            for (int w = 0; w < W; w++) { uint64_t bits = adj[(size_t)x * W + w]; while (bits) { int b = __builtin_ctzll(bits); bits &= bits - 1; int u = w * 64 + b; if (!inS[u] && tight[u] == 1 && nl < 4096) L[nl++] = u; } }
            if (nl < 2) continue;
            int off2 = rndi(nl);
            for (int i = 0; i < nl && !improved; i++) for (int j = i + 1; j < nl && !improved; j++) {
                int u = L[(i + off2) % nl], v = L[(j + off2) % nl];
                if (!isconf(u, v)) { remv(x); addv(u); addv(v); improved = 1; }
            }
        }
    }
    return nS;
}

static void write_sol(const char *fn, int *list, int n) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    for (int i = 0; i < n; i++) { int v = list[i]; fprintf(f, "%d %d\n", fp[v], fl[v]); }
    fclose(f);
}

/* ---------------- exact B&B (BBMC style) ---------------- */
static long long nodes = 0; static double tlimit; static clock_t c0; static int timed_out = 0;
static int best = 0; static int *bestSet, bestN = 0; static int *cur, curN = 0;
static inline int popc(const uint64_t *a) { int c = 0; for (int w = 0; w < W; w++) c += __builtin_popcountll(a[w]); return c; }
static void bb(uint64_t *R, int depth) {
    nodes++;
    if ((nodes & 1023) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > tlimit) { timed_out = 1; }
    if (timed_out) return;
    /* colour R: classes are sets of pairwise conflicting flags (cliques of the conflict graph) */
    int nR = popc(R);
    if (nR == 0) { if (depth > best) { best = depth; bestN = curN; memcpy(bestSet, cur, sizeof(int) * curN);
            fprintf(stderr, "new best %d (nodes %lld)\n", best, nodes); } return; }
    int *order = malloc(sizeof(int) * nR), *col = malloc(sizeof(int) * nR);
    uint64_t *U = malloc(8 * W), *Qs = malloc(8 * W);
    memcpy(U, R, 8 * W);
    int k = 0, colour = 0;
    while (k < nR) {
        colour++;
        memcpy(Qs, U, 8 * W);
        for (int w = 0; w < W; w++) while (Qs[w]) {
            int b = __builtin_ctzll(Qs[w]); int v = w * 64 + b;
            Qs[w] &= Qs[w] - 1; U[w] &= ~(1ULL << b);
            order[k] = v; col[k] = colour; k++;
            /* next member of the same colour must conflict with v (compatible vertices cannot share a colour) */
            for (int x = 0; x < W; x++) Qs[x] &= adj[(size_t)v * W + x];
        }
    }
    uint64_t *newR = malloc(8 * W);
    for (int i = nR - 1; i >= 0; i--) {
        if (depth + col[i] <= best) break;
        int v = order[i];
        /* branch: include v; candidates = compatible with v among R (still unprocessed) */
        for (int x = 0; x < W; x++) newR[x] = R[x] & ~adj[(size_t)v * W + x];
        newR[v >> 6] &= ~(1ULL << (v & 63));
        cur[curN++] = v;
        bb(newR, depth + 1);
        curN--;
        if (timed_out) break;
        R[v >> 6] &= ~(1ULL << (v & 63));   /* exclude v from the rest of this node */
    }
    free(order); free(col); free(U); free(Qs); free(newR);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: c6mis GHFILE ils|bb SECONDS SEED OUTFLAGS [INIT]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; ZN = q * q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    NF = P * Q1; W = (NF + 63) / 64;
    fp = malloc(sizeof(int32_t) * NF); fl = malloc(sizeof(int32_t) * NF);
    for (int p = 0; p < P; p++) for (int a = 0; a < Q1; a++) { int f2 = p * Q1 + a; fp[f2] = p; fl[f2] = PL[p * Q1 + a]; }
    ZPt = malloc(sizeof(int32_t) * (size_t)NF * ZN); ZLn = malloc(sizeof(int32_t) * (size_t)NF * ZN);
    int tmp[512];
    for (int v = 0; v < NF; v++) {
        int n1 = zoneP(fp[v], fl[v], tmp); if (n1 != ZN) { fprintf(stderr, "zone size %d\n", n1); return 3; }
        memcpy(&ZPt[(size_t)v * ZN], tmp, sizeof(int) * ZN);
        int n2 = zoneL(fp[v], fl[v], tmp); if (n2 != ZN) { fprintf(stderr, "line zone size %d\n", n2); return 3; }
        memcpy(&ZLn[(size_t)v * ZN], tmp, sizeof(int) * ZN);
    }
    /* incidence lists: flags whose point zone contains x, flags whose line zone contains K */
    int cap = (q + 1) * (q * q + 1);
    int32_t *LPf = malloc(sizeof(int32_t) * (size_t)P * cap), *LLf = malloc(sizeof(int32_t) * (size_t)P * cap);
    int *cntP = calloc(P, sizeof(int)), *cntL = calloc(P, sizeof(int));
    for (int v = 0; v < NF; v++) for (int i = 0; i < ZN; i++) {
        int x = ZPt[(size_t)v * ZN + i]; if (cntP[x] >= cap) { fprintf(stderr, "cap P\n"); return 3; } LPf[(size_t)x * cap + cntP[x]++] = v;
        int K = ZLn[(size_t)v * ZN + i]; if (cntL[K] >= cap) { fprintf(stderr, "cap L\n"); return 3; } LLf[(size_t)K * cap + cntL[K]++] = v; }
    adj = calloc((size_t)NF * W, 8);
    if (!adj) { fprintf(stderr, "no memory\n"); return 3; }
    for (int x = 0; x < P; x++) {
        for (int i = 0; i < cntP[x]; i++) for (int j = 0; j < cntP[x]; j++) { int a = LPf[(size_t)x * cap + i], b = LPf[(size_t)x * cap + j]; if (a != b) setconf(a, b); }
        for (int i = 0; i < cntL[x]; i++) for (int j = 0; j < cntL[x]; j++) { int a = LLf[(size_t)x * cap + i], b = LLf[(size_t)x * cap + j]; if (a != b) setconf(a, b); }
    }
    long long deg = 0; for (int v = 0; v < NF; v++) deg += popc(&adj[(size_t)v * W]);
    fprintf(stderr, "P=%d q=%d flags=%d conflict-degree avg %.1f (density %.3f)\n", P, q, NF, (double)deg / NF, (double)deg / NF / (NF - 1));
    double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    char *mode = argv[2];
    inS = calloc(NF, 1); tight = calloc(NF, sizeof(int)); Slist = malloc(sizeof(int) * NF); posS = malloc(sizeof(int) * NF);
    int *bestL = malloc(sizeof(int) * NF); int nBest = 0;
    if (!strcmp(mode, "ils")) {
        int *saved = malloc(sizeof(int) * NF); int nSaved = 0;
        /* start: greedy random maximal packing */
        localsearch(); nBest = nS; memcpy(bestL, Slist, sizeof(int) * nS);
        clock_t t0 = clock(); long it = 0;
        while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
            it++;
            nSaved = nS; memcpy(saved, Slist, sizeof(int) * nS);
            /* perturb: force-insert a random non-solution vertex (occasionally two) */
            int kk = (rndi(8) == 0) ? 2 : 1;
            for (int t = 0; t < kk; t++) {
                int v; do { v = rndi(NF); } while (inS[v]);
                for (int w = 0; w < W; w++) { uint64_t x = adj[(size_t)v * W + w]; while (x) { int b = __builtin_ctzll(x); x &= x - 1; int u = w * 64 + b; if (inS[u]) remv(u); } }
                addv(v);
            }
            localsearch();
            if (nS > nBest) { nBest = nS; memcpy(bestL, Slist, sizeof(int) * nS); write_sol(argv[5], bestL, nBest); fprintf(stderr, "ils it %ld best %d (t=%.1fs)\n", it, nBest, (double)(clock() - t0) / CLOCKS_PER_SEC); }
            if (nS < nSaved && (nSaved - nS >= 2 || rndi(3) != 0)) {   /* revert most worsening moves */
                clearS(); for (int i = 0; i < nSaved; i++) addv(saved[i]);
            }
        }
        fprintf(stderr, "ILS done: %ld iterations, best %d\n", it, nBest);
        printf("ILS best %d\n", nBest);
    } else {   /* bb */
        tlimit = secs; c0 = clock();
        int lb = 0;
        if (argc > 6) { FILE *g = fopen(argv[6], "r"); int a, b; int *fidx = NULL; (void)fidx;
            /* map (p,l) to flag id */
            while (g && fscanf(g, "%d %d", &a, &b) == 2) lb++; if (g) fclose(g); }
        bestSet = malloc(sizeof(int) * NF); cur = malloc(sizeof(int) * NF);
        best = lb;   /* only look for packings strictly larger than the lower bound */
        uint64_t *R = calloc(W, 8);
        /* flag 0 forced in (flag-transitivity): R = flags compatible with flag 0, not 0 itself */
        int f0 = getenv("FORCE") ? atoi(getenv("FORCE")) : 0;   /* forced flag (default 0) */
        for (int v = 0; v < NF; v++) if (v != f0 && !isconf(f0, v)) R[v >> 6] |= 1ULL << (v & 63);
        cur[0] = f0; curN = 1;
        bb(R, 1);
        if (bestN > 0) { memcpy(bestL, bestSet, sizeof(int) * bestN); nBest = bestN; }
        else nBest = 0;
        printf("BB-DONE exhaustive=%d best_found_above_lb=%d lb=%d nodes=%lld time=%.1fs\n", !timed_out, bestN, lb, nodes, (double)(clock() - c0) / CLOCKS_PER_SEC);
    }
    if (nBest > 0) write_sol(argv[5], bestL, nBest);
    printf("N=%d\n", nBest);
    return 0;
}
