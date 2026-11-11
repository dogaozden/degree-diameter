/* mcs: tabu max-clique search (MN/TS style: add / swap / drop moves, tabu tenures, restarts) on the hub
 * compatibility graph dumped by hubdump.
 * usage: mcs CANDS BITS SECS SEED OUT [L=20000] [TT=10] [PDROP=2]
 * OUT: one hub per line, global old-vertex ids (side 0: +H), same format as hubpack. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static uint64_t rs = 0x2545F4914F6CDD1DULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int nc, CW, side, H;
static uint64_t *B;                 /* compat bitsets */
static int *miss, *mem, *pos;       /* miss[v] = #members not adjacent to v; mem = members; pos = index in mem or -1 */
static int *naoff, *na;             /* non-neighbour lists */
static int k = 0;

static inline int adj(int a, int b) { return (B[(size_t)a * CW + (b >> 6)] >> (b & 63)) & 1; }
static void add_v(int v) {
    pos[v] = k; mem[k++] = v;
    for (int p = naoff[v]; p < naoff[v + 1]; p++) miss[na[p]]++;
}
static void rem_v(int v) {
    int i = pos[v]; mem[i] = mem[--k]; pos[mem[i]] = i; pos[v] = -1;
    for (int p = naoff[v]; p < naoff[v + 1]; p++) miss[na[p]]--;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: mcs CANDS BITS SECS SEED OUT [L] [TT] [PDROP]\n"); return 2; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    long L = argc > 6 ? atol(argv[6]) : 20000; int TT = argc > 7 ? atoi(argv[7]) : 10; int PDROP = argc > 8 ? atoi(argv[8]) : 2;
    /* candidates */
    FILE *f = fopen(argv[1], "r"); int side_ = 0;
    if (fscanf(f, "%d %d %d", &nc, &side_, &H) != 3) return 3; side = side_;
    int *csz = malloc(4 * nc), *coff = malloc(4 * (nc + 1)); int *cv = malloc(4 * 17 * (size_t)nc); int nt = 0;
    for (int i = 0; i < nc; i++) { if (fscanf(f, "%d", &csz[i]) != 1) return 3; coff[i] = nt;
        for (int k2 = 0; k2 < csz[i]; k2++) { if (fscanf(f, "%d", &cv[nt]) != 1) return 3; nt++; } }
    coff[nc] = nt; fclose(f);
    /* compat */
    f = fopen(argv[2], "rb"); int nc2, CW2;
    if (fread(&nc2, sizeof nc2, 1, f) != 1 || fread(&CW2, sizeof CW2, 1, f) != 1 || nc2 != nc) return 3; CW = CW2;
    B = malloc((size_t)nc * CW * 8); if (fread(B, 8, (size_t)nc * CW, f) != (size_t)nc * CW) return 3; fclose(f);
    /* non-neighbour lists */
    naoff = malloc(4 * (nc + 1)); long tot = 0;
    for (int i = 0; i < nc; i++) { naoff[i] = (int)tot; int c = 0;
        for (int w = 0; w < CW; w++) c += __builtin_popcountll(B[(size_t)i * CW + w]);
        tot += nc - 1 - c; }
    naoff[nc] = (int)tot; na = malloc(4 * (tot + 1));
    for (int i = 0; i < nc; i++) { int p = naoff[i];
        for (int j = 0; j < nc; j++) if (j != i && !adj(i, j)) na[p++] = j; }
    fprintf(stderr, "loaded %d candidates, non-adjacent pairs %ld\n", nc, tot);
    miss = calloc(nc, 4); mem = malloc(4 * nc); pos = malloc(4 * nc); for (int i = 0; i < nc; i++) pos[i] = -1;
    long *tabu = calloc(nc, sizeof(long)); int *bestset = malloc(4 * nc); int bestk = 0;
    double t0 = now(); long it = 0, lastimp = 0, restarts = 0;
    add_v((int)(rnd() % nc));
    while (1) {
        if ((it & 255) == 0 && now() - t0 > secs) break;
        it++;
        int nadd = 0, addpick = -1, nswap = 0, swappick = -1;
        for (int v = 0; v < nc; v++) {
            if (pos[v] >= 0) continue;
            int m = miss[v];
            if (m == 0) { if (tabu[v] <= it || k + 1 > bestk) { nadd++; if (rnd() % nadd == 0) addpick = v; } }
            else if (m == 1 && tabu[v] <= it) { nswap++; if (rnd() % nswap == 0) swappick = v; }
        }
        if (addpick >= 0) add_v(addpick);
        else if (swappick >= 0 && (int)(rnd() % 100) >= PDROP) {
            int v = swappick, u = -1;
            for (int i = 0; i < k; i++) if (!adj(v, mem[i])) { u = mem[i]; break; }
            rem_v(u); tabu[u] = it + TT + (long)(rnd() % (TT + 1)); add_v(v);
        } else if (k > 0) {
            int u = mem[rnd() % k]; rem_v(u); tabu[u] = it + TT + (long)(rnd() % (TT + 1));
        }
        if (k > bestk) { bestk = k; memcpy(bestset, mem, 4 * k); lastimp = it;
            fprintf(stderr, "best %d (it %ld, restarts %ld, %.1fs)\n", bestk, it, restarts, now() - t0); }
        if (it - lastimp > L) {   /* restart: empty clique, random seed vertex */
            while (k > 0) rem_v(mem[k - 1]);
            add_v((int)(rnd() % nc)); lastimp = it; restarts++;
        }
    }
    /* write best packing */
    FILE *g = fopen(argv[5], "w");
    for (int a = 0; a < bestk; a++) { int i = bestset[a]; for (int q = coff[i]; q < coff[i] + csz[i]; q++) fprintf(g, "%d ", cv[q] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    printf("side %d candidates %d best packing %d hubs (iters %ld, restarts %ld, %.1fs)\n", side, nc, bestk, it, restarts, now() - t0);
    return 0;
}
