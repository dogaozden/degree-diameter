/* typeanal EDGES OUTPREFIX: line-type compatibility on G (side B = T side, hubs on side A).
 * Type k = (controller cv, direction c), 6 best directions per cv (as hubpack). Line (k,o) = 4 points of coset o.
 * M[k][k2] = #offset pairs (o,o2) in 64x64 for which some point of line k2 is within distance 2 (in G, B side) of line k.
 * 4096 = always compatible at line level. Output: prefix.M (uint16 nt*nt), prefix.types, prefix.clique. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define H 16896
#define W 264
#define K 6
#define NT (66*K)
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static int P[NT][64][4];
static uint16_t M[NT * NT];
static uint64_t *R;
static int tcv[NT], tdir[NT];
static int adjc[NT][NT];
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjB[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjA[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjB[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int nt = 0;
    for (int cv = 0; cv < 66; cv++) {
        double sc[85];
        for (int di = 0; di < nd; di++) { long tot = 0;
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; uint64_t tmp[W]; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ scal(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                tot += popw(tmp); }
            sc[di] = tot / 8.0; }
        for (int k = 0; k < K; k++) { int bi = 0; for (int di = 1; di < nd; di++) if (sc[di] > sc[bi]) bi = di; sc[bi] = -1; tcv[nt] = cv; tdir[nt] = dirs[bi]; nt++; }
    }
    R = calloc((size_t)nt * 64 * W, 8);
    for (int k = 0; k < nt; k++) {
        int seen[256] = {0}, o = 0, cv = tcv[k], c = tdir[k];
        for (int y = 0; y < 256; y++) if (!seen[y]) {
            uint64_t *r = R + ((size_t)k * 64 + o) * W;
            for (int l = 0; l < 4; l++) { int z = y ^ scal(l, c); seen[z] = 1; P[k][o][l] = cv * 256 + z;
                uint64_t *dd = d2 + (size_t)(cv * 256 + z) * W; for (int w = 0; w < W; w++) r[w] |= dd[w]; }
            o++; }
        if (o != 64) { fprintf(stderr, "bad line count %d\n", o); return 4; }
    }
    for (int k = 0; k < nt; k++) for (int o = 0; o < 64; o++) {
        uint64_t *r = R + ((size_t)k * 64 + o) * W;
        for (int k2 = 0; k2 < nt; k2++) for (int o2 = 0; o2 < 64; o2++) {
            int any = 0; for (int l = 0; l < 4 && !any; l++) { int x = P[k2][o2][l]; if ((r[x >> 6] >> (x & 63)) & 1) any = 1; }
            M[k * nt + k2] += any; } }
    char fn[512]; sprintf(fn, "%s.M", argv[2]); FILE *g = fopen(fn, "wb"); fwrite(M, 2, nt * nt, g); fclose(g);
    sprintf(fn, "%s.types", argv[2]); g = fopen(fn, "w"); for (int k = 0; k < nt; k++) fprintf(g, "%d %d\n", tcv[k], tdir[k]); fclose(g);
    long hist[5] = {0}; int self4096 = 0;
    for (int k = 0; k < nt; k++) { if (M[k * nt + k] == 4096) self4096++;
        for (int k2 = k + 1; k2 < nt; k2++) { int m = M[k * nt + k2]; if (m == 4096) hist[0]++; else if (m >= 3500) hist[1]++; else if (m >= 2000) hist[2]++; else if (m >= 500) hist[3]++; else hist[4]++; } }
    printf("types %d, self-always-compatible %d\n", nt, self4096);
    printf("pairs: =1: %ld  >=0.85: %ld  >=0.49: %ld  >=0.12: %ld  lower: %ld\n", hist[0], hist[1], hist[2], hist[3], hist[4]);
    /* compatibility graph on types: edge iff always compatible (4096) */
    for (int a = 0; a < nt; a++) for (int b = 0; b < nt; b++) adjc[a][b] = (a != b && M[a * nt + b] == 4096 && M[a * nt + a] == 4096 && M[b * nt + b] == 4096);
    int *best = malloc(sizeof(int) * nt), nbest = 0, cur[NT], ncur; int ok[NT];
    for (int it = 0; it < 20000; it++) {
        int ord[NT]; for (int i = 0; i < nt; i++) ord[i] = i;
        for (int i = nt - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        ncur = 0; for (int i = 0; i < nt; i++) ok[i] = (M[ord[i] * nt + ord[i]] == 4096);
        for (int i = 0; i < nt; i++) { int v = ord[i]; if (!ok[i]) continue; int good = 1;
            for (int a = 0; a < ncur && good; a++) if (!adjc[v][cur[a]]) good = 0;
            if (good) cur[ncur++] = v; }
        if (ncur > nbest) { nbest = ncur; memcpy(best, cur, sizeof(int) * ncur); }
    }
    printf("greedy always-compatible clique over types: %d\n", nbest);
    sprintf(fn, "%s.clique", argv[2]); g = fopen(fn, "w");
    for (int a = 0; a < nbest; a++) fprintf(g, "%d %d\n", tcv[best[a]], tdir[best[a]]);
    fclose(g);
    return 0;
}
