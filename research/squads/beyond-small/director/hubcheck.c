/* hubcheck EDGES HUBFILE SIDE: for each hub (old neighbours, global ids), count S-vertices farther than 3 from N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define H 16896
#define W 264
static int adjA[H][16], adjB[H][16];
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); long n, u, v; int side = atoi(argv[3]); if (fscanf(f, "%ld", &n) != 1) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    int (*adjT)[16] = side == 0 ? adjB : adjA, (*adjS)[16] = side == 0 ? adjA : adjB;
    f = fopen(argv[2], "r"); char line[4096]; int nh = 0, bad = 0; long tot = 0;
    while (fgets(line, sizeof line, f)) { int N[20], m = 0; char *p = line; int x, k; while (m < 20 && sscanf(p, "%d%n", &x, &k) == 1) { N[m++] = x - (side == 0 ? H : 0); p += k; }
        if (!m) continue; uint64_t cov[W]; memset(cov, 0, sizeof cov);
        for (int i = 0; i < m; i++) { int t = N[i];
            for (int a = 0; a < 16; a++) { int s = adjT[t][a]; cov[s >> 6] |= 1ULL << (s & 63);
                for (int b = 0; b < 16; b++) { int t2 = adjS[s][b]; for (int c = 0; c < 16; c++) { int s2 = adjT[t2][c]; cov[s2 >> 6] |= 1ULL << (s2 & 63); } } } }
        int c = 0; for (int w = 0; w < W; w++) c += __builtin_popcountll(cov[w]); nh++; if (c < H) { bad++; tot += H - c; } }
    printf("%d hubs, %d not covering (total uncovered %ld)\n", nh, bad, tot);
    return 0;
}
