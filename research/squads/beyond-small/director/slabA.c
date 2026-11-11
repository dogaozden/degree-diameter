/* slabA: step A of the slab design (director, job beyond-small).
 * For each fibre f on side T (T = B for side 0: hubs on A with old neighbours in B; T = A for side 1), search triples
 * (c, z, z') of directions in F4^4 so that
 *   - a slab S = y0 + span(c, z) has a distance-<=2 set (inside T) that contains as many whole T-fibres as possible,
 *   - a hyperplane P = y0 + span(c, z, z') has a neighbourhood (in S-side) that contains whole S-fibres (ideally 4),
 *   - lines y + F4 c have large distance-3 balls (good for hub covers).
 * Prints, per fibre, the best triple and its scores; writes them to OUT (one line per fibre: f c z z' fullD2 fullDom).
 * usage: slabA EDGES SIDE TRIALS SEED OUT */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define H 16896
#define W 264
static int MINDV = 10;
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static int (*adjT)[16], (*adjS)[16];
static uint64_t *d2, *ball;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static int fullfibres(const uint64_t *a) { int c = 0; for (int f = 0; f < 66; f++) { int ok = 1; for (int w = f * 4; w < f * 4 + 4; w++) if (a[w] != ~0ULL) ok = 0; c += ok; } return c; }
/* span membership: is d in span of the given vectors (over F4)? brute force small spans */
static int span2(int a, int b, int *out) { int n = 0; for (int l = 0; l < 4; l++) for (int m = 0; m < 4; m++) out[n++] = scal(l, a) ^ scal(m, b); return n; }
int main(int argc, char **argv) {
    int side = atoi(argv[2]), trials = atoi(argv[3]); if (getenv("MINDV")) MINDV = atoi(getenv("MINDV")); rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    adjT = side == 0 ? adjB : adjA; adjS = side == 0 ? adjA : adjB;
    d2 = calloc((size_t)H * W, 8); ball = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) { uint64_t *dd = d2 + (size_t)t * W, *bl = ball + (size_t)t * W; dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjT[t][i]; bl[s >> 6] |= 1ULL << (s & 63); for (int j = 0; j < 16; j++) { int t2 = adjS[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b; for (int i = 0; i < 16; i++) { int s = adjT[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } } }
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    FILE *g = fopen(argv[5], "w");
    long totD2 = 0, totDom = 0;
    for (int fb = 0; fb < 66; fb++) {
        int best = -1, bc = 0, bz = 0, bz2 = 0, bD2 = 0, bDom = 0, bBall = 0;
        for (int tr = 0; tr < trials; tr++) {
            int c = dirs[rnd() % nd], z = dirs[rnd() % nd], z2 = dirs[rnd() % nd];
            int sp[16]; span2(c, z, sp); int dep = 0; for (int i = 1; i < 16; i++) if (sp[i] == 0) dep = 1; if (dep) continue;   /* c, z independent */
            int in = 0; for (int i = 0; i < 16; i++) for (int l = 1; l < 4; l++) if ((sp[i] ^ scal(l, z2)) == 0) in = 1; if (in) continue;
            /* slab D2: worst over the 16 parallel slabs is costly; use y0 = 0 and y0 = random, take min */
            int mD2 = 99;
            for (int rep = 0; rep < 2; rep++) { int y0 = rep ? (rnd() & 255) : 0; uint64_t acc[W]; memset(acc, 0, sizeof acc);
                for (int i = 0; i < 16; i++) { int t = fb * 256 + (y0 ^ sp[i]); uint64_t *dd = d2 + (size_t)t * W; for (int w = 0; w < W; w++) acc[w] |= dd[w]; }
                int fu = fullfibres(acc); if (fu < mD2) mD2 = fu; }
            /* hyperplane domination: neighbours in S of the 64 points y0 + span(c,z,z2), y0 = 0 */
            uint64_t nb[W]; memset(nb, 0, sizeof nb);
            for (int i = 0; i < 16; i++) for (int l = 0; l < 4; l++) { int t = fb * 256 + (sp[i] ^ scal(l, z2)); for (int k = 0; k < 16; k++) { int s = adjT[t][k]; nb[s >> 6] |= 1ULL << (s & 63); } }
            int dom = fullfibres(nb);
            /* line ball for direction c */
            uint64_t lb[W]; memset(lb, 0, sizeof lb); for (int l = 0; l < 4; l++) { int t = fb * 256 + scal(l, c); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) lb[w] |= bl[w]; }
            int lball = popw(lb);
            int score = (dom == 4 && mD2 >= MINDV) ? 100000 + lball : dom * 1000 + mD2 * 100 + lball / 100;
            if (score > best) { best = score; bc = c; bz = z; bz2 = z2; bD2 = mD2; bDom = dom; bBall = lball; }
        }
        fprintf(g, "%d %d %d %d %d %d %d\n", fb, bc, bz, bz2, bD2, bDom, bBall);
        totD2 += bD2; totDom += bDom;
        if (fb < 6) printf("fibre %d: c %d z %d z' %d slab-D2 full fibres %d, hyperplane dominates %d full fibres, line ball %d\n", fb, bc, bz, bz2, bD2, bDom, bBall);
    }
    fclose(g);
    printf("mean slab-D2 full fibres %.2f, mean hyperplane full fibres %.2f\n", totD2 / 66.0, totDom / 66.0);
    return 0;
}
