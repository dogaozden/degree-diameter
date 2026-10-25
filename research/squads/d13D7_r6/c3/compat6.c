/* compat6.c: card c3 (squad round 6). Orbit compatibility bitsets for the orbit graph of a group of isometries.
   compat_bits(K, W, starts, pts, RT, out):
     K good orbits, W = ceil(K/64); points of orbit k are pts[starts[k] .. starts[k+1]-1] (7 bytes each, the row
     PJ = (P J) mod 11 of the point, so B(x, r) = sum_i PJ[x][i] * r[i] mod 11); RT is 7 x K bytes, RT[i*K + j] =
     coordinate i of the representative of good orbit j.  out[k*W + w] bit b set iff orbits k and j = 64w+b are
     compatible (every point of orbit k is non-perpendicular to rep j).  The diagonal is 0 (rep is orthogonal to itself).
   Build: gcc -O3 -march=native -shared -fPIC -o libcompat6.so compat6.c                                               */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void compat_bits(int K, int W, const int64_t *starts, const uint8_t *pts, const uint8_t *RT, uint64_t *out) {
    uint8_t *zf = malloc((size_t)K);
    for (int k = 0; k < K; k++) {
        memset(zf, 0, (size_t)K);
        for (int64_t x = starts[k]; x < starts[k + 1]; x++) {
            const uint8_t *p = pts + 7 * x;
            const uint32_t p0 = p[0], p1 = p[1], p2 = p[2], p3 = p[3], p4 = p[4], p5 = p[5], p6 = p[6];
            const uint8_t *r0 = RT, *r1 = RT + K, *r2 = RT + 2 * K, *r3 = RT + 3 * K;
            const uint8_t *r4 = RT + 4 * K, *r5 = RT + 5 * K, *r6 = RT + 6 * K;
            for (int j = 0; j < K; j++) {
                uint32_t v = p0 * r0[j] + p1 * r1[j] + p2 * r2[j] + p3 * r3[j] + p4 * r4[j] + p5 * r5[j] + p6 * r6[j];
                zf[j] |= (uint8_t)(v % 11u == 0u);
            }
        }
        uint64_t *row = out + (size_t)k * W;
        memset(row, 0, 8 * (size_t)W);
        for (int j = 0; j < K; j++) if (!zf[j]) row[j >> 6] |= 1ULL << (j & 63);
    }
    free(zf);
}
