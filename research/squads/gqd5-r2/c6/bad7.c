/* bad7.c: all-pairs bad-pair counter for card c6 (bit-parallel BFS, same definition as c19/bad.c).
   allbad(n, m, eu, ev, D, pairs, maxpairs): returns the number of UNORDERED pairs {u,v}, u != v, with dist > D
   (unreachable counts). Writes up to maxpairs of them into pairs[2*i], pairs[2*i+1] (u < v). */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
long allbad(int n, int m, const int32_t *eu, const int32_t *ev, int D, int32_t *pairs, int maxpairs) {
    int W = (n + 63) / 64;
    uint64_t *cur = calloc((size_t)n * W, 8), *nxt = calloc((size_t)n * W, 8);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= (uint64_t)1 << (v % 64);
    for (int k = 0; k < D; k++) {
        memcpy(nxt, cur, (size_t)n * W * 8);
        for (int i = 0; i < m; i++) {
            uint64_t *a = nxt + (size_t)eu[i] * W; const uint64_t *b = cur + (size_t)ev[i] * W;
            uint64_t *c = nxt + (size_t)ev[i] * W; const uint64_t *d = cur + (size_t)eu[i] * W;
            for (int w = 0; w < W; w++) { a[w] |= b[w]; c[w] |= d[w]; }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long ordered = 0; long np_ = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = cur + (size_t)v * W;   /* bit u set iff dist(u,v) <= D */
        long cnt = 0;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(row[w]);
        ordered += (long)n - cnt;
        if (pairs) for (int u = 0; u < v; u++) {
            if (!((row[u / 64] >> (u % 64)) & 1)) {
                if (np_ < maxpairs) { pairs[2 * np_] = u; pairs[2 * np_ + 1] = v; }
                np_++;
            }
        }
    }
    free(cur); free(nxt);
    return ordered / 2;   /* ordered count is even: each unordered pair counted twice */
}
