/* meta_haar_climb.c (table-audit-2): hill climbing for a Haar graph H(G, S) of G = Z_m x|_r Z_k with diameter <= D, for
   groups where haar_gen3 cannot run (no element of order 2..63, so its coset bitsets degenerate and it runs out of
   memory).  S = {e} + d-1 elements.  Cost = number of vertices at distance > D from (e,A) plus from (e,B) (bitset BFS,
   level by level, element (a,j) indexed j*m + a).  Move: replace one non-identity generator by a random element;
   keep the move if the cost does not increase.  Writes a haar_gen3-style solution file when the cost reaches 0 (to be
   checked by meta_haar_check / meta_haar_bits / meta_haar_pull, which are independent of this file).
   OpenMP over the frontier words (OMP_NUM_THREADS).
   Usage: meta_haar_climb m k r d D seed iters OUT.sol */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static uint64_t m, k, N, W, *rp, rs = 0x9E3779B97F4A7C15ULL;
static uint64_t *vis[2], *cur, *nxt;
static int d, D;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static uint64_t far_from(int start, const uint64_t *sa, const uint64_t *sj) {
    memset(vis[0], 0, 8 * W); memset(vis[1], 0, 8 * W); memset(cur, 0, 8 * W);
    cur[0] = 1; vis[start][0] = 1; int side = start;
    for (int lev = 1; lev <= D; lev++) {
        int to = 1 - side; memset(nxt, 0, 8 * W);
        #pragma omp parallel for schedule(dynamic, 4096)
        for (uint64_t wi = 0; wi < W; wi++) { uint64_t b = cur[wi];
            while (b) { uint64_t g = wi * 64 + __builtin_ctzll(b); b &= b - 1;
                uint64_t j = g / m, a = g - j * m;
                for (int x = 0; x < d; x++) { uint64_t na, nj;
                    if (side == 0) { na = (sa[x] + rp[sj[x]] * a) % m; nj = (sj[x] + j) % k; }
                    else { uint64_t ij = (k - sj[x]) % k; na = rp[ij] * ((a + m - sa[x]) % m) % m; nj = (j + k - sj[x]) % k; }
                    uint64_t h = nj * m + na; __atomic_fetch_or(&nxt[h >> 6], 1ULL << (h & 63), __ATOMIC_RELAXED);
                } } }
        for (uint64_t wi = 0; wi < W; wi++) { nxt[wi] &= ~vis[to][wi]; vis[to][wi] |= nxt[wi]; }
        uint64_t *t = cur; cur = nxt; nxt = t; side = to;
    }
    uint64_t seen = 0; for (uint64_t wi = 0; wi < W; wi++) seen += __builtin_popcountll(vis[0][wi]) + __builtin_popcountll(vis[1][wi]);
    return 2 * N - seen;
}
int main(int argc, char **argv) {
    m = strtoull(argv[1], 0, 10); k = strtoull(argv[2], 0, 10); uint64_t r = strtoull(argv[3], 0, 10);
    d = atoi(argv[4]); D = atoi(argv[5]); rs ^= strtoull(argv[6], 0, 10) * 0x2545F4914F6CDD1DULL; long iters = atol(argv[7]);
    N = m * k; W = (N + 63) / 64; rp = malloc(8 * (k + 1)); rp[0] = 1; for (uint64_t j = 1; j <= k; j++) rp[j] = rp[j - 1] * r % m;
    if (rp[k] != 1) { fprintf(stderr, "r^k != 1\n"); return 2; }
    vis[0] = calloc(W, 8); vis[1] = calloc(W, 8); cur = calloc(W, 8); nxt = calloc(W, 8);
    uint64_t sa[64] = {0}, sj[64] = {0};
    for (int x = 1; x < d; x++) { sa[x] = rnd() % m; sj[x] = rnd() % k; }
    uint64_t best = far_from(0, sa, sj) + far_from(1, sa, sj);
    fprintf(stderr, "start cost %lu\n", best);
    for (long it = 0; it < iters && best > 0; it++) {
        int x = 1 + rnd() % (d - 1); uint64_t oa = sa[x], oj = sj[x];
        sa[x] = rnd() % m; sj[x] = rnd() % k;
        int dup = 0; for (int y = 0; y < d; y++) if (y != x && sa[y] == sa[x] && sj[y] == sj[x]) dup = 1;
        uint64_t c = dup ? ~0ULL : far_from(0, sa, sj);
        if (c <= best) c += far_from(1, sa, sj);
        if (c <= best) { best = c; fprintf(stderr, "it %ld cost %lu\n", it, best); } else { sa[x] = oa; sj[x] = oj; }
    }
    printf("RESULT d=%d D=%d group=meta %lu %lu %lu best=%lu\n", d, D, m, k, r, best);
    if (best == 0) { FILE *f = fopen(argv[8], "w"); fprintf(f, "%d %d meta %lu %lu %lu n 1 N %lu\n", d, D, m, k, r, N);
        for (int x = 0; x < d; x++) fprintf(f, "%lu meta(a=%lu,j=%lu) z=0\n", sa[x] * k + sj[x], sa[x], sj[x]); fclose(f); }
    return 0;
}
