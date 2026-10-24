/* affcheck.c: diameter check for a "permutation lift" of a bipartite base multigraph whose edges carry AFFINE maps
   of Z_N (N <= 64): the edge (p, l, a, b) joins (p, x) to (l, a*x + b mod N); gcd(a, N) = 1.
   Not a regular cover, so sources are (p, x) pairs: every STEP-th point p with every x in XS (default all x).
   Checks that every (line, y) is within distance 7 of the source (opposite pairs; diameter <= 8 follows).
   Base file (text): "NP NL N aff", then edges "p l a b".
   Usage: affcheck BASE STEP [XSTEP]   (XSTEP: use x = 0, XSTEP, 2*XSTEP, ...; default 1) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int NP, NL, N, nmaps;
static int *pst, *pl_, *pmap, *lst, *lp_, *lmap; /* CSR, map index for p->l direction and l->p (inverse) */
static u64 *T; /* per map: 8*256 table */
static u64 FULL;
static int mapid[64][64];
static inline u64 app(u64 x, int mi) {
    const u64 *t = T + (size_t)mi * 2048; u64 r = 0;
    for (int b = 0; x; b++, x >>= 8) { unsigned v = x & 255; if (v) r |= t[b * 256 + v]; }
    return r;
}
static int getmap(int a, int b) {
    if (mapid[a][b] >= 0) return mapid[a][b];
    int id = nmaps++; mapid[a][b] = id;
    T = realloc(T, sizeof(u64) * 2048 * nmaps);
    u64 *t = T + (size_t)id * 2048;
    for (int byte = 0; byte < 8; byte++) for (int v = 0; v < 256; v++) {
        u64 r = 0;
        for (int bit = 0; bit < 8; bit++) if (v >> bit & 1) { int x = byte * 8 + bit; if (x < N) r |= 1ULL << ((a * x + b) % N); }
        t[byte * 256 + v] = r;
    }
    return id;
}
static int inv(int a) { for (int i = 1; i < N; i++) if (a * i % N == 1) return i; return -1; }
int main(int argc, char **argv) {
    int step = argc > 2 ? atoi(argv[2]) : 1, xstep = argc > 3 ? atoi(argv[3]) : 1;
    FILE *f = fopen(argv[1], "r"); char gs[16];
    if (fscanf(f, "%d %d %d %15s", &NP, &NL, &N, gs) != 4) return 1;
    FULL = N == 64 ? ~0ULL : (1ULL << N) - 1;
    memset(mapid, -1, sizeof mapid);
    int cap = 1 << 20, ne = 0; int *E = malloc(sizeof(int) * 4 * cap); int p, l, a, b;
    while (fscanf(f, "%d %d %d %d", &p, &l, &a, &b) == 4) { if (ne == cap) { cap *= 2; E = realloc(E, sizeof(int) * 4 * cap); } E[4*ne] = p; E[4*ne+1] = l; E[4*ne+2] = a; E[4*ne+3] = b; ne++; }
    fclose(f);
    pst = calloc(NP + 1, 4); lst = calloc(NL + 1, 4);
    for (int i = 0; i < ne; i++) { pst[E[4*i]+1]++; lst[E[4*i+1]+1]++; }
    for (int i = 0; i < NP; i++) pst[i+1] += pst[i];
    for (int i = 0; i < NL; i++) lst[i+1] += lst[i];
    pl_ = malloc(4 * ne); pmap = malloc(4 * ne); lp_ = malloc(4 * ne); lmap = malloc(4 * ne);
    int *pc = calloc(NP, 4), *lc = calloc(NL, 4);
    for (int i = 0; i < ne; i++) {
        int pp = E[4*i], ll = E[4*i+1], aa = E[4*i+2] % N, bb = E[4*i+3] % N;
        int ai = inv(aa); if (ai < 0) { fprintf(stderr, "non-unit multiplier\n"); return 1; }
        /* inverse map: y -> ai*(y - b) = ai*y - ai*b */
        int k = pst[pp] + pc[pp]++; pl_[k] = ll; pmap[k] = getmap(aa, bb);
        int k2 = lst[ll] + lc[ll]++; lp_[k2] = pp; lmap[k2] = getmap(ai, ((N - ai * bb % N) % N));
    }
    fprintf(stderr, "base %d+%d, %d edges, N=%d, %d distinct maps\n", NP, NL, ne, N, nmaps);
    long long total = 0; int nsrc = 0, bad = 0, worst = 0;
    #pragma omp parallel reduction(+:total,nsrc,bad)
    {
        u64 *rp = malloc(8 * NP), *rl = malloc(8 * NL), *fp = malloc(8 * NP), *fl = malloc(8 * NL);
        #pragma omp for schedule(dynamic, 4)
        for (int s = 0; s < NP; s += step) for (int x0 = 0; x0 < N; x0 += xstep) {
            memset(rp, 0, 8 * NP); memset(rl, 0, 8 * NL); memset(fp, 0, 8 * NP); memset(fl, 0, 8 * NL);
            rp[s] = fp[s] = 1ULL << x0;
            for (int t = 1; t <= 7; t++) {
                if (t & 1) {
                    /* push from points along forward maps */
                    memset(fl, 0, 8 * NL);
                    for (int x = 0; x < NP; x++) { u64 v = fp[x]; if (!v) continue;
                        for (int k = pst[x]; k < pst[x+1]; k++) fl[pl_[k]] |= app(v, pmap[k]); }
                    for (int y = 0; y < NL; y++) { fl[y] &= ~rl[y]; rl[y] |= fl[y]; }
                } else {
                    memset(fp, 0, 8 * NP);
                    for (int y = 0; y < NL; y++) { u64 v = fl[y]; if (!v) continue;
                        for (int k = lst[y]; k < lst[y+1]; k++) fp[lp_[k]] |= app(v, lmap[k]); }
                    for (int x = 0; x < NP; x++) { fp[x] &= ~rp[x]; rp[x] |= fp[x]; }
                }
            }
            long long u = 0; for (int y = 0; y < NL; y++) u += N - __builtin_popcountll(rl[y] & FULL);
            total += u; nsrc++; if (u) bad++;
            #pragma omp critical
            { if (u > worst) worst = (int)u; }
        }
        free(rp); free(rl); free(fp); free(fl);
    }
    printf("sources %d, bad %d, total uncovered %lld, worst %d, misses/source %.3f\n", nsrc, bad, total, worst, (double)total / nsrc);
    return 0;
}
