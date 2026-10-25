/* classcheck.c: scan structured voltage families. Base file: "NP NL K" then edges "p l cls" (cls 0..K-1).
   Group A = Z_a x Z_b (m = a*b <= 64; element (u,v) has index u*b+v). Parameter file: one family member per line,
   2K integers "u_0 v_0 u_1 v_1 ..." giving the voltage (u_c, v_c) of class c (read point -> line).
   For each member: BFS from point sources 0, STEP, 2*STEP, ... to depth MAXLEN (7) in the lift; prints
   "idx uncovered sources" (stops a member early once uncovered > CAP). Lift diameter <= 8 iff 0 over all sources.
   usage: classcheck BASE a b PARAMS [STEP=1] [CAP=1e18] [MAXLEN=7]   build: gcc -O3 -march=native -fopenmp */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int NP, NL, K, A_, B_, m;
static u64 *T;
static inline u64 act(u64 x, int g) {
    if (g == 0) return x;
    const u64 *t = T + (size_t)g * 8 * 256; u64 r = 0;
    for (int b = 0; b < 8 && x; b++, x >>= 8) { unsigned v = x & 255; if (v) r |= t[b * 256 + v]; }
    return r;
}
static inline int mul(int x, int y) { int u = (x / B_ + y / B_) % A_, v = (x % B_ + y % B_) % B_; return u * B_ + v; }
static inline int inv(int x) { int u = (A_ - x / B_) % A_, v = (B_ - x % B_) % B_; return u * B_ + v; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
    A_ = atoi(argv[2]); B_ = atoi(argv[3]); m = A_ * B_;
    int step = argc > 5 ? atoi(argv[5]) : 1; long long cap = argc > 6 ? atoll(argv[6]) : (long long)1e18;
    int maxlen = argc > 7 ? atoi(argv[7]) : 7;
    if (m > 64) { fprintf(stderr, "m > 64\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &NP, &NL, &K) != 3) return 1;
    int cap2 = 1 << 20, ne = 0; int *E = malloc(sizeof(int) * 3 * cap2); int p, l, c;
    while (fscanf(f, "%d %d %d", &p, &l, &c) == 3) { if (ne == cap2) { cap2 *= 2; E = realloc(E, sizeof(int) * 3 * cap2); } E[3*ne] = p; E[3*ne+1] = l; E[3*ne+2] = c; ne++; }
    fclose(f);
    int *pstart = calloc(NP + 1, sizeof(int)), *lstart = calloc(NL + 1, sizeof(int));
    for (int i = 0; i < ne; i++) { pstart[E[3*i] + 1]++; lstart[E[3*i+1] + 1]++; }
    for (int i = 0; i < NP; i++) pstart[i + 1] += pstart[i];
    for (int i = 0; i < NL; i++) lstart[i + 1] += lstart[i];
    int *padj = malloc(sizeof(int) * ne), *pcl = malloc(sizeof(int) * ne), *ladj = malloc(sizeof(int) * ne), *lcl = malloc(sizeof(int) * ne);
    int *pc = calloc(NP, sizeof(int)), *lc = calloc(NL, sizeof(int));
    for (int i = 0; i < ne; i++) {
        int a = E[3*i], b = E[3*i+1], cl = E[3*i+2];
        int k = pstart[a] + pc[a]++; padj[k] = b; pcl[k] = cl;
        int k2 = lstart[b] + lc[b]++; ladj[k2] = a; lcl[k2] = cl;
    }
    T = calloc((size_t)m * 8 * 256, sizeof(u64));
    for (int g = 0; g < m; g++) for (int b = 0; b < 8; b++) for (int v = 0; v < 256; v++) {
        u64 r = 0; for (int bit = 0; bit < 8; bit++) if (v >> bit & 1) { int x = b * 8 + bit; if (x < m) r |= 1ULL << mul(x, g); }
        T[((size_t)g * 8 + b) * 256 + v] = r;
    }
    FILE *pf = fopen(argv[4], "r"); int *vol = malloc(sizeof(int) * K);
    int *gp = malloc(sizeof(int) * ne), *gl = malloc(sizeof(int) * ne);
    for (int idx = 0;; idx++) {
        int ok = 1;
        for (int c2 = 0; c2 < K; c2++) { int u, v; if (fscanf(pf, "%d %d", &u, &v) != 2) { ok = 0; break; } vol[c2] = (((u % A_) + A_) % A_) * B_ + (((v % B_) + B_) % B_); }
        if (!ok) break;
        for (int k = 0; k < ne; k++) { gp[k] = vol[pcl[k]]; gl[k] = inv(vol[lcl[k]]); }
        long long total = 0; int nsrc = 0; volatile int stop = 0;
        #pragma omp parallel
        {
            u64 *rp = malloc(8 * NP), *rl = malloc(8 * NL), *fp = malloc(8 * NP), *fl = malloc(8 * NL);
            #pragma omp for schedule(dynamic, 4) reduction(+:total,nsrc)
            for (int s = 0; s < NP; s += step) {
                if (stop) continue;
                memset(rp, 0, 8 * NP); memset(rl, 0, 8 * NL); memset(fp, 0, 8 * NP); memset(fl, 0, 8 * NL);
                rp[s] = fp[s] = 1;
                for (int t = 1; t <= maxlen; t++) {
                    if (t & 1) {
                        for (int y = 0; y < NL; y++) { u64 acc = 0;
                            for (int k = lstart[y]; k < lstart[y + 1]; k++) { u64 x = fp[ladj[k]]; if (x) acc |= act(x, inv(gl[k])); }
                            acc &= ~rl[y]; fl[y] = acc; rl[y] |= acc; }
                    } else {
                        for (int x0 = 0; x0 < NP; x0++) { u64 acc = 0;
                            for (int k = pstart[x0]; k < pstart[x0 + 1]; k++) { u64 x = fl[padj[k]]; if (x) acc |= act(x, inv(gp[k])); }
                            acc &= ~rp[x0]; fp[x0] = acc; rp[x0] |= acc; }
                    }
                }
                long long unc = 0; for (int y = 0; y < NL; y++) unc += m - __builtin_popcountll(rl[y]);
                total += unc; nsrc++;
                if (total > cap) stop = 1;
            }
            free(rp); free(rl); free(fp); free(fl);
        }
        printf("%d %lld %d\n", idx, total, nsrc); fflush(stdout);
    }
    return 0;
}
