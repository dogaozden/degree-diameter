/* d12: lift of a 7-regular bipartite controller H on m+m vertices, edge colours 0..6.
   Colours 0..3 are CHART letters (lift edges (a,x)~(b, A_c x + lam B_c), lam in F4: 4 neighbours each),
   colours 4..6 are PLAIN letters ((a,x)~(b, A_p x + c_p): 1 neighbour each). Degree 4*4+3 = 19.
   Each colour is a perfect matching of H (sig[l] : A -> B), all pairs distinct.  Fibre F4^4 (256 points,
   vector id = sum digit_c << 2c, F4 = {0,1,w,w^2} coded 0..3, addition = XOR).
   Lift vertices: A-vertex (a,x) -> a*256+x, B-vertex (b,y) -> m*256 + b*256 + y.  n = 512 m.
   Cost = number of uncovered (source (u,x), target w, pairs with dist > 5) over sampled sources u, computed by
   bit-parallel BFS of depth 5 (sources = the 256 fibre points of u, one bit each).  0 means diameter <= 5 on them.
   usage: mix7 m iters seed out.edges [K]     (K sampled controller sources, default 6; full check at the end)
   Output edge file has first line n, then "u v" per line (apsp.c format). Deterministic for fixed args. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
static uint64_t rs;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
#define NL 7
#define NF 256
int m; long n;
int sig[NL][512], isig[NL][512];
unsigned char used[512][512];           /* bitmask of colours using pair (a,b) */
int A[NL][4][4];                      /* matrices over F4 */
int f[NL][NF], finv[NL][NF];          /* forward / inverse maps on fibre */
int sv[NL][4];                        /* chart: lam * B_c (vector ids) */
int cp[NL];                           /* plain: translation vector id */
int *adj; int DEG = 19;
uint64_t *vis, *fr, *nx;
int chk_ok;

static int matvec(int l, int x) {
    int y = 0;
    for (int r = 0; r < 4; r++) { int s = 0;
        for (int c = 0; c < 4; c++) s ^= MUL[A[l][r][c]][(x >> (2 * c)) & 3];
        y |= s << (2 * r); }
    return y;
}
/* random invertible matrix for letter l; returns 0 on failure */
static void build_maps(int l) {
    for (int x = 0; x < NF; x++) f[l][x] = matvec(l, x);
    for (int x = 0; x < NF; x++) finv[l][f[l][x]] = x;
}
static void rand_letter(int l) {
    for (;;) {
        for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) A[l][r][c] = xr() & 3;
        unsigned char seen[NF] = {0}; int ok = 1;
        for (int x = 0; x < NF && ok; x++) { int y = matvec(l, x); if (seen[y]) ok = 0; seen[y] = 1; }
        if (ok) break;
    }
    build_maps(l);
    if (l < 4) { int B = 0; while (B == 0) B = xr() & 255;
        for (int lam = 0; lam < 4; lam++) { int v = 0; for (int c = 0; c < 4; c++) v |= MUL[lam][(B >> (2 * c)) & 3] << (2 * c);
            sv[l][lam] = v; }
    } else cp[l] = xr() & 255;
}
static void build_adj(void) {
    for (int a = 0; a < m; a++) for (int x = 0; x < NF; x++) {
        int *p = adj + ((long)a * NF + x) * DEG; int k = 0;
        for (int l = 0; l < NL; l++) { int b = sig[l][a];
            if (l < 4) for (int lam = 0; lam < 4; lam++) p[k++] = (long)m * NF + b * NF + (f[l][x] ^ sv[l][lam]);
            else p[k++] = (long)m * NF + b * NF + (f[l][x] ^ cp[l]); }
    }
    for (int b = 0; b < m; b++) for (int y = 0; y < NF; y++) {
        int *p = adj + ((long)m * NF + b * NF + y) * DEG; int k = 0;
        for (int l = 0; l < NL; l++) { int a = isig[l][b];
            if (l < 4) for (int lam = 0; lam < 4; lam++) p[k++] = (long)a * NF + finv[l][y ^ sv[l][lam]];
            else p[k++] = (long)a * NF + finv[l][y ^ cp[l]]; }
    }
}
static int popc(uint64_t v) { return __builtin_popcountll(v); }
/* uncovered (source, target) pairs for controller vertex src (side 0 = A, 1 = B), depth 5 */
static long uncovered(int side, int u) {
    long base = (side == 0 ? 0 : (long)m * NF) + (long)u * NF;
    memset(vis, 0, n * 32); memset(fr, 0, n * 32);
    for (int x = 0; x < NF; x++) { long v = base + x; vis[v * 4 + (x >> 6)] |= 1ULL << (x & 63); fr[v * 4 + (x >> 6)] |= 1ULL << (x & 63); }
    for (int d = 1; d <= 5; d++) {
        for (long w = 0; w < n; w++) {
            uint64_t a0 = 0, a1 = 0, a2 = 0, a3 = 0; int *p = adj + w * DEG;
            for (int k = 0; k < DEG; k++) { long z = p[k] * 4; a0 |= fr[z]; a1 |= fr[z + 1]; a2 |= fr[z + 2]; a3 |= fr[z + 3]; }
            nx[w * 4] = a0 & ~vis[w * 4]; nx[w * 4 + 1] = a1 & ~vis[w * 4 + 1];
            nx[w * 4 + 2] = a2 & ~vis[w * 4 + 2]; nx[w * 4 + 3] = a3 & ~vis[w * 4 + 3];
        }
        for (long i = 0; i < 4 * n; i++) { vis[i] |= nx[i]; }
        uint64_t *t = fr; fr = nx; nx = t;
    }
    long c = 0;
    for (long w = 0; w < n; w++) c += 256 - popc(vis[w * 4]) - popc(vis[w * 4 + 1]) - popc(vis[w * 4 + 2]) - popc(vis[w * 4 + 3]);
    return c;
}
static long cost_sample(int K, int *SS, int *SU) {
    build_adj(); long c = 0;
    for (int i = 0; i < K; i++) c += uncovered(SS[i], SU[i]);
    return c;
}
static void write_edges(const char *path) {
    FILE *g = fopen(path, "w"); fprintf(g, "%ld\n", n);
    for (int a = 0; a < m; a++) for (int x = 0; x < NF; x++) for (int l = 0; l < NL; l++) {
        int b = sig[l][a];
        if (l < 4) for (int lam = 0; lam < 4; lam++) fprintf(g, "%ld %ld\n", (long)a * NF + x, (long)m * NF + b * NF + (f[l][x] ^ sv[l][lam]));
        else fprintf(g, "%ld %ld\n", (long)a * NF + x, (long)m * NF + b * NF + (f[l][x] ^ cp[l]));
    }
    fclose(g);
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: mix7 m iters seed out.edges [K]\n"); return 1; }
    m = atoi(argv[1]); long iters = atol(argv[2]); rs = strtoull(argv[3], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *out = argv[4]; int K = argc > 5 ? atoi(argv[5]) : 6;
    n = 2L * m * NF;
    adj = malloc(n * DEG * sizeof(int)); vis = calloc(n * 4, 8); fr = calloc(n * 4, 8); nx = calloc(n * 4, 8);
    memset(used, 0, sizeof used);
    for (int l = 0; l < NL; l++) {
        for (;;) { int p[512]; for (int i = 0; i < m; i++) p[i] = i;
            for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
            int ok = 1; for (int a = 0; a < m && ok; a++) if (used[a][p[a]] & 0xFF) ok = 0;
            if (!ok) continue;
            for (int a = 0; a < m; a++) { sig[l][a] = p[a]; isig[l][p[a]] = a; used[a][p[a]] |= 1 << l; }
            break; }
        rand_letter(l);
    }

    if (iters == 0) { /* diagnostic: uncovered targets from source (A,u=0,x=0) by controller vertex */
        build_adj(); memset(vis,0,n*32); memset(fr,0,n*32);
        vis[0] |= 1; fr[0] |= 1;
        for (int d = 1; d <= 5; d++) { for (long w = 0; w < n; w++) { uint64_t a[4]={0,0,0,0}; int *p = adj + w*DEG;
                for (int k=0;k<DEG;k++){ long z=(long)p[k]*4; for(int j=0;j<4;j++) a[j]|=fr[z+j]; }
                for (int j=0;j<4;j++){ nx[w*4+j]=a[j]&~vis[w*4+j]; } }
            for (long i=0;i<4*n;i++) vis[i]|=nx[i]; uint64_t*t=fr; fr=nx; nx=t; }
        static int hist[512]; long tot=0;
        for (long w=0; w<n; w++) { int miss = (vis[w*4] & 1) ? 0 : 1;
            if (miss) { tot+=miss; int cv = w < (long)m*NF ? w/NF : (int)((w-(long)m*NF)/NF); hist[cv] += miss; } }
        printf("diag: uncovered from (A0,x=0) total %ld\n", tot);
        for (int c=0;c<2*m;c++) if (hist[c]) printf("  %s%d: %d\n", c<m?"A":"B", c<m?c:c-m, hist[c]);
        return 0;
    }
    int SS[16], SU[16];
    for (int i = 0; i < K; i++) { SS[i] = i & 1; SU[i] = xr() % m; }   /* alternate A and B sources */
    long cur = cost_sample(K, SS, SU), best = cur;
    fprintf(stderr, "m=%d n=%ld K=%d initial cost %ld\n", m, n, K, cur);
    double T0 = 40.0, T1 = 0.5;
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        if (xr() % 100 < 3) {   /* re-draw one letter (matrix / vector) */
            int l = xr() % NL; int sA[4][4]; memcpy(sA, A[l], sizeof sA); int ssv[4], scp = cp[l];
            memcpy(ssv, sv[l], sizeof ssv); int sf[NF], sfi[NF];
            memcpy(sf, f[l], sizeof sf); memcpy(sfi, finv[l], sizeof sfi);
            rand_letter(l);
            long nc = cost_sample(K, SS, SU);
            if (nc <= cur || ur() < exp(-(nc - cur) / T)) { cur = nc; }
            else { memcpy(A[l], sA, sizeof sA); memcpy(sv[l], ssv, sizeof ssv); cp[l] = scp;
                memcpy(f[l], sf, sizeof sf); memcpy(finv[l], sfi, sizeof sfi); }
        } else {
            int l = xr() % NL; int a1 = xr() % m, a2 = xr() % m; if (a1 == a2) continue;
            int b1 = sig[l][a1], b2 = sig[l][a2];
            if (used[a1][b2] || used[a2][b1]) continue;
            used[a1][b1] &= ~(1 << l); used[a2][b2] &= ~(1 << l);
            used[a1][b2] |= 1 << l; used[a2][b1] |= 1 << l;
            sig[l][a1] = b2; sig[l][a2] = b1; isig[l][b2] = a1; isig[l][b1] = a2;
            long nc = cost_sample(K, SS, SU);
            if (nc <= cur || ur() < exp(-(nc - cur) / T)) cur = nc;
            else {
                used[a1][b2] &= ~(1 << l); used[a2][b1] &= ~(1 << l);
                used[a1][b1] |= 1 << l; used[a2][b2] |= 1 << l;
                sig[l][a1] = b1; sig[l][a2] = b2; isig[l][b1] = a1; isig[l][b2] = a2;
            }
        }
        if (cur < best) { best = cur; fprintf(stderr, "it %ld T %.3f best %ld\n", it, T, best); }
    }
    fprintf(stderr, "sampled cost %ld after search\n", cur);
    /* full check: every controller vertex on both sides as a source */
    long full = 0;
    build_adj();
    for (int a = 0; a < m; a++) full += uncovered(0, a);
    for (int b = 0; b < m; b++) full += uncovered(1, b);
    printf("m %d n %ld full_uncovered %ld\n", m, n, full);
    if (full == 0) { write_edges(out); printf("WROTE %s\n", out); }
    return 0;
}
