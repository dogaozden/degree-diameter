/* d16 family search: hubs on side A (neighbours in B) whose fibre lines lie in the 4 B-controller vertices adjacent to
 * one A-controller vertex (acv). Directions are fixed per tuple: one direction per B-cv, from the top TOPK by mean
 * line-ball size. A hub = one affine line per B-cv (64 offsets each), i.e. 64^4 candidates per tuple, tested by
 * meet-in-the-middle cover (every A-vertex within distance 3 of N). A hub may also take ONE extra old B-vertex t
 * (|N| = 17) when the residue U left by the 4 lines is inside ball3(t) (|U| <= UMAX).
 * Compatibility: disjoint N and some x in N(h), x' in N(h') with d(x,x') <= 2. Max clique: Tomita colouring
 * branch and bound with a time cap (NOTPROVEN if cut).
 * usage: famsearch EDGES ACV TOPK T0 T1 SECS OUTPREFIX UMAX */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define H 16896
#define W 264
#define NCV 66
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;             /* over B-vertices t: ball3 in A (bitset over A), d2 in B */
static inline int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int TOPK;
static int dirs[4][85];
static int lvv[4][85][64][4];           /* [cv slot][dir slot][coset][l] -> local B id */
static uint64_t *lb;                    /* [4][TOPK][64][W] line balls */
#define LB(k,j,o) (lb + ((((size_t)(k)*TOPK + (j))*64 + (o)) * W))

/* max clique (compat graph) */
static int K, KW; static uint64_t *cadj;
static int best_sz, *best_set, *cur, curn; static double deadline; static long nodes; static int aborted;
static void expand(uint64_t *P) {
    if (aborted) return;
    if ((++nodes & 255) == 0 && now() > deadline) { aborted = 1; return; }
    int n = 0; int *ord = malloc(sizeof(int) * K), *col = malloc(sizeof(int) * K);
    uint64_t *Q = malloc(8 * KW), *R = malloc(8 * KW);
    memcpy(Q, P, 8 * KW); int color = 0;
    for (;;) {
        int any = 0; for (int w = 0; w < KW; w++) if (Q[w]) { any = 1; break; }
        if (!any) break;
        color++; memcpy(R, Q, 8 * KW);
        for (;;) {
            int v = -1; for (int w = 0; w < KW; w++) if (R[w]) { v = w * 64 + __builtin_ctzll(R[w]); break; }
            if (v < 0) break;
            Q[v >> 6] &= ~(1ULL << (v & 63)); R[v >> 6] &= ~(1ULL << (v & 63));
            const uint64_t *a = cadj + (size_t)v * KW;
            for (int w = 0; w < KW; w++) R[w] &= ~a[w];
            ord[n] = v; col[n] = color; n++;
        }
    }
    free(Q); free(R);
    uint64_t *NP = malloc(8 * KW), *PP = malloc(8 * KW); memcpy(PP, P, 8 * KW);
    for (int i = n - 1; i >= 0; i--) {
        if (curn + col[i] <= best_sz) break;
        int v = ord[i]; cur[curn++] = v;
        const uint64_t *a = cadj + (size_t)v * KW; int empty = 1;
        for (int w = 0; w < KW; w++) { NP[w] = PP[w] & a[w]; if (NP[w]) empty = 0; }
        if (empty) { if (curn > best_sz) { best_sz = curn; memcpy(best_set, cur, sizeof(int) * curn); } }
        else expand(NP);
        curn--;
        PP[v >> 6] &= ~(1ULL << (v & 63));
        if (aborted) break;
    }
    free(NP); free(PP); free(ord); free(col);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: famsearch EDGES ACV TOPK T0 T1 SECS OUTPREFIX UMAX\n"); return 2; }
    int acv = atoi(argv[2]); TOPK = atoi(argv[3]); long T0 = atol(argv[4]), T1 = atol(argv[5]); double secs = atof(argv[6]);
    int UMAX = atoi(argv[8]);
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    static int da[H], db[H];
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    int ncnt[NCV] = {0}; for (int a = acv * 256; a < acv * 256 + 256; a++) for (int i = 0; i < 16; i++) ncnt[adjA[a][i] >> 8]++;
    int Ncv[4], nn = 0; for (int c = 0; c < NCV; c++) if (ncnt[c]) { if (nn < 4) Ncv[nn] = c; nn++; }
    fprintf(stderr, "A-cv %d: %d B-cv neighbours\n", acv, nn);
    if (nn != 4) return 4;
    double t0 = now();
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjB[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjA[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjB[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    int alld[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) alld[nd++] = c; }
    lb = malloc((size_t)4 * TOPK * 64 * W * 8);
    for (int k = 0; k < 4; k++) {
        double sc[85]; int idx[85]; int seen[256];
        for (int di = 0; di < nd; di++) { long tot = 0; int cnt = 0; idx[di] = di; memset(seen, 0, sizeof seen);
            for (int y = 0; y < 256; y++) if (!seen[y]) { uint64_t tmp[W]; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int z = y ^ scal(l, alld[di]); seen[z] = 1; int t = Ncv[k] * 256 + z; uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                for (int w = 0; w < W; w++) tot += __builtin_popcountll(tmp[w]); cnt++; }
            sc[di] = (double)tot / cnt; }
        for (int a = 0; a < nd; a++) for (int b = a + 1; b < nd; b++) if (sc[idx[b]] > sc[idx[a]]) { int t = idx[a]; idx[a] = idx[b]; idx[b] = t; }
        for (int j = 0; j < TOPK; j++) {
            int di = idx[j]; dirs[k][j] = alld[di];
            int o = 0; memset(seen, 0, sizeof seen);
            for (int y = 0; y < 256; y++) if (!seen[y]) {
                for (int l = 0; l < 4; l++) { int z = y ^ scal(l, alld[di]); seen[z] = 1; lvv[k][j][o][l] = Ncv[k] * 256 + z; }
                o++; }
            for (o = 0; o < 64; o++) {
                uint64_t *out = LB(k, j, o); memset(out, 0, 8 * W);
                for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lvv[k][j][o][l] * W; for (int w = 0; w < W; w++) out[w] |= bl[w]; }
            }
        }
        fprintf(stderr, "cv %d: best direction %d mean line ball %.0f\n", Ncv[k], dirs[k][0], sc[idx[0]]);
    }
    fprintf(stderr, "setup %.1fs\n", now() - t0);
    long NT = 1; for (int k = 0; k < 4; k++) NT *= TOPK;
    if (T1 > NT) T1 = NT;
    uint64_t *P12 = malloc((size_t)4096 * W * 8), *P34 = malloc((size_t)4096 * W * 8);
    int *hubo = malloc(sizeof(int) * 4 * 2000000), *hext = malloc(sizeof(int) * 2000000);
    for (long t = T0; t < T1; t++) {
        long tt = t; int jj[4]; for (int k = 0; k < 4; k++) { jj[k] = tt % TOPK; tt /= TOPK; }
        double ts = now();
        for (int p = 0; p < 4096; p++) { uint64_t *d = P12 + (size_t)p * W, *a = LB(0, jj[0], p >> 6), *b = LB(1, jj[1], p & 63);
            for (int w = 0; w < W; w++) d[w] = a[w] | b[w]; }
        for (int p = 0; p < 4096; p++) { uint64_t *d = P34 + (size_t)p * W, *a = LB(2, jj[2], p >> 6), *b = LB(3, jj[3], p & 63);
            for (int w = 0; w < W; w++) d[w] = a[w] | b[w]; }
        int nc = 0, cap = 2000000, mn = 1 << 30; long nres = 0;
        for (int p = 0; p < 4096; p++) { uint64_t *a = P12 + (size_t)p * W;
            for (int q = 0; q < 4096; q++) { uint64_t *b = P34 + (size_t)q * W; int c = 0;
                for (int w = 0; w < W; w++) c += __builtin_popcountll(~(a[w] | b[w]));
                if (c < mn) mn = c;
                if (c > UMAX) continue;
                int ext = -1;
                if (c > 0) { nres++;
                    uint64_t U[W]; for (int w = 0; w < W; w++) U[w] = ~(a[w] | b[w]);
                    int lv16[16]; for (int k = 0; k < 4; k++) for (int l = 0; l < 4; l++) lv16[4*k+l] = lvv[k][jj[k]][k==0?(p>>6):k==1?(p&63):k==2?(q>>6):(q&63)][l];
                    for (int tt2 = 0; tt2 < H && ext < 0; tt2++) { uint64_t *bl = ball + (size_t)tt2 * W; int w = 0;
                        for (; w < W; w++) if (U[w] & ~bl[w]) break;
                        if (w < W) continue;
                        int inN = 0; for (int l = 0; l < 16; l++) if (lv16[l] == tt2) inN = 1;
                        if (!inN) ext = tt2; }
                    if (ext < 0) continue;
                }
                if (nc < cap) { hubo[4*nc] = p >> 6; hubo[4*nc+1] = p & 63; hubo[4*nc+2] = q >> 6; hubo[4*nc+3] = q & 63; hext[nc] = ext; }
                nc++;
            } }
        double tc = now() - ts;
        int ncov = 0, next_ = 0; for (int i = 0; i < nc && i < cap; i++) { if (hext[i] < 0) ncov++; else next_++; }
        if (nc == 0 || nc > 20000) {
            printf("tuple %ld dirs %d %d %d %d min_uncovered %d cover4 %d cover_with_extra %d (enum %.1fs) clique skipped\n", t,
                   dirs[0][jj[0]], dirs[1][jj[1]], dirs[2][jj[2]], dirs[3][jj[3]], mn, ncov, next_, tc);
            fflush(stdout); continue; }
        int (*N)[17] = malloc(sizeof(int[17]) * nc); int *nN = malloc(sizeof(int) * nc);
        for (int i = 0; i < nc; i++) { int o[4] = {hubo[4*i], hubo[4*i+1], hubo[4*i+2], hubo[4*i+3]}; int m = 0;
            for (int k = 0; k < 4; k++) for (int l = 0; l < 4; l++) N[i][m++] = lvv[k][jj[k]][o[k]][l];
            if (hext[i] >= 0) N[i][m++] = hext[i];
            nN[i] = m; }
        K = nc; KW = (nc + 63) / 64;
        uint64_t *R = malloc((size_t)nc * W * 8);
        for (int i = 0; i < nc; i++) { uint64_t *o = R + (size_t)i * W; memset(o, 0, W * 8);
            for (int k = 0; k < nN[i]; k++) { uint64_t *dd = d2 + (size_t)N[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
        cadj = calloc((size_t)nc * KW, 8);
        int *stamp = calloc(H, 4); long ne = 0;
        for (int i = 0; i < nc; i++) {
            for (int l = 0; l < nN[i]; l++) stamp[N[i][l]] = i + 1;
            uint64_t *o = R + (size_t)i * W;
            for (int j = i + 1; j < nc; j++) { int meet = 0, dis = 1;
                for (int k = 0; k < nN[j]; k++) { int x = N[j][k]; if (stamp[x] == i + 1) { dis = 0; break; } if ((o[x >> 6] >> (x & 63)) & 1) meet = 1; }
                if (meet && dis) { cadj[(size_t)i * KW + (j >> 6)] |= 1ULL << (j & 63); cadj[(size_t)j * KW + (i >> 6)] |= 1ULL << (i & 63); ne++; } }
        }
        double dens = nc > 1 ? 2.0 * ne / ((double)nc * (nc - 1)) : 0;
        best_sz = 0; best_set = malloc(sizeof(int) * (nc + 1)); cur = malloc(sizeof(int) * (nc + 1)); curn = 0; nodes = 0; aborted = 0;
        deadline = now() + secs;
        uint64_t *P = calloc(KW, 8); for (int i = 0; i < nc; i++) P[i >> 6] |= 1ULL << (i & 63);
        expand(P);
        printf("tuple %ld dirs %d %d %d %d min_uncovered %d cover4 %d cover_with_extra %d density %.4f clique %d %s nodes %ld (%.1fs)\n", t,
               dirs[0][jj[0]], dirs[1][jj[1]], dirs[2][jj[2]], dirs[3][jj[3]], mn, ncov, next_, dens, best_sz, aborted ? "NOTPROVEN" : "exact", nodes, now() - ts);
        fflush(stdout);
        if (best_sz > 0) { char fn[512]; snprintf(fn, sizeof fn, "%s_t%ld.hubs", argv[7], t); FILE *g = fopen(fn, "w");
            for (int a = 0; a < best_sz; a++) { int i = best_set[a]; for (int l = 0; l < nN[i]; l++) fprintf(g, "%d ", N[i][l] + H); fprintf(g, "\n"); }
            fclose(g); }
        free(N); free(nN); free(R); free(cadj); free(stamp); free(best_set); free(cur); free(P);
    }
    return 0;
}
