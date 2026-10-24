/* kcopy3.c: kcopy_hub.c with THREE cross bijections (card c6, squad c157-r2, cell (15,7), 2026-10-24).

   Cross edges of the 7-copy graph: (p,c) ~ (phi_j(p), c+j) for non-freed p, j = 1,2,3 (kcopy_hub.c has phi_j = M for all j).
   Here phi_1 = M (the bijection of the solution file), phi_j = M o sigma_j for j = 2,3, where sigma_j is a random
   permutation of the set R of non-freed points that are not protected. Freed points are never in R, so sigma_j fixes
   every freed point: phi_j(p_a) = M(p_a) = l_a for all j, and the hub structure of kcopy_hub.c is unchanged
   (3 point-side hubs on the copies of p_a, 3 line-side hubs on the copies of l_a, hub graph as in the file).

   Protection MODE (what sigma_j must leave alone so that the freed-source routes of the equal graph survive):
     0: nothing protected (sigma_j random on all non-freed points)
     1: points at incidence distance <= 4 from a freed point (side-A routes and hub-2-cross routes use these cross edges)
     2: MODE 1, plus the M-preimages of lines at distance <= 3 from a freed point, plus the points at distance <= 3
        from the freed line l_a (their cross edges carry the short routes of the line source).

   Usage: kcopy3 HEXBIN SOL 3 MODE SEED
   For every freed source s = (p_a,0) and (l_a,0) (copy shift invariance and the argument of kcopy_hub.c still reduce
   validity to these sources and the hubs), it computes the far set F_eq(s) (distance > 7 or unreached) in the equal
   graph (phi_j = M) and F_3(s) in the three-bijection graph. Printed: |F_eq|, |F_3|, the far targets covered only by
   the new routes (F_eq minus F_3), the new far targets (F_3 minus F_eq), per type and copy, and the fraction covered. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1, k, r, K, NV, HB;
static int32_t *LP, *PL;
static int *M, *Minv, *F, *isF;
static int HGm = 0, *HGj, *HGk;
static int **HGL, **HGP, *HGLn, *HGPn;
static int *PHI[4], *PHIinv[4];          /* cross bijections in use: PHI[j][p], PHIinv[j][l], j = 1..3 */
static int *sig[4], *sigi[4];           /* sigma_j and its inverse (identity for j = 1) */
static uint8_t *dist; static int *que;
static uint8_t *hd; static int *hq;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + cnt[p]++] = l; }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "bad hexagon table\n"); exit(1); }
    free(cnt);
}

static void read_sol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int qq, nn, kk, nv; char w[16];
    if (fscanf(f, "d7hex %d %d %d %d %15s", &qq, &nn, &kk, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol header\n"); exit(1); }
    K = kk; F = malloc(sizeof(int) * (K + 1)); isF = calloc(N, sizeof(int));
    for (int a = 0; a < K; a++) { if (fscanf(f, "%d", &F[a]) != 1) exit(1); if (isF[F[a]]) { fprintf(stderr, "repeated freed point\n"); exit(1); } isF[F[a]] = a + 1; }
    long pos = ftell(f); char tok[32];
    if (fscanf(f, "%31s", tok) == 1 && !strcmp(tok, "hubedges")) {
        if (fscanf(f, "%d", &HGm) != 1) exit(1);
        HGj = malloc(sizeof(int) * (HGm + 1)); HGk = malloc(sizeof(int) * (HGm + 1));
        for (int e = 0; e < HGm; e++) if (fscanf(f, "%d %d", &HGj[e], &HGk[e]) != 2) exit(1);
    } else fseek(f, pos, SEEK_SET);
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N); for (int l = 0; l < N; l++) Minv[l] = -1;
    for (int p = 0; p < N; p++) {
        if (fscanf(f, "%d", &M[p]) != 1 || M[p] < 0 || M[p] >= N) { fprintf(stderr, "bad M\n"); exit(1); }
        if (Minv[M[p]] >= 0) { fprintf(stderr, "M not a bijection\n"); exit(1); }
        Minv[M[p]] = p;
    }
    fclose(f);
    HGL = malloc(sizeof(int *) * (K + 1)); HGP = malloc(sizeof(int *) * (K + 1));
    HGLn = calloc(K + 1, sizeof(int)); HGPn = calloc(K + 1, sizeof(int));
    for (int a = 0; a < K; a++) { HGL[a] = malloc(sizeof(int) * 64); HGP[a] = malloc(sizeof(int) * 64); }
    for (int e = 0; e < HGm; e++) {
        int j = HGj[e], b = HGk[e];
        if (j < 0 || j >= K || b < 0 || b >= K) { fprintf(stderr, "hub edge out of range\n"); exit(1); }
        if (HGLn[j] >= 64 || HGPn[b] >= 64) { fprintf(stderr, "hub degree too large\n"); exit(1); }
        HGL[j][HGLn[j]++] = b; HGP[b][HGPn[b]++] = j;
    }
    r = 2 * k + 1; HB = r * 2 * N; NV = HB + 2 * k * K;
}

/* incidence BFS from a point (isline 0) or a line (isline 1), marks every node within distance D (points 0..N-1, lines N..2N-1) */
static void hball(int start, int isline, int D, uint8_t *mark) {
    memset(hd, 255, 2 * N); int h = 0, t = 0; int s = isline ? N + start : start; hd[s] = 0; hq[t++] = s;
    while (h < t) {
        int v = hq[h++]; if (hd[v] >= D) continue;
        if (v < N) { for (int i = 0; i < Q1; i++) { int w = N + PL[v * Q1 + i]; if (hd[w] == 255) { hd[w] = hd[v] + 1; hq[t++] = w; } } }
        else { int l = v - N; for (int i = 0; i < Q1; i++) { int w = LP[l * Q1 + i]; if (hd[w] == 255) { hd[w] = hd[v] + 1; hq[t++] = w; } } }
    }
    for (int v = 0; v < 2 * N; v++) if (hd[v] != 255) mark[v] = 1;
}

/* vertex ids: point (p,c) = c*2N + p; line (l,c) = c*2N + N + l; hub z_{a,j} = HB + a*k + (j-1); w_{a,j} = HB + k*K + a*k + (j-1) */
static inline int VP(int p, int c) { return c * 2 * N + p; }
static inline int VL(int l, int c) { return c * 2 * N + N + l; }
static int nbrs(int v, int *out) {
    int n = 0;
    if (v >= HB) {
        int h = v - HB;
        if (h < k * K) {                       /* point-side hub z_{a,j} (attached to the copies of p_a) */
            int a = h / k, j = h % k + 1, p = F[a];
            for (int c = 0; c < r; c++) out[n++] = VP(p, c);
            if (j == 1) for (int t = 0; t < HGLn[a]; t++) out[n++] = HB + k * K + HGL[a][t] * k;
        } else {                               /* line-side hub w_{a,j} (attached to the copies of l_a = M(p_a)) */
            h -= k * K; int a = h / k, j = h % k + 1, l = M[F[a]];
            for (int c = 0; c < r; c++) out[n++] = VL(l, c);
            if (j == 1) for (int t = 0; t < HGPn[a]; t++) out[n++] = HB + HGP[a][t] * k;
        }
        return n;
    }
    int c = v / (2 * N), x = v % (2 * N);
    if (x < N) {
        int p = x;
        for (int t = 0; t < Q1; t++) out[n++] = VL(PL[p * Q1 + t], c);
        if (isF[p]) { int a = isF[p] - 1; for (int j = 1; j <= k; j++) out[n++] = HB + a * k + (j - 1); }
        else for (int j = 1; j <= k; j++) out[n++] = VL(PHI[j][p], (c + j) % r);
    } else {
        int l = x - N;
        for (int t = 0; t < Q1; t++) out[n++] = VP(LP[l * Q1 + t], c);
        for (int j = 1; j <= k; j++) {
            int p = PHIinv[j][l];
            if (isF[p]) { int a = isF[p] - 1; out[n++] = HB + k * K + a * k + (j - 1); }
            else out[n++] = VP(p, (c - j + r) % r);
        }
    }
    return n;
}

static void set_eq(void) {
    for (int j = 1; j <= k; j++) {
        if (!PHI[j]) { PHI[j] = malloc(sizeof(int) * N); PHIinv[j] = malloc(sizeof(int) * N); }
        for (int p = 0; p < N; p++) PHI[j][p] = M[p];
        for (int l = 0; l < N; l++) PHIinv[j][l] = Minv[l];
    }
}

static void set_diff(void) {
    for (int j = 1; j <= k; j++) {
        if (!PHI[j]) { PHI[j] = malloc(sizeof(int) * N); PHIinv[j] = malloc(sizeof(int) * N); }
        for (int p = 0; p < N; p++) PHI[j][p] = M[sig[j][p]];
        for (int l = 0; l < N; l++) PHIinv[j][l] = sigi[j][Minv[l]];
    }
}

static void build_sigma(int mode) {
    uint8_t *prot = calloc(N, 1), *mk = calloc(2 * N, 1);
    for (int a = 0; a < K; a++) {
        int p = F[a], l = M[p];
        prot[p] = 1;
        if (mode >= 1) { memset(mk, 0, 2 * N); hball(p, 0, 4, mk); for (int x = 0; x < N; x++) if (mk[x]) prot[x] = 1; }
        if (mode >= 2) {
            memset(mk, 0, 2 * N); hball(p, 0, 3, mk);
            for (int x = N; x < 2 * N; x++) if (mk[x]) prot[Minv[x - N]] = 1;
            memset(mk, 0, 2 * N); hball(l, 1, 3, mk);
            for (int x = 0; x < N; x++) if (mk[x]) prot[x] = 1;
        }
        if (mode >= 3) {                       /* side B of the line source: preimages of the lines within 4 of l_a */
            memset(mk, 0, 2 * N); hball(l, 1, 4, mk);
            for (int x = N; x < 2 * N; x++) if (mk[x]) prot[Minv[x - N]] = 1;
        }
    }
    int *Rl = malloc(sizeof(int) * N), nR = 0;
    for (int p = 0; p < N; p++) if (!prot[p]) Rl[nR++] = p;
    printf("protected points %d, free points (sigma moves them) %d\n", N - nR, nR); fflush(stdout);
    for (int j = 1; j <= k; j++) {
        sig[j] = malloc(sizeof(int) * N); sigi[j] = malloc(sizeof(int) * N);
        for (int p = 0; p < N; p++) sig[j][p] = p;
        if (j > 1) {                           /* random permutation of R, applied to R only */
            int *perm = malloc(sizeof(int) * (nR + 1));
            for (int i = 0; i < nR; i++) perm[i] = Rl[i];
            for (int i = nR - 1; i > 0; i--) { int t = rndi(i + 1), tmp = perm[i]; perm[i] = perm[t]; perm[t] = tmp; }
            for (int i = 0; i < nR; i++) sig[j][Rl[i]] = perm[i];
            free(perm);
        }
        for (int p = 0; p < N; p++) sigi[j][sig[j][p]] = p;
    }
    for (int a = 0; a < K; a++) for (int j = 1; j <= k; j++) if (sig[j][F[a]] != F[a]) { fprintf(stderr, "sigma moves a freed point\n"); exit(1); }
    free(prot); free(mk); free(Rl);
}

static void basic_stats(int *maxdeg, long *nedges, long *asym) {
    int nb[128], md = 0; long m = 0; *asym = 0;
    for (int v = 0; v < NV; v++) {
        int c = nbrs(v, nb); if (c > md) md = c; m += c;
        for (int i = 0; i < c; i++) {
            int w = nb[i], nb2[128], c2 = nbrs(w, nb2), f = 0;
            for (int t = 0; t < c2; t++) if (nb2[t] == v) f++;
            if (f != 1) (*asym)++;
        }
    }
    *maxdeg = md; *nedges = m / 2;
}

/* BFS from s; marks far targets (distance > 7 or unreached) in bits (may be NULL); returns their number */
static long bfs_far(int s, uint8_t *bits) {
    memset(dist, 255, NV);
    int h = 0, t = 0, nb[128]; dist[s] = 0; que[t++] = s;
    while (h < t) {
        int v = que[h++]; int d = dist[v];
        int c = nbrs(v, nb);
        for (int i = 0; i < c; i++) { int w = nb[i]; if (dist[w] == 255) { dist[w] = d + 1; que[t++] = w; } }
    }
    long far = 0;
    for (int v = 0; v < NV; v++) if (dist[v] == 255 || dist[v] > 7) { far++; if (bits) bits[v >> 3] |= (uint8_t)(1u << (v & 7)); }
    return far;
}

static inline int bitof(const uint8_t *b, int v) { return (b[v >> 3] >> (v & 7)) & 1; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: kcopy3 HEXBIN SOL 3 MODE SEED\n"); return 1; }
    load(argv[1]); k = atoi(argv[3]); read_sol(argv[2]);
    int mode = atoi(argv[4]); uint64_t seed = strtoull(argv[5], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    dist = malloc(NV); que = malloc(sizeof(int) * NV);
    hd = malloc(2 * N); hq = malloc(sizeof(int) * 2 * N);
    int nsrc = 2 * K; int *srcv = malloc(sizeof(int) * nsrc);
    for (int a = 0; a < K; a++) { srcv[2 * a] = VP(F[a], 0); srcv[2 * a + 1] = VL(M[F[a]], 0); }
    size_t bytes = (size_t)NV / 8 + 1;
    uint8_t **FE = malloc(sizeof(void *) * nsrc), **FD = malloc(sizeof(void *) * nsrc);
    long *ce = calloc(nsrc, sizeof(long)), *cd = calloc(nsrc, sizeof(long));
    set_eq();
    for (int s = 0; s < nsrc; s++) { FE[s] = calloc(bytes, 1); ce[s] = bfs_far(srcv[s], FE[s]); }
    long eqtot = 0; for (int s = 0; s < nsrc; s++) eqtot += ce[s];
    printf("EQUAL graph (phi_j = M): freed sources %d, far pairs %ld\n", nsrc, eqtot); fflush(stdout);

    build_sigma(mode);
    set_diff();
    {
        int md; long m, asym; basic_stats(&md, &m, &asym);
        printf("THREE-bijection graph: n=%d edges=%ld maxdeg=%d asymmetric adjacencies %ld\n", NV, m, md, asym); fflush(stdout);
        if (asym) { fprintf(stderr, "adjacency not symmetric\n"); return 1; }
    }
    for (int s = 0; s < nsrc; s++) { FD[s] = calloc(bytes, 1); cd[s] = bfs_far(srcv[s], FD[s]); }
    long dtot = 0, covered = 0, newfar = 0, both = 0;
    long cntE[3][8], cntC[3][8];
    memset(cntE, 0, sizeof cntE); memset(cntC, 0, sizeof cntC);
    for (int s = 0; s < nsrc; s++) {
        long cov = 0, nw = 0;
        for (int v = 0; v < NV; v++) {
            int e = bitof(FE[s], v), d = bitof(FD[s], v);
            if (!e && !d) continue;
            int type = v >= HB ? 2 : ((v % (2 * N)) >= N ? 1 : 0), copy = v >= HB ? 0 : v / (2 * N);
            if (e && !d) { cov++; cntC[type][copy]++; }
            if (!e && d) { nw++; }
            if (e) cntE[type][copy]++;
            if (e && d) both++;
        }
        covered += cov; newfar += nw; dtot += cd[s];
        printf("src %2d %s: eq far %ld, three-bij far %ld, covered by new routes %ld, new far %ld\n",
               s / 2, (s & 1) ? "line " : "point", ce[s], cd[s], cov, nw);
        fflush(stdout);
    }
    printf("TOTAL: eq far %ld, three-bij far %ld, covered by new routes %ld (%.1f%% of eq far), new far %ld, far in both %ld\n",
           eqtot, dtot, covered, eqtot ? 100.0 * covered / eqtot : 0.0, newfar, both);
    const char *tn[3] = {"point", "line", "hub"};
    printf("eq far by type/copy (copy 0..6) and covered-by-new-routes in brackets:\n");
    for (int t = 0; t < 3; t++) {
        printf("  %-5s", tn[t]);
        for (int c = 0; c < 7; c++) printf(" %6ld[%ld]", cntE[t][c], cntC[t][c]);
        printf("\n");
    }
    return 0;
}
