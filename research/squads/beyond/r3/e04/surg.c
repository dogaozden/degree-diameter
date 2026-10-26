/* e04: friendly-transition surgery + hubs on the typed level graph of H(q) (D7_HEXAGON.md Sec. 2-4, 6-8).
   Layout: M = 2r+1 levels with types given by a string over {H,D} (e.g. HDHDH for r = 2).
   Friendly transitions (types differ, matching = identity on the common element set) carry freed sets:
     H -> D (points freed): F = non-collinear point set (greedy)   [segment set, Theorem B]
     D -> H (lines freed):  G = non-concurrent line set (greedy)   [dual segment set, Theorem B]
   Non-friendly transitions carry no freed set and a random bijection (H->H: P->L; D->D: L->P); Theorem A covers them.
   Hubs: K = min(|F|, |G|, Kcap) B-hubs and K A-hubs; B-hub i takes the i-th free A-slot of every level, A-hub i the
   i-th free B-slot of every level; hub graph Y = union of q-r random perfect matchings between the two hub sets
   (degree <= q-r, so hub degree <= 2r+1+q-r = q+1+r).
   Usage: surg q r TYPES seed Kcap OUT.edges     (OUT = "sizes": only print |F|, |G|)
   Cache: hex_q{q}.bin in the working directory (built if absent). */
#include "hexpart.h"

static int cmpll(const void *a, const void *b) {
    const int64_t *x = a, *y = b; return x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : x[1] < y[1] ? -1 : x[1] > y[1];
}

static uint64_t rs;
static uint64_t rnd(void) { uint64_t z = (rs += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: surg q r TYPES seed Kcap OUT\n"); return 1; }
    q = atoi(argv[1]); R = atoi(argv[2]); const char *types = argv[3];
    uint64_t seed = strtoull(argv[4], 0, 10); long Kcap = atol(argv[5]); const char *out = argv[6];
    for (p = 2; q % p; p++) {}
    field();
    { int pe = 1; for (int i = 0; i < e; i++) pe *= p; if (pe != q) die("unsupported q"); }
    int Q1 = q + 1;
    char cfn[64]; sprintf(cfn, "hex_q%d.bin", q);
    FILE *cf = fopen(cfn, "rb");
    if (cf) {
        int32_t hd[2]; if (fread(hd, 4, 2, cf) != 2) die("cache header");
        N = hd[0]; LL = hd[1];
        LP = malloc(sizeof(int32_t) * (int64_t)N * Q1);
        if (fread(LP, 4, (size_t)N * Q1, cf) != (size_t)N * Q1) die("cache body");
        fclose(cf);
        PL = malloc(sizeof(int32_t) * (int64_t)N * Q1); int *fill = calloc(N, sizeof(int));
        for (int l = 0; l < LL; l++) for (int s = 0; s < Q1; s++) { int pp = LP[(int64_t)l * Q1 + s]; PL[(int64_t)pp * Q1 + fill[pp]++] = l; }
    } else {
        build_hex();
        cf = fopen(cfn, "wb"); int32_t hd[2] = {N, LL};
        fwrite(hd, 4, 2, cf); fwrite(LP, 4, (size_t)N * Q1, cf); fclose(cf);
    }
    M = 2 * R + 1;
    if ((int)strlen(types) != M) die("TYPES must have 2r+1 letters");
    rs = seed * 7919 + 12345;

    /* greedy non-collinear point set F and non-concurrent line set G, random order */
    int32_t *ord = malloc(sizeof(int32_t) * N);
    for (int i = 0; i < N; i++) ord[i] = i;
    for (int i = N - 1; i > 0; i--) { int jj = (int)(rnd() % (uint64_t)(i + 1)); int32_t t = ord[i]; ord[i] = ord[jj]; ord[jj] = t; }
    char *blk = calloc(N, 1); char *inF = calloc(2 * N, 1); int nF = 0;
    for (int ii = 0; ii < N; ii++) {
        int x = ord[ii]; if (blk[x]) continue;
        inF[x] = 1; nF++; blk[x] = 1;
        for (int s = 0; s < Q1; s++) { int l = PL[(int64_t)x * Q1 + s]; for (int t2 = 0; t2 < Q1; t2++) blk[LP[(int64_t)l * Q1 + t2]] = 1; }
    }
    for (int i = LL - 1; i > 0; i--) { int jj = (int)(rnd() % (uint64_t)(i + 1)); int32_t t = ord[i]; ord[i] = ord[jj]; ord[jj] = t; }
    memset(blk, 0, N); char *inG = calloc(2 * N, 1); int nG = 0;
    for (int ii = 0; ii < LL; ii++) {
        int l = ord[ii]; if (blk[l]) continue;
        inG[N + l] = 1; nG++; blk[l] = 1;
        for (int s = 0; s < Q1; s++) { int x = LP[(int64_t)l * Q1 + s]; for (int t2 = 0; t2 < Q1; t2++) blk[PL[(int64_t)x * Q1 + t2]] = 1; }
    }
    if (!strcmp(out, "sizes")) { printf("q=%d r=%d nF=%d nG=%d min=%d\n", q, R, nF, nG, nF < nG ? nF : nG); return 0; }
    int K = nF < nG ? nF : nG; if (K > Kcap) K = (int)Kcap;
    fprintf(stderr, "q=%d r=%d types=%s nF=%d nG=%d K=%d\n", q, R, types, nF, nG, K);

    /* per transition t = j*R + (k-1): element map mp[t][e] for A-elements e of level j, and freed flags */
    int32_t **mp = malloc(sizeof(int32_t *) * M * R);
    char **fr = malloc(sizeof(char *) * M * R);
    int32_t *perm = malloc(sizeof(int32_t) * N);
    int nfree_tr = 0;
    for (int j = 0; j < M; j++) for (int k = 1; k <= R; k++) {
        int t = j * R + (k - 1), jt = (j + k) % M;
        int friendly = types[j] != types[jt];
        mp[t] = malloc(sizeof(int32_t) * 2 * N); fr[t] = calloc(2 * N, 1);
        for (int i = 0; i < N; i++) perm[i] = i;
        for (int i = N - 1; i > 0; i--) { int jj = (int)(rnd() % (uint64_t)(i + 1)); int32_t tt = perm[i]; perm[i] = perm[jj]; perm[jj] = tt; }
        for (int e2 = 0; e2 < 2 * N; e2++) mp[t][e2] = -1;
        if (types[j] == 'H') {            /* A = points */
            for (int x = 0; x < N; x++) {
                if (friendly) { mp[t][x] = x; fr[t][x] = inF[x]; nfree_tr += inF[x]; }
                else mp[t][x] = N + perm[x];
            }
        } else {                          /* A = lines */
            for (int l = 0; l < LL; l++) {
                if (friendly) { mp[t][N + l] = N + l; fr[t][N + l] = inG[N + l]; nfree_tr += inG[N + l]; }
                else mp[t][N + l] = perm[l];
            }
        }
    }
    /* slot lists per level: A-slots (a,j) for out-transitions, B-slots (b,j) for in-transitions */
    int **Aslot = malloc(sizeof(int *) * M), **Bslot = malloc(sizeof(int *) * M);
    int *nA = calloc(M, sizeof(int)), *nB = calloc(M, sizeof(int));
    for (int j = 0; j < M; j++) { Aslot[j] = malloc(sizeof(int) * (size_t)(2 * N * R + 1)); Bslot[j] = malloc(sizeof(int) * (size_t)(2 * N * R + 1)); }
    for (int j = 0; j < M; j++) for (int k = 1; k <= R; k++) {
        int t = j * R + (k - 1);
        for (int e2 = 0; e2 < 2 * N; e2++) if (fr[t][e2]) Aslot[j][nA[j]++] = e2 * M + j;
        int jin = (j - k + M) % M, tin = jin * R + (k - 1);
        for (int e2 = 0; e2 < 2 * N; e2++) if (fr[tin][e2]) Bslot[j][nB[j]++] = mp[tin][e2] * M + j;
    }
    int minA = 1 << 30, minB = 1 << 30;
    for (int j = 0; j < M; j++) { if (nA[j] < minA) minA = nA[j]; if (nB[j] < minB) minB = nB[j]; }
    fprintf(stderr, "slots: min alpha=%d min beta=%d (per level:", minA, minB);
    for (int j = 0; j < M; j++) fprintf(stderr, " %d/%d", nA[j], nB[j]);
    fprintf(stderr, ")\n");
    if (K > minA) K = minA;
    if (K > minB) K = minB;
    int dY = q - R; if (dY < 1) die("q-r < 1");
    long long nLevel = 2LL * N * M;
    long long nVtx = nLevel + 2LL * K;
    int64_t Bh0 = nLevel, Ah0 = nLevel + K;       /* B-hubs, A-hubs */

    /* hub graph Y: union of dY random perfect matchings between the hub sets, deduplicated */
    int64_t *Yp = malloc(sizeof(int64_t) * 2 * (size_t)K * dY + 2); long nY = 0;
    int32_t *pi = malloc(sizeof(int32_t) * (K + 1));
    for (int t = 0; t < dY; t++) {
        for (int i = 0; i < K; i++) pi[i] = i;
        for (int i = K - 1; i > 0; i--) { int jj = (int)(rnd() % (uint64_t)(i + 1)); int32_t tt = pi[i]; pi[i] = pi[jj]; pi[jj] = tt; }
        for (int i = 0; i < K; i++) { Yp[2 * nY] = i; Yp[2 * nY + 1] = pi[i]; nY++; }
    }
    qsort(Yp, nY, 2 * sizeof(int64_t), cmpll);
    long nYu = 0;
    for (long i = 0; i < nY; i++) if (i == 0 || Yp[2 * i] != Yp[2 * (nYu - 1)] || Yp[2 * i + 1] != Yp[2 * (nYu - 1) + 1]) {
        Yp[2 * nYu] = Yp[2 * i]; Yp[2 * nYu + 1] = Yp[2 * i + 1]; nYu++;
    }

    FILE *f = fopen(out, "w"); if (!f) die("open out");
    fprintf(f, "%lld\n", nVtx);
    long long ne = 0;
    /* level incidences (point side writes each edge once) */
    for (int l = 0; l < LL; l++) for (int s = 0; s < Q1; s++) {
        int x = LP[(int64_t)l * Q1 + s];
        for (int j = 0; j < M; j++) { fprintf(f, "%lld %lld\n", (long long)(x * M + j), (long long)((N + l) * M + j)); ne++; }
    }
    /* matching edges of the non-freed elements */
    for (int j = 0; j < M; j++) {
        int a0 = types[j] == 'H' ? 0 : N, a1 = types[j] == 'H' ? N : 2 * N;
        for (int k = 1; k <= R; k++) {
            int t = j * R + (k - 1), jt = (j + k) % M;
            for (int e2 = a0; e2 < a1; e2++) {
                if (fr[t][e2]) continue;
                fprintf(f, "%lld %lld\n", (long long)(e2 * M + j), (long long)(mp[t][e2] * M + jt)); ne++;
            }
        }
    }
    /* hub edges: B-hub i takes A-slot i of every level; A-hub i takes B-slot i of every level */
    for (int i = 0; i < K; i++) for (int j = 0; j < M; j++) {
        fprintf(f, "%lld %lld\n", (long long)(Bh0 + i), (long long)Aslot[j][i]); ne++;
        fprintf(f, "%lld %lld\n", (long long)(Ah0 + i), (long long)Bslot[j][i]); ne++;
    }
    for (long i = 0; i < nYu; i++) { fprintf(f, "%lld %lld\n", (long long)(Bh0 + Yp[2 * i]), (long long)(Ah0 + Yp[2 * i + 1])); ne++; }
    fclose(f);
    fprintf(stderr, "wrote %s: n=%lld edges=%lld K=%d Y-edges=%ld maxdeg=%d (levels %d, hub degree %d)\n", out, nVtx, ne, K, nYu,
            q + 1 + R, M, 2 * R + 1 + dY);
    printf("RESULT q=%d r=%d types=%s K=%d n=%lld Delta=%d\n", q, R, types, K, nVtx, q + 1 + R);
    return 0;
}
