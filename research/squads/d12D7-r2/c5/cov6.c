/* cov6.c (c5 scratch): which targets does each point-side hub g reach within 6 in G - h?  Bit-parallel BFS (64 sources
   per pass), so that a set of hub neighbours of h can be chosen by max-coverage of the targets that h's owners miss.
   Usage: cov6 EDGES H OWNERS(comma list of 4 vertex ids) CANDLO CANDHI SEL_K OUT_PREFIX
   Writes OUT_PREFIX.cov (binary bitsets over U) and OUT_PREFIX.U (vertex ids of U), prints greedy + swap result. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int64_t n; static int64_t *st; static int32_t *adj;
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: cov6 EDGES H OWNERS CANDLO CANDHI SEL_K OUT_PREFIX\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); long nn; if (!f || fscanf(f, "%ld", &nn) != 1) return 2; n = nn;
    int64_t cap = 1 << 23, m = 0; int32_t *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    int32_t H = atoi(argv[2]);
    int owners[8], no = 0; { char *s = strdup(argv[3]); for (char *t = strtok(s, ","); t; t = strtok(NULL, ",")) owners[no++] = atoi(t); }
    int32_t clo = atoi(argv[4]), chi = atoi(argv[5]); int K = atoi(argv[6]); const char *outp = argv[7];
    /* CSR without vertex H (its edges removed) */
    int64_t *deg = calloc(n + 1, 8);
    for (int64_t i = 0; i < m; i++) { if (U[i] == H || W[i] == H) continue; deg[U[i]]++; deg[W[i]]++; }
    st = malloc((n + 1) * 8); st[0] = 0; for (int64_t v = 0; v < n; v++) st[v + 1] = st[v] + deg[v];
    adj = malloc((st[n] + 1) * 4); int64_t *pos = calloc(n, 8);
    for (int64_t i = 0; i < m; i++) { if (U[i] == H || W[i] == H) continue; adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(pos); free(U); free(W); free(deg);
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    /* 1) owners: multi-source depth 6 (bits 0..no-1) */
    memset(vis, 0, n * 8); memset(fr, 0, n * 8);
    for (int i = 0; i < no; i++) { vis[owners[i]] |= 1ULL << i; fr[owners[i]] |= 1ULL << i; }
    for (int lev = 1; lev <= 6; lev++) {
        for (int64_t x = 0; x < n; x++) { uint64_t acc = 0; for (int64_t i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; }
        for (int64_t x = 0; x < n; x++) vis[x] |= nx[x];
        uint64_t *t = fr; fr = nx; nx = t;
    }
    /* U = targets not reached by owners, excluding H */
    int32_t *Uv = malloc(n * 4); int64_t nu = 0; int64_t *uidx = malloc(n * 8);
    for (int64_t x = 0; x < n; x++) { uidx[x] = -1; if (x == H) continue; if (vis[x] == 0) { uidx[x] = nu; Uv[nu++] = (int32_t)x; } }
    int64_t W64 = (nu + 63) / 64;
    fprintf(stderr, "owners reach: |U| = %lld targets not within 6 of the owners (excluding H)\n", (long long)nu);
    /* 2) candidates in passes of 64 */
    int64_t nc = chi - clo + 1; uint64_t *cov = calloc(nc * W64, 8);
    for (int64_t c0 = 0; c0 < nc; c0 += 64) {
        int64_t cnt = (nc - c0 < 64) ? nc - c0 : 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int64_t k = 0; k < cnt; k++) { int32_t g = clo + c0 + k; vis[g] |= 1ULL << k; fr[g] |= 1ULL << k; }
        for (int lev = 1; lev <= 6; lev++) {
            for (int64_t x = 0; x < n; x++) { uint64_t acc = 0; for (int64_t i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; }
            for (int64_t x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (int64_t u = 0; u < nu; u++) {
            uint64_t bits = vis[Uv[u]]; if (!bits) continue;
            int64_t w = u >> 6; uint64_t bit = 1ULL << (u & 63);
            while (bits) { int k = __builtin_ctzll(bits); bits &= bits - 1; cov[(c0 + k) * W64 + w] |= bit; }
        }
        if ((c0 / 64) % 20 == 0) fprintf(stderr, "pass %lld/%lld\n", (long long)(c0 / 64), (long long)((nc + 63) / 64));
    }
    /* 3) write outputs */
    char fn[512]; sprintf(fn, "%s.cov", outp); FILE *g = fopen(fn, "wb"); fwrite(cov, 8, nc * W64, g); fclose(g);
    sprintf(fn, "%s.U", outp); g = fopen(fn, "wb"); fwrite(Uv, 4, nu, g); fclose(g);
    /* 4) greedy max coverage of U with K sets, then 1-swap local search */
    uint64_t *covd = calloc(W64, 8); int *sel = malloc(sizeof(int) * K); char *inSel = calloc(nc, 1);
    int64_t got = 0;
    for (int s = 0; s < K; s++) {
        int64_t best = -1, bestc = -1;
        for (int64_t c = 0; c < nc; c++) if (!inSel[c]) {
            int64_t cc = 0; for (int64_t w = 0; w < W64; w++) cc += __builtin_popcountll(cov[c * W64 + w] & ~covd[w]);
            if (cc > bestc) { bestc = cc; best = c; }
        }
        sel[s] = (int)best; inSel[best] = 1; got += bestc;
        for (int64_t w = 0; w < W64; w++) covd[w] |= cov[best * W64 + w];
        printf("greedy %d: candidate hub %d (+%lld), uncovered %lld\n", s + 1, (int)(clo + best), (long long)bestc, (long long)(nu - got));
    }
    /* swap search */
    for (int it = 0; it < 30; it++) {
        int improved = 0;
        for (int s = 0; s < K; s++) {
            /* coverage of the others */
            uint64_t *oth = calloc(W64, 8);
            for (int t = 0; t < K; t++) if (t != s) for (int64_t w = 0; w < W64; w++) oth[w] |= cov[(int64_t)sel[t] * W64 + w];
            int64_t base = 0; for (int64_t w = 0; w < W64; w++) base += __builtin_popcountll(oth[w]);
            int64_t bestc = -1, bestc_id = -1;
            for (int64_t c = 0; c < nc; c++) if (!inSel[c]) {
                int64_t cc = 0; for (int64_t w = 0; w < W64; w++) cc += __builtin_popcountll(cov[c * W64 + w] | oth[w]);
                if (cc > bestc) { bestc = cc; bestc_id = c; }
            }
            int64_t cur = 0; for (int64_t w = 0; w < W64; w++) cur += __builtin_popcountll(cov[(int64_t)sel[s] * W64 + w] | oth[w]);
            if (bestc > cur) { inSel[sel[s]] = 0; inSel[bestc_id] = 1; sel[s] = (int)bestc_id; improved = 1; }
            free(oth);
        }
        int64_t tot = 0; { uint64_t *all = calloc(W64, 8); for (int s = 0; s < K; s++) for (int64_t w = 0; w < W64; w++) all[w] |= cov[(int64_t)sel[s] * W64 + w];
            for (int64_t w = 0; w < W64; w++) tot += __builtin_popcountll(all[w]); free(all); }
        printf("swap round %d: uncovered %lld\n", it + 1, (long long)(nu - tot));
        if (!improved) break;
    }
    printf("selected (candidate hub ids):");
    for (int s = 0; s < K; s++) printf(" %lld", (long long)(clo + sel[s])); printf("\n");
    return 0;
}
