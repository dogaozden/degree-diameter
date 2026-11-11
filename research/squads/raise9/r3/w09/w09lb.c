/* w09lb: lower bound for Z_M covers of a Haar base H(G,S), d = |S| <= 6.
 * Each length-8 walk (4 pairs) with base product g has a net voltage vector n in Z^{d-1} (c_e = 0).
 * A fiber g needs M distinct voltage values, so uncovered_g >= M - K_g where K_g = #distinct (g,n).
 * Prints K_g min/histogram and LB(M) = sum_g max(0, M-K_g) per side, side A (s^-1 t), side B (s t^-1).
 * usage: w09lb SOL */
#define main haar_gen3_main
#include "/home/user/degree-diameter/research/frontier/haar_gen3.c"
#undef main
#include <stdint.h>
static int cmpu(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[4096];
    fgets(line, sizeof line, f);
    char *tok[64]; int nt = 0; char *p = strtok(line, " \n"); while (p && nt < 64) { tok[nt++] = p; p = strtok(NULL, " \n"); }
    d = atoi(tok[0]); int gi = 2; char *gargv[16]; int ga = 1; gargv[0] = "g";
    while (gi < nt && strcmp(tok[gi], "n")) gargv[ga++] = tok[gi++];
    ncyc = atoi(tok[gi + 1]);
    int aidx = 1; Q = parse_group(gargv, ga, &aidx);
    N = Q->order * ncyc; ident = Q->ident * ncyc;
    CHI = malloc(Q->order); memset(CHI, 1, Q->order);
    int Sg[MAXD];
    for (int i = 0; i < d; i++) { fgets(line, sizeof line, f); Sg[i] = atoi(strtok(line, " \n")); }
    fclose(f);
    if (Sg[0] != ident) fprintf(stderr, "warning: first generator not identity\n");
    int total = 1; for (int i = 0; i < 8; i++) total *= d;
    uint64_t *keys = malloc(sizeof(uint64_t) * total);
    for (int side = 0; side < 2; side++) {
        int nk = 0;
        for (int code = 0; code < total; code++) {
            int c = code, idx[8]; for (int i = 0; i < 8; i++) { idx[i] = c % d; c /= d; }
            int g = ident; int net[MAXD] = {0};
            for (int i = 0; i < 4; i++) {
                int s = Sg[idx[2 * i]], t = Sg[idx[2 * i + 1]];
                int y = side == 0 ? gmul(ginv(s), t) : gmul(s, ginv(t));
                g = gmul(g, y);
                int ps = idx[2 * i], pt = idx[2 * i + 1];
                if (side == 0) { if (pt) net[pt]++; if (ps) net[ps]--; }
                else { if (ps) net[ps]++; if (pt) net[pt]--; }
            }
            uint64_t nc = 0; for (int i = 1; i < d; i++) nc = nc * 17 + (uint64_t)(net[i] + 8);
            keys[nk++] = ((uint64_t)g << 32) | nc;
        }
        qsort(keys, nk, sizeof(uint64_t), cmpu);
        int *Kg = calloc(N, sizeof(int)); int i = 0;
        while (i < nk) { int j = i; while (j < nk && keys[j] == keys[i]) j++; Kg[keys[i] >> 32]++; i = j; }
        int mn = 1 << 30, mx = 0; long long hist[64] = {0}; int nz = 0;
        for (int g = 0; g < N; g++) { if (Kg[g] < mn) mn = Kg[g]; if (Kg[g] > mx) mx = Kg[g]; if (Kg[g] < 64) hist[Kg[g]]++; if (Kg[g] == 0) nz++; }
        printf("side %s: |G|=%d min K_g=%d max=%d zero-fibers=%d\n  hist K_g:", side ? "B(SS^-1)^4" : "A(S^-1S)^4", N, mn, mx, nz);
        for (int k = 0; k < 16; k++) printf(" %d:%lld", k, hist[k]);
        printf("\n  LB per side: ");
        for (int M = 2; M <= 8; M++) { long long lb = 0; for (int g = 0; g < N; g++) if (Kg[g] < M) lb += M - Kg[g]; printf("M=%d:%lld ", M, lb); }
        printf("\n");
        free(Kg);
    }
    return 0;
}
