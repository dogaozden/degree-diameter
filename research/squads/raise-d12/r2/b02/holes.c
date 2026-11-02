#define main frob_main
#include "frob.c"
#undef main
int main(int argc, char **argv) {
    init_field();
    vis = malloc((NBITS / 64 + 2) * sizeof(uint64_t));
    q = malloc((size_t)NBITS * sizeof(uint32_t));
    FILE *f = fopen(argv[1], "r"); uint32_t S[16], Si[16]; int n = 0; char line[256];
    while (fgets(line, sizeof line, f)) { if (line[0] == '#') continue; unsigned a, j; if (sscanf(line, "%u %u", &a, &j) == 2) S[n++] = (j << 15) | a; }
    for (int k = 0; k < n; k++) Si[k] = inv(S[k]);
    bfs(S, Si, n, 0, 11);
    static uint8_t reached[NG]; memset(reached, 0, sizeof reached);
    /* B-vertices within 11 */
    for (int k = 1; k <= 11 && k < nl; k += 2) for (uint32_t i = lev[k]; i < lev[k + 1]; i++) reached[q[i] - NG] = 1;
    int nh = 0; long byj[NZ]; memset(byj, 0, sizeof byj);
    printf("holes (B-vertices at distance > 11 from (e,A)):\n");
    for (uint32_t h = 0; h < NG; h++) if (!reached[h]) { nh++; byj[h >> 15]++; if (nh <= 40) printf("  (a=%u, j=%u)\n", h & (FQ - 1), h >> 15); }
    printf("total holes %d\nj-histogram of holes (nonzero):", nh);
    for (int j = 0; j < NZ; j++) if (byj[j]) printf(" j%d:%ld", j, byj[j]);
    printf("\n");
    /* alpha-clumps: count holes fixed by alpha_3 and orbit sizes */
    int fixed = 0; for (uint32_t h = 0; h < NG; h++) if (!reached[h] && alpha(h, 3) == h) fixed++;
    printf("holes fixed by alpha: %d\n", fixed);
    return 0;
}
