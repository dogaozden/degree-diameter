/* w09nb: for ANY regular voltage cover of order M of H(G,S): fiber g (same side) needs M distinct voltages;
 * distinct voltages <= R_g = number of non-backtracking walks of length 2..8 (even) from e on that side ending at g.
 * LB(M) = sum_g max(0, M - R_g) per side. usage: w09nb SOL */
#define main haar_gen3_main
#include "/home/user/degree-diameter/research/frontier/haar_gen3.c"
#undef main
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[4096]; fgets(line, sizeof line, f);
    char *tok[64]; int nt = 0; char *p = strtok(line, " \n"); while (p && nt < 64) { tok[nt++] = p; p = strtok(NULL, " \n"); }
    d = atoi(tok[0]); int gi = 2; char *gargv[16]; int ga = 1; gargv[0] = "g";
    while (gi < nt && strcmp(tok[gi], "n")) gargv[ga++] = tok[gi++];
    ncyc = atoi(tok[gi + 1]); int aidx = 1; Q = parse_group(gargv, ga, &aidx);
    N = Q->order * ncyc; ident = Q->ident * ncyc; CHI = malloc(Q->order); memset(CHI, 1, Q->order);
    int Sg[MAXD];
    for (int i = 0; i < d; i++) { fgets(line, sizeof line, f); Sg[i] = atoi(strtok(line, " \n")); }
    fclose(f);
    int Si[MAXD]; for (int i = 0; i < d; i++) Si[i] = ginv(Sg[i]);
    for (int side = 0; side < 2; side++) {
        /* cur[g*(d+1)+last] counts walks at vertex g on the start side (A) with last letter last (d = none) */
        long long *cur = calloc((size_t)N * (d + 1), sizeof(long long)), *nxt = calloc((size_t)N * (d + 1), sizeof(long long));
        long long *R = calloc(N, sizeof(long long));
        cur[(size_t)ident * (d + 1) + d] = 1; R[ident] += 1;
        for (int step = 1; step <= 4; step++) {   /* one double step = 2 letters */
            memset(nxt, 0, sizeof(long long) * N * (d + 1));
            /* half-step: from start-side vertex x (last letter L) to other side vertex (letter i), then the other side
               vertex y=S_i x (side A) or y = S_i^{-1} x (side B) ... implemented via the group: A side: y = s x, then
               back to start side by t^{-1} y, t != s. B side: y = s^{-1}... symmetric by using S^{-1} as generators. */
            for (int x = 0; x < N; x++) for (int L = 0; L <= d; L++) {
                long long c = cur[(size_t)x * (d + 1) + L]; if (!c) continue;
                for (int i = 0; i < d; i++) {
                    if (i == L) continue;               /* non-backtracking */
                    int sgen = side == 0 ? Sg[i] : Si[i];   /* side B walks use the inverse generators */
                    int y = gmul(sgen, x);               /* other side vertex */
                    /* back to start side: z = t^{-1} y, letter j != i */
                    for (int j = 0; j < d; j++) {
                        if (j == i) continue;
                        int tgen = side == 0 ? Sg[j] : Si[j];
                        int z = gmul(ginv(tgen), y);
                        nxt[(size_t)z * (d + 1) + j] += c;
                    }
                }
            }
            long long *tmp = cur; cur = nxt; nxt = tmp;
            for (int x = 0; x < N; x++) for (int L = 0; L <= d; L++) R[x] += cur[(size_t)x * (d + 1) + L];
        }
        int mn = 1 << 30, mx = 0; long long hist[40] = {0};
        for (int g = 0; g < N; g++) { if (R[g] < mn) mn = R[g]; if (R[g] > mx) mx = R[g]; if (R[g] < 40) hist[R[g]]++; }
        printf("side %s: min R_g=%d max=%lld; hist:", side ? "B" : "A", mn, mx);
        for (int k = 0; k < 12; k++) printf(" %d:%lld", k, hist[k]);
        printf("\n  LB(M) per side: ");
        for (int M = 2; M <= 8; M++) { long long lb = 0; for (int g = 0; g < N; g++) if (R[g] < M) lb += M - R[g]; printf("M=%d:%lld ", M, lb); }
        printf("\n");
        free(cur); free(nxt); free(R);
    }
    return 0;
}
