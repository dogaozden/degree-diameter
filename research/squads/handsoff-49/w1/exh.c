/* exh: exhaustive Haar-cost scan for a group table (groups.py .bin format: int32 N, N*N uint16, identity 0).
 * H(G,S), S = {e, r, b, c}, r ranges over one representative per conjugacy class (every S is conjugate to one
 * containing a class rep, so this covers all Haar graphs up to inner automorphism and translation).
 * cost = #x not in B4(U) + #x not in B4(V), U = {t^-1 s}, V = {s t^-1} (same as haar_tab for d=4, D=9).
 * usage: exh BIN BOUND R0 R1   (class reps with index in [R0,R1); prints min, zero count, histogram <= BOUND)
 * Prints "ZERO" lines for cost 0 and the sets achieving the running minimum. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N; static uint16_t *T; static int *INV;
static unsigned char *vis; static int *fr, *nf;
static int ball_uncov(const int *gens, int ng, int bound, int *cnt_out) {
    /* returns uncovered count after radius 4, or >= bound early */
    memset(vis, 0, N); vis[0] = 1; int nfr = 1, tot = 1; fr[0] = 0;
    for (int lev = 0; lev < 4; lev++) {
        int m = 0;
        for (int i = 0; i < nfr; i++) {
            int x = fr[i];
            for (int j = 0; j < ng; j++) { int y = T[(size_t)gens[j] * N + x]; if (!vis[y]) { vis[y] = 1; nf[m++] = y; } }
        }
        tot += m; int *t = fr; fr = nf; nf = t; nfr = m;
        if (lev == 2) {  /* after radius 3: max possible uncovered after level 4 is N - tot - ... prune */
            int maxadd = nfr * ng; int lowest_uncov = N - tot - maxadd; if (lowest_uncov < 0) lowest_uncov = 0;
            if (lowest_uncov >= bound) { *cnt_out = tot; return lowest_uncov; }
        }
        if (nfr == 0) break;
    }
    *cnt_out = tot;
    return N - tot;
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: exh BIN BOUND R0 R1\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2;
    N = n32; T = malloc((size_t)N * N * 2); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    int bound = atoi(argv[2]); int R0 = atoi(argv[3]), R1 = atoi(argv[4]);
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) { INV[x] = -1; for (int y = 0; y < N; y++) if (T[(size_t)x * N + y] == 0) { INV[x] = y; break; } }
    /* conjugacy classes: cls[x] = smallest element of the class */
    int *cls = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) cls[x] = -1;
    int *reps = malloc(sizeof(int) * N); int nreps = 0;
    for (int x = 0; x < N; x++) {
        if (cls[x] >= 0) continue;
        reps[nreps++] = x;
        for (int h = 0; h < N; h++) { int y = T[(size_t)T[(size_t)h * N + x] * N + INV[h]]; if (cls[y] < 0) cls[y] = x; }
    }
    /* drop identity class */
    int ri = 0; int *R = malloc(sizeof(int) * nreps); int nR = 0;
    for (int i = 0; i < nreps; i++) if (reps[i] != 0) R[nR++] = reps[i];
    fprintf(stderr, "N=%d classes=%d (non-identity reps %d) range [%d,%d)\n", N, nreps, nR, R0, R1);
    if (R1 > nR) R1 = nR; (void)ri;
    vis = malloc(N); fr = malloc(sizeof(int) * N); nf = malloc(sizeof(int) * N);
    int best = bound; long long evals = 0, zeros = 0; int hist[64] = {0};
    int gens[16]; int ng;
    for (int ri2 = R0; ri2 < R1; ri2++) {
        int r = R[ri2];
        for (int b = 1; b < N; b++) { if (b == r) continue;
            for (int c = b + 1; c < N; c++) { if (c == r) continue;
                int S[4] = {0, r, b, c};
                /* U side */
                int U[12]; ng = 0;
                for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { int u = T[(size_t)INV[S[j]] * N + S[i]]; if (u == 0) continue; int dup = 0; for (int k = 0; k < ng; k++) if (U[k] == u) { dup = 1; break; } if (!dup) U[ng++] = u; }
                int cnt; int cu = ball_uncov(U, ng, best, &cnt);
                if (cu >= best) { evals++; continue; }
                int V[12]; int nv = 0;
                for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { int v = T[(size_t)S[i] * N + INV[S[j]]]; if (v == 0) continue; int dup = 0; for (int k = 0; k < nv; k++) if (V[k] == v) { dup = 1; break; } if (!dup) V[nv++] = v; }
                int cv = ball_uncov(V, nv, best - cu, &cnt);
                int cost = cu + cv; evals++; if (evals % 200000 == 0) { fprintf(stderr, "evals %lld best %d\n", evals, best); }
                if (cost < 64) hist[cost]++;
                if (cost < best || cost == 0) {
                    if (cost < best) best = cost;
                    if (cost == 0) zeros++;
                    printf("cost %d cu %d cv %d S = {0,%d,%d,%d} class_rep %d\n", cost, cu, cv, r, b, c, r); fflush(stdout);
                }
            }
        }
        fprintf(stderr, "rep %d (elem %d) done; evals %lld best %d\n", ri2, r, evals, best);
    }
    printf("DONE evals=%lld best=%d zeros=%lld\n", evals, best, zeros);
    printf("hist:"); for (int i = 0; i < 20; i++) printf(" %d", hist[i]); printf("\n");
    return 0;
}
