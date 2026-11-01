/* exh2: exhaustive Haar-cost scan for a group table (groups.py .bin format: int32 N, N*N uint16, identity 0).
 * H(G,S), S = {e, r, b, c}. r ranges over one representative per non-identity conjugacy class (every S containing e
 * is conjugate to one containing a class rep). For fixed r let C = C_G(r). Conjugation by h in C fixes e and r and
 * maps S to hSh^-1 (same Haar graph up to automorphism), so b can be taken as a conjugation-orbit representative of C
 * on G \ {e,r}, and c ranges over all of G \ {e,r,b}. This covers every S up to inner automorphism.
 * cost = #x not in B4(U) + #x not in B4(V), U = {t^-1 s}, V = {s t^-1} (w1's exh.c, same cost).
 * usage: exh2 BIN BOUND R0 R1   (class reps with index in [R0,R1) over the non-identity reps; prints "cost ..." lines
 * for every set with cost < best (best starts at BOUND, so a final best = BOUND means nothing below BOUND) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int N; static uint16_t *T; static int *INV;
static unsigned char *vis; static int *fr, *nf;
static int ball_uncov(const int *gens, int ng, int bound, int *cnt_out) {
    memset(vis, 0, N); vis[0] = 1; int nfr = 1, tot = 1; fr[0] = 0;
    for (int lev = 0; lev < 4; lev++) {
        int m = 0;
        for (int i = 0; i < nfr; i++) {
            int x = fr[i];
            for (int j = 0; j < ng; j++) { int y = T[(size_t)gens[j] * N + x]; if (!vis[y]) { vis[y] = 1; nf[m++] = y; } }
        }
        tot += m; int *t = fr; fr = nf; nf = t; nfr = m;
        if (lev == 2) {
            int maxadd = nfr * ng; int lowest_uncov = N - tot - maxadd; if (lowest_uncov < 0) lowest_uncov = 0;
            if (lowest_uncov >= bound) { *cnt_out = tot; return lowest_uncov; }
        }
        if (nfr == 0) break;
    }
    *cnt_out = tot;
    return N - tot;
}
static int cjg(int h, int x) { return T[(size_t)T[(size_t)h * N + x] * N + INV[h]]; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: exh2 BIN BOUND R0 R1\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2;
    N = n32; T = malloc((size_t)N * N * 2); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    int bound = atoi(argv[2]); int R0 = atoi(argv[3]), R1 = atoi(argv[4]);
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) { INV[x] = -1; for (int y = 0; y < N; y++) if (T[(size_t)x * N + y] == 0) { INV[x] = y; break; } }
    int *cls = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) cls[x] = -1;
    int *reps = malloc(sizeof(int) * N); int nreps = 0;
    for (int x = 0; x < N; x++) {
        if (cls[x] >= 0) continue;
        reps[nreps++] = x;
        for (int h = 0; h < N; h++) { int y = cjg(h, x); if (cls[y] < 0) cls[y] = x; }
    }
    int *R = malloc(sizeof(int) * nreps); int nR = 0;
    for (int i = 0; i < nreps; i++) if (reps[i] != 0) R[nR++] = reps[i];
    if (R1 > nR) R1 = nR;
    fprintf(stderr, "N=%d classes=%d (non-identity reps %d) range [%d,%d) bound %d\n", N, nreps, nR, R0, R1, bound);
    vis = malloc(N); fr = malloc(sizeof(int) * N); nf = malloc(sizeof(int) * N);
    int *Cen = malloc(sizeof(int) * N); unsigned char *seen = malloc(N); int *brep = malloc(sizeof(int) * N);
    int best = bound; long long evals = 0, zeros = 0;
    clock_t t0 = clock();
    for (int ri = R0; ri < R1; ri++) {
        int r = R[ri];
        int nC = 0;
        for (int h = 0; h < N; h++) if (T[(size_t)h * N + r] == T[(size_t)r * N + h]) Cen[nC++] = h;
        memset(seen, 0, N); seen[0] = 1; seen[r] = 1;
        int nb = 0;
        for (int x = 0; x < N; x++) {
            if (seen[x]) continue;
            brep[nb++] = x;
            for (int k = 0; k < nC; k++) seen[cjg(Cen[k], x)] = 1;
        }
        long long ev0 = evals;
        for (int bi = 0; bi < nb; bi++) {
            int b = brep[bi];
            for (int c = 0; c < N; c++) {
                if (c == 0 || c == r || c == b) continue;
                int S[4] = {0, r, b, c};
                int U[12]; int ng = 0;
                for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { int u = T[(size_t)INV[S[j]] * N + S[i]]; if (u == 0) continue; int dup = 0; for (int k = 0; k < ng; k++) if (U[k] == u) { dup = 1; break; } if (!dup) U[ng++] = u; }
                int cnt; int cu = ball_uncov(U, ng, best, &cnt);
                evals++;
                if (cu >= best) continue;
                int V[12]; int nv = 0;
                for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { int v = T[(size_t)S[i] * N + INV[S[j]]]; if (v == 0) continue; int dup = 0; for (int k = 0; k < nv; k++) if (V[k] == v) { dup = 1; break; } if (!dup) V[nv++] = v; }
                int cv = ball_uncov(V, nv, best - cu, &cnt);
                int cost = cu + cv;
                if (cost < best || cost == 0) {
                    if (cost < best) best = cost;
                    if (cost == 0) zeros++;
                    printf("cost %d cu %d cv %d S = {0,%d,%d,%d} rep %d\n", cost, cu, cv, r, b, c, r); fflush(stdout);
                }
            }
        }
        fprintf(stderr, "rep %d (elem %d) |C|=%d orbits=%d evals %lld best %d time %.1fs\n", ri, r, nC, nb,
                evals - ev0, best, (double)(clock() - t0) / CLOCKS_PER_SEC);
    }
    printf("DONE range=[%d,%d) evals=%lld best=%d zeros=%lld time=%.1f\n", R0, R1, evals, best, zeros,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
