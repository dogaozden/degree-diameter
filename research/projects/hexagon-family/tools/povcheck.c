/* povcheck HEXBIN SETFILE [opp|ncol]
   opp  (default): every two points of the set are opposite in H(q) (B(x,y) != 0); prints the size, and how many
        points outside are opposite to all of them (0 = maximal).
   ncol: no two points on a common line of H(q) (the q = 3^h duality construction); prints the size, the number of
        pairs at distance 4, and how many points outside could be added.
   Last line: "SCORE <size> VALID" or "SCORE 0 INVALID <reason>". */
#include "q6.h"
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: povcheck HEXBIN SETFILE [opp|ncol]\n"); return 1; }
    Hex h = hex_load(argv[1]); int *R; int n = read_ids(argv[2], &R);
    int ncol = argc > 3 && !strcmp(argv[3], "ncol"); int Q1 = h.q + 1;
    char *in = calloc(h.N, 1);
    for (int i = 0; i < n; i++) {
        if (R[i] < 0 || R[i] >= h.N) { printf("SCORE 0 INVALID id %d out of range\n", R[i]); return 0; }
        if (in[R[i]]) { printf("SCORE 0 INVALID duplicate id %d\n", R[i]); return 0; }
        in[R[i]] = 1;
    }
    if (!ncol) {
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
            if (Bxy(h.C + 7 * (size_t)R[i], h.C + 7 * (size_t)R[j]) == 0) { printf("SCORE 0 INVALID points %d %d not opposite\n", R[i], R[j]); return 0; }
        long ext = 0;
        for (int x = 0; x < h.N; x++) { if (in[x]) continue; int ok = 1; for (int i = 0; i < n && ok; i++) if (Bxy(h.C + 7 * (size_t)x, h.C + 7 * (size_t)R[i]) == 0) ok = 0; ext += ok; }
        printf("q=%d pairwise opposite set of %d points; %ld points outside are opposite to all\n", h.q, n, ext);
        printf("SCORE %d VALID\n", n);
    } else {
        char *cov = calloc(h.N, 1);   /* points collinear with some set point (or in it) */
        for (int i = 0; i < n; i++) for (int k = 0; k < Q1; k++) { int l = h.PL[(size_t)R[i] * Q1 + k];
            for (int t = 0; t < Q1; t++) { int y = h.LP[(size_t)l * Q1 + t]; if (y != R[i] && in[y]) { printf("SCORE 0 INVALID points %d %d collinear\n", R[i], y); return 0; } cov[y] = 1; } }
        long d4 = 0;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (Bxy(h.C + 7 * (size_t)R[i], h.C + 7 * (size_t)R[j]) == 0) d4++;
        long ext = 0; for (int x = 0; x < h.N; x++) if (!cov[x]) ext++;
        printf("q=%d non-collinear set of %d points; %ld pairs at distance 4; %ld points outside could be added\n", h.q, n, d4, ext);
        printf("SCORE %d VALID\n", n);
    }
    return 0;
}
