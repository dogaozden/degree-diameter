/* Exact minimum number of singular nonbacktracking patterns over 4-letter charts (fixed points w_s, b_s) that cover
   both diagonals and have every pencil complete, by scanning all combinations of per-letter star collineations
   (input from dp_prep.py).  Pairwise tables: pencils and singular counts depend on two letters' line data only.
   Output: min singular, number of optimal combinations, one optimal combination (collineation indices). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
#define K 4
int n[K]; u64 *U[K], *V[K]; /* per candidate: U[s][c*3+i], V[s][c*3+i], i over t != s in increasing order */
u64 eA, eB, bm[K], wm[K], FULL; int np; u64 *PL;
static int others(int s, int i) { int t = 0; for (int x = 0; x < K; x++) if (x != s) { if (t == i) return x; t++; } return -1; }
static int idx_of(int s, int t) { return t < s ? t : t - 1; }   /* position of label t in U[s][..] */
static int pencil_ok(u64 L, u64 *lines, int nl, u64 *pts, int npt) {
    for (int p = 0; p < np; p++) { if ((PL[p] & L) != L) continue;          /* plane through L */
        int hit = 0;
        for (int i = 0; i < nl && !hit; i++) if (lines[i] != L && (PL[p] & lines[i]) == lines[i]) hit = 1;
        for (int i = 0; i < npt && !hit; i++) if ((PL[p] & pts[i]) == pts[i] && !(pts[i] & L)) hit = 1;
        if (!hit) return 0; }
    return 1; }
static u64 linemask(u64 a, u64 b) { /* the line through two points (masks), from the plane list: intersection of planes containing both */
    u64 m = ~(u64)0; int any = 0;
    for (int p = 0; p < np; p++) if ((PL[p] & a) && (PL[p] & b)) { m &= PL[p]; any = 1; }
    return any ? m : 0; }
int main(void) {
    int kk; if (scanf("%d %lu %lu", &kk, &eA, &eB) != 3 || kk != K) return 2;
    for (int s = 0; s < K; s++) { if (scanf("%d", &n[s]) != 1) return 3; U[s] = malloc(8 * 3 * n[s]); V[s] = malloc(8 * 3 * n[s]);
        for (int c = 0; c < n[s]; c++) { for (int i = 0; i < 3; i++) if (scanf("%lu", &U[s][c * 3 + i]) != 1) return 4;
            for (int i = 0; i < 3; i++) if (scanf("%lu", &V[s][c * 3 + i]) != 1) return 4; } }
    for (int s = 0; s < K; s++) if (scanf("%lu", &bm[s]) != 1) return 5;
    for (int s = 0; s < K; s++) if (scanf("%lu", &wm[s]) != 1) return 5;
    if (scanf("%d", &np) != 1) return 6; PL = malloc(8 * np); for (int p = 0; p < np; p++) if (scanf("%lu", &PL[p]) != 1) return 6;
    FULL = 0; for (int p = 0; p < np; p++) FULL |= PL[p];
    /* pairwise tables for unordered pairs (s < s2): ok (pencils on both sides) and singular count (both orders, both sides) */
    int *S[K][K]; unsigned char *OK[K][K];
    for (int s = 0; s < K; s++) for (int s2 = s + 1; s2 < K; s2++) {
        S[s][s2] = malloc(sizeof(int) * n[s] * n[s2]); OK[s][s2] = malloc(n[s] * n[s2]);
        u64 LA = linemask(bm[s], bm[s2]), LB = linemask(wm[s], wm[s2]);
        u64 ptsA[K], ptsB[K]; int npt = 0; for (int t = 0; t < K; t++) if (t != s && t != s2) { ptsA[npt] = bm[t]; ptsB[npt] = wm[t]; npt++; }
        for (int a = 0; a < n[s]; a++) for (int b = 0; b < n[s2]; b++) {
            int sing = 0;
            for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
                if (U[s][a * 3 + i] & U[s2][b * 3 + j]) sing += 2;     /* patterns (t,s,s2,t') and (t',s2,s,t) */
                if (V[s][a * 3 + i] & V[s2][b * 3 + j]) sing += 2; }
            u64 lA[6], lB[6]; for (int i = 0; i < 3; i++) { lA[i] = V[s][a * 3 + i]; lA[3 + i] = V[s2][b * 3 + i]; lB[i] = U[s][a * 3 + i]; lB[3 + i] = U[s2][b * 3 + i]; }
            int ok = pencil_ok(LA, lA, 6, ptsA, npt) && pencil_ok(LB, lB, 6, ptsB, npt);
            S[s][s2][a * n[s2] + b] = sing; OK[s][s2][a * n[s2] + b] = ok; } }
    /* per-candidate diagonal masks */
    u64 *DA[K], *DB[K];
    for (int s = 0; s < K; s++) { DA[s] = malloc(8 * n[s]); DB[s] = malloc(8 * n[s]);
        for (int c = 0; c < n[s]; c++) { DA[s][c] = U[s][c * 3] | U[s][c * 3 + 1] | U[s][c * 3 + 2]; DB[s][c] = V[s][c * 3] | V[s][c * 3 + 1] | V[s][c * 3 + 2]; } }
    int best = getenv("BOUND") ? atoi(getenv("BOUND")) : 1000000; long nbest = 0; int bc[K] = {-1, -1, -1, -1}; long ndp = 0;
    for (int c0 = 0; c0 < n[0]; c0++) for (int c1 = 0; c1 < n[1]; c1++) {
        if (!OK[0][1][c0 * n[1] + c1]) continue; int p01 = S[0][1][c0 * n[1] + c1]; if (p01 > best) continue;
        for (int c2 = 0; c2 < n[2]; c2++) {
            if (!OK[0][2][c0 * n[2] + c2] || !OK[1][2][c1 * n[2] + c2]) continue;
            int p2 = p01 + S[0][2][c0 * n[2] + c2] + S[1][2][c1 * n[2] + c2]; if (p2 > best) continue;
            u64 ua = eA | DA[0][c0] | DA[1][c1] | DA[2][c2], ub = eB | DB[0][c0] | DB[1][c1] | DB[2][c2];
            for (int c3 = 0; c3 < n[3]; c3++) {
                if (((ua | DA[3][c3]) != FULL) || ((ub | DB[3][c3]) != FULL)) continue;
                if (!OK[0][3][c0 * n[3] + c3] || !OK[1][3][c1 * n[3] + c3] || !OK[2][3][c2 * n[3] + c3]) continue;
                ndp++;
                int tot = p2 + S[0][3][c0 * n[3] + c3] + S[1][3][c1 * n[3] + c3] + S[2][3][c2 * n[3] + c3];
                if (tot < best) { best = tot; nbest = 0; bc[0] = c0; bc[1] = c1; bc[2] = c2; bc[3] = c3; }
                if (tot == best) nbest++; } } }
    printf("min_singular %d count %ld example %d %d %d %d (diag+pencil combos seen under the bound: %ld)\n", best, nbest, bc[0], bc[1], bc[2], bc[3], ndp);
    return 0; }
