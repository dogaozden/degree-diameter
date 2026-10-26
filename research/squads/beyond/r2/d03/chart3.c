/* Route-chart search over F_3: A_0 = I, A_1..A_5 in GL_4(F_3), b_0..b_5 in F_3^4 (nonzero).
   Cost = number of singular NB 4-patterns (both sides, 2*750 total). Simulated annealing.
   usage: chart3 seconds seed out */
#include "f3.h"
#include <time.h>
#include <math.h>
static uint64_t rs = 88172645463325252ULL;
static uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int cost(void) {
    int s_cnt = 0;
    for (int s = 0; s < 2; s++) for (int c1 = 0; c1 < 6; c1++) for (int c2 = 0; c2 < 6; c2++) for (int c3 = 0; c3 < 6; c3++) for (int c4 = 0; c4 < 6; c4++) {
        if (c1 == c2 || c2 == c3 || c3 == c4) continue;
        int c[4] = {c1, c2, c3, c4};
        s_cnt += !pattern_ok(s, c);
    }
    return s_cnt;
}
static void randA(mat *M) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) M->a[r][c] = xr() % 3; }
int main(int argc, char **argv) {
    double secs = atof(argv[1]); rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; rs |= 1;
    memset(&A[0], 0, sizeof(mat)); for (int i = 0; i < 4; i++) A[0].a[i][i] = 1;
    for (int t = 1; t < 6; t++) { do randA(&A[t]); while (!inv_mat(&A[t], &Ai[t])); }
    inv_mat(&A[0], &Ai[0]);
    for (int t = 0; t < 6; t++) { do { for (int i = 0; i < 4; i++) bv[t][i] = xr() % 3; } while (!bv[t][0] && !bv[t][1] && !bv[t][2] && !bv[t][3]); }
    int cur = cost(), best = cur; mat bA[6]; int bb[6][4]; memcpy(bA, A, sizeof A); memcpy(bb, bv, sizeof bb);
    time_t t0 = time(NULL); long it = 0; double T0 = 1.5, T1 = 0.05;
    while (1) {
        it++;
        if ((it & 255) == 0) { double el = difftime(time(NULL), t0); if (el >= secs) break; }
        double frac = (double)(it % 200000) / 200000.0; (void)frac;
        double el = difftime(time(NULL), t0); double T = T0 * pow(T1 / T0, el / secs);
        int kind = xr() % 3;
        mat oldA[6]; int oldb[6][4]; memcpy(oldA, A, sizeof A); memcpy(oldb, bv, sizeof bv);
        mat oldAi[6]; memcpy(oldAi, Ai, sizeof Ai);
        if (kind < 2) {
            int t = 1 + xr() % 5; int r = xr() % 4, c = xr() % 4;
            A[t].a[r][c] = xr() % 3;
            if (!inv_mat(&A[t], &Ai[t])) { memcpy(A, oldA, sizeof A); memcpy(Ai, oldAi, sizeof Ai); continue; }
        } else {
            int t = xr() % 6; int i = xr() % 4; bv[t][i] = xr() % 3;
            if (!bv[t][0] && !bv[t][1] && !bv[t][2] && !bv[t][3]) { memcpy(bv, oldb, sizeof bv); continue; }
        }
        int nc = cost();
        if (nc <= cur || (double)(xr() % 1000000) / 1e6 < exp(-(nc - cur) / T)) {
            cur = nc;
            if (cur < best) { best = cur; memcpy(bA, A, sizeof A); memcpy(bb, bv, sizeof bb); }
            if (best == 0) break;
        } else { memcpy(A, oldA, sizeof A); memcpy(Ai, oldAi, sizeof Ai); memcpy(bv, oldb, sizeof bv); }
    }
    memcpy(A, bA, sizeof A); memcpy(bv, bb, sizeof bv); for (int t = 0; t < 6; t++) inv_mat(&A[t], &Ai[t]);
    FILE *f = fopen(argv[3], "w");
    for (int t = 0; t < 6; t++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", A[t].a[r][c]);
        for (int i = 0; i < 4; i++) fprintf(f, "%d ", bv[t][i]); fprintf(f, "\n"); }
    fclose(f);
    printf("best singular patterns %d (of 1500), iterations %ld\n", best, it);
    return 0;
}
