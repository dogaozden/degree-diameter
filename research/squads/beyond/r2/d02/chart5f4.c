/* 5-letter route chart over F4. Cost = 4 * (#singular nonbacktracking 4-words, both start sides, of 640)
   + (#singular backtracking 4-words, both sides). usage: chart5f4 seconds seed out.txt */
#include "gf4.h"
static int nbcost(int *sing_nb, int *sing_bt) {
    int w[4]; int nb = 0, bt = 0; (void)bt;
    for (int s0 = 0; s0 < 2; s0++)
    for (w[0] = 0; w[0] < 5; w[0]++) for (w[1] = 0; w[1] < 5; w[1]++) for (w[2] = 0; w[2] < 5; w[2]++) for (w[3] = 0; w[3] < 5; w[3]++) {
        int isnb = (w[0] != w[1]) && (w[1] != w[2]) && (w[2] != w[3]);
        if (!isnb) continue; if (!word_full(w, 4, s0)) nb++;
    }
    *sing_nb = nb; *sing_bt = bt; *sing_bt = 0; return nb;
}
static int rand_inv(M4 *M) { M4 R; do { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) M->a[r][c] = xr() & 3; } while (!inv4(M, &R)); return 0; }
int main(int argc, char **argv) {
    double secs = atof(argv[1]); rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; const char *out = argv[3];
    clock_t t0 = clock(); int best = 1 << 30; long evals = 0;
    M4 bA[5]; V4 bb[5];
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > 0) {
        for (int t = 0; t < 5; t++) { rand_inv(&Ach[t]); inv4(&Ach[t], &Aich[t]); for (int r = 0; r < 4; r++) bch[t].v[r] = xr() & 3; }
        int sn, sb; int c = nbcost(&sn, &sb);
        for (long it = 0; it < 200000 && c > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs; it++) {
            double T = 3.0 * (1.0 - it / 200000.0) + 0.05;
            int t = xr() % 5; M4 oA = Ach[t], oAi = Aich[t]; V4 ob = bch[t]; int isA = xr() & 1;
            if (isA) { int r = xr() & 3, cc = xr() & 3; Ach[t].a[r][cc] = xr() & 3; if (!inv4(&Ach[t], &Aich[t])) { Ach[t] = oA; Aich[t] = oAi; continue; } }
            else { bch[t].v[xr() & 3] = xr() & 3; }
            int c2 = nbcost(&sn, &sb); evals++;
            double u = (xr() >> 11) * (1.0 / 9007199254740992.0);
            if (c2 <= c || u < __builtin_exp(-(c2 - c) / T)) { c = c2; }
            else { Ach[t] = oA; Aich[t] = oAi; bch[t] = ob; }
            if (c < best) { best = c; memcpy(bA, Ach, sizeof Ach); memcpy(bb, bch, sizeof bch); }
            if (c == 0) break;
        }
        printf("restart done: best so far %d (nb %d bt %d at cost of current) evals %ld\n", best, sn, sb, evals); fflush(stdout);
    }
    memcpy(Ach, bA, sizeof Ach); memcpy(bch, bb, sizeof bch); for (int t = 0; t < 5; t++) inv4(&Ach[t], &Aich[t]);
    int sn, sb; nbcost(&sn, &sb);
    printf("FINAL cost %d singular NB4 %d singular backtracking4 %d evals %ld\n", best, sn, sb, evals);
    write_chart(out); printf("written %s\n", out);
    return 0;
}
