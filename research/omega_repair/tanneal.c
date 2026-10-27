/* tanneal.c: simulated annealing over the twists lam_c (c >= 1; lam_0 = id) of twist.c, cost = exact number of far
   (hub, copy vertex) pairs from the route formulas.  Move: lam_c <- g lam_c or lam_c g, g from a generator file.
   usage: tanneal hex.txt gens.bin TYPES iters T0 T1 seed out.bin [init.bin] [tstep]  */
#define TWIST_NO_MAIN
#include "twist.c"
#include <math.h>
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void save(const char *path) {
    FILE *f = fopen(path, "wb"); int hdr[2] = {C, n}; fwrite(hdr, 4, 2, f);
    for (int c = 0; c < C; c++) { fwrite(lamP + c * n, 4, n, f); fwrite(lamL + c * n, 4, n, f); } fclose(f);
}
int main(int argc, char **argv) {
    load_hex(argv[1]); strcpy(types, argv[3]); A = strlen(types); C = 5 * A; wiring();
    long iters = atol(argv[4]); double T0 = atof(argv[5]), T1 = atof(argv[6]); rs ^= atol(argv[7]) * 2654435761ULL;
    if (argc > 10) tstep = atoi(argv[10]);
    FILE *f = fopen(argv[2], "rb"); int hdr[2]; if (fread(hdr, 4, 2, f) != 2 || hdr[1] != n) { fprintf(stderr, "gens\n"); return 1; }
    int G = hdr[0]; int *gP = malloc(sizeof(int) * G * n), *gL = malloc(sizeof(int) * G * n);
    for (int i = 0; i < G; i++) { if (fread(gP + i * n, 4, n, f) != (size_t)n || fread(gL + i * n, 4, n, f) != (size_t)n) return 1; }
    fclose(f);
    if (argc > 9 && strcmp(argv[9], "-")) load_twists(argv[9]);
    else { lamP = malloc(sizeof(int) * C * n); lamL = malloc(sizeof(int) * C * n); ilamP = malloc(sizeof(int) * C * n); ilamL = malloc(sizeof(int) * C * n);
        for (int c = 0; c < C; c++) for (int x = 0; x < n; x++) lamP[c * n + x] = lamL[c * n + x] = ilamP[c * n + x] = ilamL[c * n + x] = x; }
    balls(); routes();
    long cur = formula(0), best = cur; save(argv[8]);
    printf("start cost %ld\n", cur); fflush(stdout);
    int *oP = malloc(sizeof(int) * n), *oL = malloc(sizeof(int) * n);
    for (long it = 0; it < iters && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int c = 1 + rnd() % (C - 1), g = rnd() % G, left = rnd() & 1;
        memcpy(oP, lamP + c * n, 4 * n); memcpy(oL, lamL + c * n, 4 * n);
        for (int x = 0; x < n; x++) {
            lamP[c * n + x] = left ? gP[g * n + oP[x]] : oP[gP[g * n + x]];
            lamL[c * n + x] = left ? gL[g * n + oL[x]] : oL[gL[g * n + x]];
        }
        for (int x = 0; x < n; x++) { ilamP[c * n + lamP[c * n + x]] = x; ilamL[c * n + lamL[c * n + x]] = x; }
        invalidate(c);
        long nc = formula(0);
        if (nc <= cur || exp((cur - nc) / T) > (rnd() % 1000000) / 1e6) {
            cur = nc;
            if (cur < best) { best = cur; save(argv[8]); }
        } else {
            memcpy(lamP + c * n, oP, 4 * n); memcpy(lamL + c * n, oL, 4 * n);
            for (int x = 0; x < n; x++) { ilamP[c * n + lamP[c * n + x]] = x; ilamL[c * n + lamL[c * n + x]] = x; }
            invalidate(c);
        }
        if (it % 200 == 0) { printf("it %ld T %.1f cur %ld best %ld\n", it, T, cur, best); fflush(stdout); }
    }
    printf("RESULT best %ld\n", best);
    return 0;
}
