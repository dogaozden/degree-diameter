/* prodopt: Haar graph H(G,S), G = (Z_m0 x|_r0 Z_k0) x (Z_m1 x|_r1 Z_k1), D = 10, |S| = 4, S[0] = identity.
 * Edges (g,A) ~ (s g,B). Cost as in haar_gen3 for even D: number of B-side elements not reached from (e,A)
 * within 9 steps.
 * Usage:
 *   prodopt SOL eval
 *   prodopt SOL one OUT                 exhaustive 1-opt (3 slots x N)
 *   prodopt SOL two KEEP X0 SECS OUT   2-opt: keep slot KEEP (1..3), replace the other two by a pair {x<y};
 *                                       x starts at X0, stops after SECS seconds at a row boundary and prints NEXT x.
 * Any state of cost 0 is written to OUT (same format as haar_gen3 solution files) and the program exits.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define DD 10
#define MAXS 8
#define HIST 64

static int M[2] = {11, 19}, K[2] = {5, 6}; static long long RR[2] = {3, 8};
static long long PW[2][16];
static int N, O2;
static uint16_t *MUL, *INV;
static uint32_t *gA, *gB, gen = 0;
static uint16_t *fA, *fB;

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int gmul(int i, int x, int y) {
    int kk = K[i], mm = M[i]; int a = x / kk, j = x % kk, b = y / kk, l = y % kk;
    int c = (int)((a + PW[i][j] * b) % mm);
    return c * kk + (j + l) % kk;
}
static int mulx(int x, int y) { return gmul(0, x / O2, y / O2) * O2 + gmul(1, x % O2, y % O2); }

#define MU(x, y) MUL[(size_t)(x) * N + (y)]

/* number of B-side elements NOT within 9 of (e,A) */
static int cost_of(const int *S, int d) {
    gen++;
    int Si[MAXS];
    for (int t = 0; t < d; t++) { int s = S[t]; int r = 0; (void)r; Si[t] = INV[s]; }
    int nfa = 1; fA[0] = 0; gA[0] = gen;
    long long cntB = 0; int nfb = 0;
    for (int lev = 1; lev <= DD - 1; lev++) {
        if (lev & 1) {                       /* A -> B : h = s g */
            nfb = 0;
            for (int i = 0; i < nfa; i++) {
                int g = fA[i];
                for (int t = 0; t < d; t++) {
                    int h = MU(S[t], g);
                    if (gB[h] != gen) { gB[h] = gen; fB[nfb++] = (uint16_t)h; }
                }
            }
            cntB += nfb;
        } else {                             /* B -> A : g = s^-1 h */
            nfa = 0;
            for (int i = 0; i < nfb; i++) {
                int h = fB[i];
                for (int t = 0; t < d; t++) {
                    int g = MU(Si[t], h);
                    if (gA[g] != gen) { gA[g] = gen; fA[nfa++] = (uint16_t)g; }
                }
            }
        }
    }
    return (int)(N - cntB);
}

static int readS(const char *fn, int *S) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    char line[512]; if (!fgets(line, sizeof line, f)) exit(1);
    int d = 0, D = 0; sscanf(line, "%d %d", &d, &D);
    for (int i = 0; i < d; i++) { if (!fgets(line, sizeof line, f)) exit(1); sscanf(line, "%d", &S[i]); }
    fclose(f);
    if (D != DD) { fprintf(stderr, "D=%d not supported\n", D); exit(1); }
    return d;
}
static void desc(int x, char *buf) {
    int x1 = x / O2, x2 = x % O2;
    sprintf(buf, "prod[meta(a=%d,j=%d);meta(a=%d,j=%d)]", x1 / K[0], x1 % K[0], x2 / K[1], x2 % K[1]);
}
static void writeS(const char *fn, const int *S, int d, int cost) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d %d prod meta %d %d %lld meta %d %d %lld n 1 N %d cost %d\n", d, DD, M[0], K[0], RR[0], M[1], K[1], RR[1], N, cost);
    for (int t = 0; t < d; t++) { char b[200]; desc(S[t], b); fprintf(f, "%d %s z=0\n", S[t], b); }
    fclose(f);
}

static void init_group(void) {
    for (int i = 0; i < 2; i++) {
        PW[i][0] = 1 % M[i];
        for (int j = 1; j < K[i]; j++) PW[i][j] = PW[i][j - 1] * RR[i] % M[i];
        if (PW[i][K[i] - 1] * RR[i] % M[i] != 1 % M[i]) { fprintf(stderr, "r^k != 1\n"); exit(2); }
    }
    O2 = M[1] * K[1]; N = (M[0] * K[0]) * O2;
    MUL = malloc(2 * (size_t)N * N); INV = malloc(2 * (size_t)N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) MU(x, y) = (uint16_t)mulx(x, y);
    /* checks: identity 0, rows are permutations (sampled), inverses, associativity on samples */
    for (int x = 0; x < N; x++) {
        int found = -1;
        for (int y = 0; y < N; y++) if (MU(x, y) == 0) { found = y; break; }
        if (found < 0) { fprintf(stderr, "no inverse for %d\n", x); exit(3); }
        INV[x] = (uint16_t)found;
    }
    for (int x = 0; x < N; x += 97) for (int y = 0; y < N; y += 89) {
        int seen = 0; for (int z = 0; z < N; z++) if (MU(x, z) == y) seen++;
        if (seen != 1) { fprintf(stderr, "row %d not a permutation\n", x); exit(3); }
    }
    unsigned long long s = 12345;
    for (int it = 0; it < 200000; it++) {
        s = s * 6364136223846793005ULL + 1442695040888963407ULL; int a = (int)((s >> 20) % N);
        s = s * 6364136223846793005ULL + 1442695040888963407ULL; int b = (int)((s >> 20) % N);
        s = s * 6364136223846793005ULL + 1442695040888963407ULL; int c = (int)((s >> 20) % N);
        if (MU(MU(a, b), c) != MU(a, MU(b, c))) { fprintf(stderr, "not associative\n"); exit(3); }
    }
    gA = calloc(N, 4); gB = calloc(N, 4); fA = malloc(2 * (size_t)N); fB = malloc(2 * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: prodopt SOL eval|one OUT|two KEEP X0 SECS OUT\n"); return 1; }
    double t0 = now();
    init_group();
    int S[MAXS]; int d = readS(argv[1], S);
    const char *mode = argv[2];
    fprintf(stderr, "N=%d init %.2fs\n", N, now() - t0);

    if (!strcmp(mode, "eval")) {
        printf("cost %d\n", cost_of(S, d));
        return 0;
    }
    if (!strcmp(mode, "one")) {
        const char *out = argc > 3 ? argv[3] : NULL;
        int c0 = cost_of(S, d);
        printf("start cost %d\n", c0);
        int best = 1 << 30; long long hist[HIST] = {0}; int bestS[MAXS]; memcpy(bestS, S, sizeof S);
        long long nev = 0;
        for (int slot = 1; slot < d; slot++) {
            int T[MAXS]; memcpy(T, S, sizeof T);
            for (int x = 1; x < N; x++) {
                int dup = 0; for (int t = 0; t < d; t++) if (t != slot && S[t] == x) dup = 1;
                if (dup) continue;
                T[slot] = x; int c = cost_of(T, d); nev++;
                hist[c < HIST ? c : HIST - 1]++;
                if (c < best) { best = c; memcpy(bestS, T, sizeof T); }
                if (c == 0) { char b[300]; sprintf(b, "%s", out ? out : "cost0.sol"); writeS(b, T, d, 0); printf("COST0 slot %d x %d\n", slot, x); return 0; }
            }
        }
        printf("1-opt evals %lld best %d (start %d) time %.1f\n", nev, best, c0, now() - t0);
        for (int c = 0; c < 12; c++) if (hist[c]) printf("  cost %d: %lld\n", c, hist[c]);
        if (out) writeS(out, bestS, d, best);
        return 0;
    }
    if (!strcmp(mode, "two")) {
        int keep = atoi(argv[3]), x0 = atoi(argv[4]); double secs = atof(argv[5]);
        const char *out = argc > 6 ? argv[6] : "two_out.sol";
        if (keep < 1 || keep >= d) { fprintf(stderr, "bad KEEP\n"); return 1; }
        int z = S[keep];
        int best = 1 << 30; long long nev = 0; long long hist[HIST] = {0};
        int bestS[MAXS]; memcpy(bestS, S, sizeof bestS);
        int x; double tstart = now();
        for (x = x0; x < N; x++) {
            if (x == 0 || x == z) continue;
            for (int y = x + 1; y < N; y++) {
                if (y == z || y == 0) continue;
                int T[MAXS] = {0, 0, 0, 0}; T[0] = 0; int u = 1;
                /* S = {e, z, x, y} with z in the kept slot */
                T[u++] = z; T[u++] = x; T[u++] = y;
                int c = cost_of(T, d); nev++;
                hist[c < HIST ? c : HIST - 1]++;
                if (c < best) { best = c; memcpy(bestS, T, sizeof T); printf("best %d at x=%d y=%d\n", c, x, y); fflush(stdout); }
                if (c == 0) { writeS(out, T, d, 0); printf("COST0 keep %d x %d y %d\n", keep, x, y); return 0; }
            }
            if (now() - tstart > secs) { x++; break; }
        }
        printf("KEEP %d z=%d evals %lld best %d rows-to x=%d time %.1f\n", keep, z, nev, best, x, now() - t0);
        for (int c = 0; c < 12; c++) if (hist[c]) printf("  cost %d: %lld\n", c, hist[c]);
        printf("NEXT %d\n", x);
        writeS(out, bestS, d, best);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 1;
}
