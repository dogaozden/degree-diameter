/* clq_fib.c (card c2, squad round 2): max clique in the coset graph G_u of the line fibration of H(11).
   Vertices: offsets (0,b,c,e,f) (a = 0), i.e. F_11^4.  t ~ s iff Q(t-s+nu*u) != 0 for all nu in F_11,
   Q(a,b,c,e,f) = c^2 - a*e - b*f  (u[0] must be 1).  Max clique by a multi-neighbourhood tabu search (ADD / SWAP /
   DROP) with restarts, CPU-time limited.
   usage: clq_fib "u0 u1 u2 u3 u4" SEED CPU_SECONDS(<=600) OUT_OFFSETS [STALL] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NV 14641
#define WORDS ((NV + 63) / 64)

static uint64_t adjb[(size_t)NV * WORDS];
static int okw[NV];
static int u[5];
static int dig[NV][4];

static int Qf(int a, int b, int c, int e, int f) {
    int r = (c * c - a * e - b * f) % 11;
    if (r < 0) r += 11;
    return r;
}
static int enc(int b, int c, int e, int f) { return ((b * 11 + c) * 11 + e) * 11 + f; }

static void build(void) {
    for (int w = 0; w < NV; w++) {
        int b = dig[w][0], c = dig[w][1], e = dig[w][2], f = dig[w][3];
        int good = (w != 0);
        for (int nu = 0; nu < 11 && good; nu++) {
            int A = (nu * u[0]) % 11, B = (b + nu * u[1]) % 11, C = (c + nu * u[2]) % 11;
            int E = (e + nu * u[3]) % 11, F = (f + nu * u[4]) % 11;
            if (Qf(A, B, C, E, F) == 0) good = 0;
        }
        okw[w] = good;
    }
    for (int v1 = 0; v1 < NV; v1++)
        for (int v2 = 0; v2 < NV; v2++) {
            if (v1 == v2) continue;
            int d0 = (dig[v1][0] - dig[v2][0] + 11) % 11, d1 = (dig[v1][1] - dig[v2][1] + 11) % 11;
            int d2 = (dig[v1][2] - dig[v2][2] + 11) % 11, d3 = (dig[v1][3] - dig[v2][3] + 11) % 11;
            if (okw[enc(d0, d1, d2, d3)]) adjb[(size_t)v1 * WORDS + (v2 >> 6)] |= 1ULL << (v2 & 63);
        }
}

static int inC[NV], Cl[NV], csz, posC[NV], miss[NV];
static long tabu_until[NV];
static int bestC[NV], bestsz = 0;
static int PA[NV], OM[NV];

static inline int isadj(int x, int y) { return (adjb[(size_t)x * WORDS + (y >> 6)] >> (y & 63)) & 1; }

static void addv(int x) {
    inC[x] = 1; posC[x] = csz; Cl[csz++] = x;
    const uint64_t *row = adjb + (size_t)x * WORDS;
    for (int v = 0; v < NV; v++)
        if (v != x && !((row[v >> 6] >> (v & 63)) & 1)) miss[v]++;
}
static void remv(int x) {
    inC[x] = 0; int p = posC[x]; Cl[p] = Cl[--csz]; posC[Cl[p]] = p;
    const uint64_t *row = adjb + (size_t)x * WORDS;
    for (int v = 0; v < NV; v++)
        if (v != x && !((row[v >> 6] >> (v & 63)) & 1)) miss[v]--;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: clq_fib \"u0 u1 u2 u3 u4\" SEED CPU_SECONDS OUT [STALL]\n"); return 1; }
    sscanf(argv[1], "%d %d %d %d %d", &u[0], &u[1], &u[2], &u[3], &u[4]);
    for (int k = 0; k < 5; k++) u[k] = ((u[k] % 11) + 11) % 11;
    if (u[0] != 1) { fprintf(stderr, "need u0 = 1\n"); return 1; }
    unsigned seed = (unsigned)atoi(argv[2]);
    double tlim = atof(argv[3]);
    if (tlim > 600) tlim = 600;
    long STALL = argc > 5 ? atol(argv[5]) : 20000;
    for (int v = 0; v < NV; v++) { dig[v][3] = v % 11; dig[v][2] = (v / 11) % 11; dig[v][1] = (v / 121) % 11; dig[v][0] = v / 1331; }
    build();
    int deg = 0; for (int k = 0; k < WORDS; k++) deg += __builtin_popcountll(adjb[k]);
    printf("u = %d %d %d %d %d: degree of vertex 0 = %d\n", u[0], u[1], u[2], u[3], u[4], 0);
    { int d0 = 0; for (int k = 0; k < WORDS; k++) d0 += __builtin_popcountll(adjb[k]); printf("degree(0) = %d (total edge-ends/NV = %.1f)\n", d0, (double)deg / NV); }
    srand(seed);
    clock_t t0 = clock();
    long it = 0, restarts = 0;
    int stop = 0;
    while (!stop) {
        restarts++;
        memset(inC, 0, sizeof inC); memset(miss, 0, sizeof miss); memset(tabu_until, 0, sizeof tabu_until); csz = 0;
        addv(rand() % NV);
        int lb = csz; long stall = 0;
        while (stall < STALL) {
            it++;
            if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tlim) { stop = 1; break; }
            int nPA = 0, nOM = 0;
            for (int v = 0; v < NV; v++) {
                if (inC[v]) continue;
                if (miss[v] == 0) { if (tabu_until[v] <= it || csz + 1 > bestsz) PA[nPA++] = v; }
                else if (miss[v] == 1 && tabu_until[v] <= it) OM[nOM++] = v;
            }
            if (nPA) {
                addv(PA[rand() % nPA]);
            } else if (nOM) {
                int x = OM[rand() % nOM], y = -1;
                for (int k = 0; k < csz; k++) if (!isadj(Cl[k], x)) { y = Cl[k]; break; }
                remv(y); tabu_until[y] = it + 7 + rand() % 10;
                addv(x);
            } else if (csz > 0) {
                int y = Cl[rand() % csz];
                remv(y); tabu_until[y] = it + 7 + rand() % 10;
            }
            if (csz > bestsz) {
                bestsz = csz; memcpy(bestC, Cl, sizeof(int) * csz);
                printf("  size %d at iter %ld, restart %ld, cpu %.1f s\n", bestsz, it, restarts, (double)(clock() - t0) / CLOCKS_PER_SEC);
                fflush(stdout);
            }
            if (csz > lb) { lb = csz; stall = 0; } else stall++;
        }
    }
    printf("done: best clique (lines) = %d, iterations %ld, restarts %ld, cpu %.1f s\n", bestsz, it, restarts,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    /* verify */
    int ok = 1;
    for (int i = 0; i < bestsz; i++) for (int j = i + 1; j < bestsz; j++) if (!isadj(bestC[i], bestC[j])) ok = 0;
    printf("clique verified: %s\n", ok ? "yes" : "NO");
    FILE *f = fopen(argv[4], "w");
    fprintf(f, "# clique of %d offsets (a=0), direction %s\n", bestsz, argv[1]);
    for (int i = 0; i < bestsz; i++) { int v = bestC[i]; fprintf(f, "0 %d %d %d %d\n", dig[v][0], dig[v][1], dig[v][2], dig[v][3]); }
    fclose(f);
    return 0;
}
