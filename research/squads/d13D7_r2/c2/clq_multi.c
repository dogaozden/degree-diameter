/* clq_multi.c (card c2, squad round 2): max clique over lines in SEVERAL directions u_1..u_m of H(11)'s affine chart.
   Vertices (i,k): the affine line t + F11*u_i, t the canonical representative with t[piv_i] = 0 (k = 4 free digits).
   Same direction: adjacent iff Q(d + nu*u_i) != 0 for all nu (d = difference of representatives).
   Different directions i<j: adjacent iff (1) span(u_i,u_j) is degenerate: P(u_i,u_j)^2 = 4 Q(u_i) Q(u_j), and with
   r = P(u_i,u_j)/(2Q(u_i)), rho = u_j - r u_i (the radical), (2) P(d,rho) = 0, (3) D = A^2 - 4 Q(u_i) C is a nonzero
   non-square, A = P(d,u_i), C = Q(d).  Q(a,b,c,e,f) = c^2 - ae - bf, P its polar form (P(x,x) = 2Q(x)).
   Max clique by multi-neighbourhood tabu search with restarts (CPU-limited).
   usage: clq_multi DIRFILE SEED CPU_SECONDS(<=600) OUT [STALL]   (DIRFILE: one "u0 u1 u2 u3 u4" per line) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define Q11 11
#define NF 14641
#define MAXM 4
static int m, piv[MAXM], dirv[MAXM][5];
static int n, WORDS;
static uint64_t *adjb;
static int (*TV)[5];            /* full representative of vertex */
static int *okS[MAXM];         /* same-direction adjacency table over free digits, size NF */
static int *Cl, *posC, *inC, *miss, csz, *PA, *OM;
static long *tabu;
static int *bestC, bestsz = 0;
static int rho[MAXM][MAXM][5], rhoOK[MAXM][MAXM];

static int md(int x) { x %= Q11; return x < 0 ? x + Q11 : x; }
static int Qf(const int *x) { return md(x[2] * x[2] - x[0] * x[3] - x[1] * x[4]); }
static int Pf(const int *x, const int *y) { return md(2 * x[2] * y[2] - (x[0] * y[3] + y[0] * x[3]) - (x[1] * y[4] + y[1] * x[4])); }
static int sq[Q11];

static void free_to_full(int i, int k, int *out) {  /* k = 4 base-11 digits in coordinate order skipping piv_i */
    int dg[4]; int kk = k; for (int t = 0; t < 4; t++) { dg[t] = kk % 11; kk /= 11; }
    int c = 0;
    for (int t = 0; t < 5; t++) { if (t == piv[i]) out[t] = 0; else out[t] = dg[c++]; }
}
static int full_to_free(int i, const int *x) {  /* x[piv_i] assumed 0 */
    int k = 0, pw = 1;
    for (int t = 0; t < 5; t++) { if (t == piv[i]) continue; k += x[t] * pw; pw *= 11; }
    return k;
}
static inline int isadj(int x, int y) { return (adjb[(size_t)x * WORDS + (y >> 6)] >> (y & 63)) & 1; }
static void addv(int x) {
    inC[x] = 1; posC[x] = csz; Cl[csz++] = x;
    const uint64_t *row = adjb + (size_t)x * WORDS;
    for (int v = 0; v < n; v++) if (v != x && !((row[v >> 6] >> (v & 63)) & 1)) miss[v]++;
}
static void remv(int x) {
    inC[x] = 0; int p = posC[x]; Cl[p] = Cl[--csz]; posC[Cl[p]] = p;
    const uint64_t *row = adjb + (size_t)x * WORDS;
    for (int v = 0; v < n; v++) if (v != x && !((row[v >> 6] >> (v & 63)) & 1)) miss[v]--;
}
static void setbit(int x, int y) { adjb[(size_t)x * WORDS + (y >> 6)] |= 1ULL << (y & 63); }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: clq_multi DIRFILE SEED CPU OUT [STALL]\n"); return 1; }
    for (int x = 1; x < Q11; x++) for (int y = 1; y < Q11; y++) if (x * y % Q11 == 1) sq[x] = 0;
    for (int x = 1; x < Q11; x++) sq[x * x % Q11] = 1;   /* sq[v]=1 iff v nonzero square */
    FILE *df = fopen(argv[1], "r"); m = 0;
    while (m < MAXM && fscanf(df, "%d %d %d %d %d", &dirv[m][0], &dirv[m][1], &dirv[m][2], &dirv[m][3], &dirv[m][4]) == 5) {
        for (int t = 0; t < 5; t++) dirv[m][t] = md(dirv[m][t]);
        int p = 0; while (p < 5 && dirv[m][p] == 0) p++;
        int inv = 1; for (int s = 1; s < Q11; s++) if (dirv[m][p] * s % Q11 == 1) inv = s;
        for (int t = 0; t < 5; t++) dirv[m][t] = dirv[m][t] * inv % Q11;
        piv[m] = p; m++;
    }
    fclose(df);
    unsigned seed = (unsigned)atoi(argv[2]); double tlim = atof(argv[3]); if (tlim > 600) tlim = 600;
    long STALL = argc > 5 ? atol(argv[5]) : 20000;
    n = m * NF; WORDS = (n + 63) / 64;
    for (int i = 0; i < m; i++) printf("dir %d: %d %d %d %d %d  pivot %d  Q=%d (%s)\n", i, dirv[i][0], dirv[i][1], dirv[i][2], dirv[i][3], dirv[i][4], piv[i], Qf(dirv[i]), sq[Qf(dirv[i])] ? "square" : "nonsquare");
    /* tangency and rho */
    int tang[MAXM][MAXM];
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) {
        tang[i][j] = 0; rhoOK[i][j] = 0; if (i == j) continue;
        int Pij = Pf(dirv[i], dirv[j]), Qi = Qf(dirv[i]), Qj = Qf(dirv[j]);
        if (Qi == 0 || Qj == 0) continue;
        if (Pij * Pij % Q11 != (4 * Qi * Qj) % Q11) continue;
        tang[i][j] = 1;
        int inv2Qi = 0; for (int s = 1; s < Q11; s++) if ((2 * Qi * s) % Q11 == 1) inv2Qi = s;
        int r = Pij * inv2Qi % Q11;
        for (int t = 0; t < 5; t++) rho[i][j][t] = md(dirv[j][t] - r * dirv[i][t]);
        rhoOK[i][j] = (Qf(rho[i][j]) == 0);
    }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (i != j) printf("tangent(%d,%d)=%d rhoOK=%d\n", i, j, tang[i][j], rhoOK[i][j]);
    /* same-direction tables */
    for (int i = 0; i < m; i++) {
        okS[i] = calloc(NF, sizeof(int));
        for (int k = 0; k < NF; k++) {
            int w[5]; free_to_full(i, k, w);
            int good = (k != 0);
            for (int nu = 0; nu < Q11 && good; nu++) {
                int x[5]; for (int t = 0; t < 5; t++) x[t] = md(w[t] + nu * dirv[i][t]);
                if (Qf(x) == 0) good = 0;
            }
            okS[i][k] = good;
        }
        int cnt = 0; for (int k = 0; k < NF; k++) cnt += okS[i][k];
        printf("direction %d: same-direction degree %d\n", i, cnt);
    }
    TV = malloc(sizeof(int[5]) * (size_t)n);
    for (int i = 0; i < m; i++) for (int k = 0; k < NF; k++) free_to_full(i, k, TV[i * NF + k]);
    adjb = calloc((size_t)n * WORDS, sizeof(uint64_t));
    if (!adjb) { fprintf(stderr, "no memory\n"); return 1; }
    for (int x = 0; x < n; x++) {
        int i = x / NF, k = x % NF;
        for (int y = x + 1; y < n; y++) {
            int j = y / NF, l = y % NF, ok = 0;
            if (i == j) {
                /* difference of free digits */
                int d[5]; for (int t = 0; t < 5; t++) d[t] = md(TV[x][t] - TV[y][t]);
                int kk = full_to_free(i, d); ok = okS[i][kk];
            } else {
                int a = i < j ? i : j, b = i < j ? j : i;  /* use ordering a<b */
                const int *ua = dirv[a]; const int *ub_ = dirv[b];
                (void)ub_;
                if (!tang[a][b] || !rhoOK[a][b]) ok = 0;
                else {
                    int d[5];
                    const int *X = (i == a) ? TV[x] : TV[y], *Y = (i == a) ? TV[y] : TV[x];
                    for (int t = 0; t < 5; t++) d[t] = md(X[t] - Y[t]);
                    if (Pf(d, rho[a][b]) == 0) {
                        int A = Pf(d, ua), C = Qf(d);
                        int D = md(A * A - 4 * Qf(ua) * C);
                        ok = (D != 0) && !sq[D];
                    }
                }
            }
            if (ok) { setbit(x, y); setbit(y, x); }
        }
    }
    /* degrees */
    long dsum = 0; for (int x = 0; x < n; x++) { for (int w = 0; w < WORDS; w++) dsum += __builtin_popcountll(adjb[(size_t)x * WORDS + w]) * 0; }
    { long e = 0; for (size_t t = 0; t < (size_t)n * WORDS; t++) e += __builtin_popcountll(adjb[t]); printf("graph: %d vertices, average degree %.1f\n", n, (double)e / n); }
    (void)dsum;
    Cl = malloc(sizeof(int) * n); posC = malloc(sizeof(int) * n); inC = malloc(sizeof(int) * n); miss = malloc(sizeof(int) * n);
    PA = malloc(sizeof(int) * n); OM = malloc(sizeof(int) * n); tabu = malloc(sizeof(long) * n); bestC = malloc(sizeof(int) * n);
    srand(seed);
    clock_t t0 = clock(); long it = 0, restarts = 0; int stop = 0;
    while (!stop) {
        restarts++;
        memset(inC, 0, sizeof(int) * n); memset(miss, 0, sizeof(int) * n); memset(tabu, 0, sizeof(long) * n); csz = 0;
        addv(rand() % n);
        int lb = csz; long stall = 0;
        while (stall < STALL) {
            it++;
            if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tlim) { stop = 1; break; }
            int nPA = 0, nOM = 0;
            for (int v = 0; v < n; v++) {
                if (inC[v]) continue;
                if (miss[v] == 0) { if (tabu[v] <= it || csz + 1 > bestsz) PA[nPA++] = v; }
                else if (miss[v] == 1 && tabu[v] <= it) OM[nOM++] = v;
            }
            if (nPA) addv(PA[rand() % nPA]);
            else if (nOM) {
                int x = OM[rand() % nOM], y = -1;
                for (int k = 0; k < csz; k++) if (!isadj(Cl[k], x)) { y = Cl[k]; break; }
                remv(y); tabu[y] = it + 7 + rand() % 10; addv(x);
            } else if (csz > 0) { int y = Cl[rand() % csz]; remv(y); tabu[y] = it + 7 + rand() % 10; }
            if (csz > bestsz) {
                bestsz = csz; memcpy(bestC, Cl, sizeof(int) * csz);
                printf("  size %d at iter %ld, restart %ld, cpu %.1f s\n", bestsz, it, restarts, (double)(clock() - t0) / CLOCKS_PER_SEC);
                fflush(stdout);
            }
            if (csz > lb) { lb = csz; stall = 0; } else stall++;
        }
    }
    printf("done: best clique = %d lines, iterations %ld, restarts %ld, cpu %.1f s\n", bestsz, it, restarts,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    int ok = 1;
    for (int i = 0; i < bestsz; i++) for (int j = i + 1; j < bestsz; j++) if (!isadj(bestC[i], bestC[j])) ok = 0;
    printf("clique verified: %s\n", ok ? "yes" : "NO");
    FILE *f = fopen(argv[4], "w");
    fprintf(f, "# %d lines: direction index then offset t (t[piv]=0); directions from %s\n", bestsz, argv[1]);
    for (int i = 0; i < bestsz; i++) { int v = bestC[i]; fprintf(f, "%d %d %d %d %d %d\n", v / NF, TV[v][0], TV[v][1], TV[v][2], TV[v][3], TV[v][4]); }
    fclose(f);
    return 0;
}
