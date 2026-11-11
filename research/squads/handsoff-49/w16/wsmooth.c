/* wsmooth (w16): annealing over voltages of a base multigraph lifted over a group table (groups.py .bin), with a
   SMOOTH walk-count objective. Lift: (u,g) = u*K+g, base edge e=(u,v) with voltage a gives (u,g)~(v,g*a).
   For each root (x,e): c(y) = sum_{t=0..D} (number of walks of length t from root to y), so far <=> c = 0.
   Objective: far + LAM * sum_{roots,y} exp(-c(y)/TAU); far = number of (root, y) with c = 0 (= wl2's cost).
   Usage: wsmooth BASE.wl GROUP.bin D seconds seed LAM TAU OUT
   BASE.wl: first line b, then m lines "u v". Prints RESULT far=... (best far seen, and the far of the best smooth state). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXB 256
#define MAXE 1024
static int b, m, K, D, NV;
static uint16_t *MT; static int *INV;
static int eu[MAXE], ev[MAXE], volt[MAXE], bestv[MAXE];
static int ndart[MAXB], dv[MAXB][64], de[MAXB][64], dsign[MAXB][64];
static double *x, *y, *acc;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int mul(int a, int c) { return MT[(size_t)a * K + c]; }
static void build_darts(void) {
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        dv[u][ndart[u]] = v; de[u][ndart[u]] = e; dsign[u][ndart[u]] = 0; ndart[u]++;
        dv[v][ndart[v]] = u; de[v][ndart[v]] = e; dsign[v][ndart[v]] = 1; ndart[v]++;
    }
}
/* dart from u along e: forward (u = eu) uses volt, backward uses inverse */
static inline int dart_volt(int u, int j) { int a = volt[de[u][j]]; return dsign[u][j] ? INV[a] : a; }
/* returns far count; if smooth != NULL also the smooth sum */
static long evaluate(double tau, double *smooth) {
    long far = 0; double sm = 0;
    for (int root = 0; root < b; root++) {
        memset(x, 0, sizeof(double) * NV); memset(acc, 0, sizeof(double) * NV);
        x[root * K + 0] = 1.0; acc[root * K + 0] = 1.0;
        for (int t = 1; t <= D; t++) {
            memset(y, 0, sizeof(double) * NV);
            for (int u = 0; u < b; u++) for (int g = 0; g < K; g++) { double xv = x[u * K + g]; if (xv == 0.0) continue;
                for (int j = 0; j < ndart[u]; j++) y[dv[u][j] * K + mul(g, dart_volt(u, j))] += xv; }
            for (int i = 0; i < NV; i++) { acc[i] += y[i]; } double *tmp = x; x = y; y = tmp;
        }
        for (int i = 0; i < NV; i++) { if (acc[i] == 0.0) far++; if (smooth) sm += exp(-acc[i] / tau); }
    }
    if (smooth) *smooth = sm;
    return far;
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: wsmooth BASE.wl GROUP.bin D seconds seed LAM TAU OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &b) != 1) return 2;
    m = 0; while (m < MAXE && fscanf(f, "%d %d", &eu[m], &ev[m]) == 2) m++; fclose(f);
    D = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double LAM = atof(argv[6]), TAU = atof(argv[7]); const char *out = argv[8];
    f = fopen(argv[2], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2;
    K = n32; MT = malloc((size_t)K * K * 2); if (fread(MT, 2, (size_t)K * K, f) != (size_t)K * K) return 2; fclose(f);
    INV = malloc(K * sizeof(int));
    for (int g = 0; g < K; g++) { INV[g] = -1; for (int h = 0; h < K; h++) if (MT[(size_t)g * K + h] == 0) { INV[g] = h; break; } }
    NV = b * K; x = malloc(sizeof(double) * NV); y = malloc(sizeof(double) * NV); acc = malloc(sizeof(double) * NV);
    build_darts();
    for (int e = 0; e < m; e++) volt[e] = (int)(rnd() % K);
    /* gauge: tree edges (BFS from 0) get identity; the rest random */
    { int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0; int intree[MAXE] = {0};
      while (h < t) { int u = q[h++]; for (int j = 0; j < ndart[u]; j++) { int v = dv[u][j], e = de[u][j]; if (!seen[v]) { seen[v] = 1; intree[e] = 1; volt[e] = 0; q[t++] = v; } } } }
    double smooth; long far = evaluate(TAU, &smooth);
    double cur = far + LAM * smooth; long bestfar = far; double bestcur = cur; memcpy(bestv, volt, sizeof volt);
    double t0 = now(), T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.02;
    long it = 0; double tl = t0;
    while (bestfar > 0) {
        double el = now() - t0; if (el > secs) break;
        double T = T0 * pow(T1 / T0, el / secs);
        int e = (int)(rnd() % m); int old = volt[e]; int g = (int)(rnd() % K); if (g == old) continue;
        volt[e] = g; it++;
        double sm2; long f2 = evaluate(TAU, &sm2); double nc = f2 + LAM * sm2;
        if (nc <= cur || rnd01() < exp((cur - nc) / T)) { cur = nc; far = f2;
            if (far < bestfar) { bestfar = far; memcpy(bestv, volt, sizeof volt); bestcur = cur; } }
        else volt[e] = old;
        if (now() - tl > 30) { tl = now(); fprintf(stderr, "  t=%.0f it=%ld cur=%.2f far=%ld bestfar=%ld\n", now() - t0, it, cur, far, bestfar); }
    }
    memcpy(volt, bestv, sizeof volt); long fin = evaluate(TAU, NULL);
    printf("RESULT far=%ld cost=%ld n=%d K=%d D=%d it=%ld time=%.1f lam=%g tau=%g\n", fin, fin, b * K, K, D, it, now() - t0, LAM, TAU);
    if (out) { char fn[512]; snprintf(fn, sizeof fn, "%s.volt", out); FILE *o = fopen(fn, "w"); for (int i = 0; i < m; i++) fprintf(o, "%d ", bestv[i]); fprintf(o, "\n"); fclose(o); }
    return 0;
}
