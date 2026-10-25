/* wsa.c: weighted maximum independent set by simulated annealing with restarts from the best set.
   graph file: "n" then per vertex: "w deg nbr1 ... nbr_deg"  (weights are positive integers)
   usage: wsa GRAPH OUT CPU_SECONDS SEED [T0 T1 STEPS]
   OUT receives the best set (vertex ids, one per line) whenever it improves. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int n, *w, *deg, **nb;
char *inS;
long long cur;
void setin(int v) { inS[v] = 1; cur += w[v]; }
void setout(int v) { inS[v] = 0; cur -= w[v]; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: wsa GRAPH OUT CPU SEED [T0 T1 STEPS]\n"); return 1; }
    double budget = atof(argv[3]);
    rs = 0x243F6A8885A308D3ULL ^ ((uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL); if (!rs) rs = 1;
    double T0 = argc > 5 ? atof(argv[5]) : 4.0, T1 = argc > 6 ? atof(argv[6]) : 0.15;
    long long steps = argc > 7 ? atoll(argv[7]) : 2000000;
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &n) != 1) return 1;
    w = malloc(sizeof(int) * n); deg = malloc(sizeof(int) * n); nb = malloc(sizeof(int *) * n);
    for (int i = 0; i < n; i++) {
        if (fscanf(f, "%d %d", &w[i], &deg[i]) != 2) return 1;
        nb[i] = malloc(sizeof(int) * (deg[i] + 1));
        for (int k = 0; k < deg[i]; k++) if (fscanf(f, "%d", &nb[i][k]) != 1) return 1;
    }
    fclose(f);
    inS = calloc(n, 1);
    char *bestS = calloc(n, 1); long long bestW = 0; char *tmp = calloc(n, 1);
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long long restarts = 0;
    cur = 0;
    int *conf = malloc(sizeof(int) * n);
    /* start from empty set; anneal; afterwards restart from best with a perturbation */
    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - t0;
        if (el > budget) break;
        restarts++;
        if (restarts > 1 && (rnd() & 1)) {
            /* restart from best set */
            for (int i = 0; i < n; i++) if (inS[i]) setout(i);
            for (int i = 0; i < n; i++) if (bestS[i]) setin(i);
        } else {
            for (int i = 0; i < n; i++) if (inS[i]) setout(i);
        }
        for (long long it = 0; it < steps; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)steps);
            int v = (int)(rnd() % (uint64_t)n);
            if (inS[v]) {
                /* remove with Boltzmann probability */
                if (urand() < exp(-w[v] / T)) setout(v);
            } else {
                long long cw = 0; int nc = 0;
                for (int k = 0; k < deg[v]; k++) { int u = nb[v][k]; if (inS[u]) { conf[nc++] = u; cw += w[u]; } }
                long long delta = (long long)w[v] - cw;
                if (delta >= 0 || urand() < exp((double)delta / T)) {
                    for (int k = 0; k < nc; k++) setout(conf[k]);
                    setin(v);
                    if (cur > bestW) {
                        bestW = cur; memcpy(bestS, inS, n);
                    }
                }
            }
        }
        if (cur > bestW) { bestW = cur; memcpy(bestS, inS, n); }
        /* write best */
        FILE *o = fopen(argv[2], "w");
        for (int i = 0; i < n; i++) if (bestS[i]) fprintf(o, "%d\n", i);
        fclose(o);
        printf("restart %lld best %lld t %.1f\n", restarts, bestW, el); fflush(stdout);
    }
    printf("final best %lld restarts %lld\n", bestW, restarts);
    return 0;
}
