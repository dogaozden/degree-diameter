/* spread.c: how well can flag shifts sigma (values in Z_k) spread the voltages of the q+1 geodesics between two
   opposite lines (and two opposite points) of H(q)?  Cost = sum over opposite pairs of (min(k,q+1) - #distinct
   geodesic voltages).  Simulated annealing over sigma.
   Usage: spread HEX k secs seed [points]   ("points": also count opposite point pairs) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int q, q1, N, V, k;
static int *lp, *pl;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
/* flag id: p*q1 + j (j-th line of p).  For a line l and its point slot, find flag id. */
static int flag_of(int p, int l) { for (int j = 0; j < q1; j++) if (pl[p * q1 + j] == l) return p * q1 + j; return -1; }
/* geodesic = 6 flags with signs (+1 if traversed point->line) */
typedef struct { int f[6]; signed char s[6]; } Geo;
static Geo *geo; static long ngeo; static int *pairstart; static long npairs;
static int *sig;
static long *flagocc_start; static long *flagocc; /* list of (geodesic index) per flag */
int main(int argc, char **argv) {
    FILE *fh = fopen(argv[1], "rb"); int32_t h[3]; if (fread(h, 4, 3, fh) != 3) return 1;
    q = h[0]; N = h[1]; q1 = q + 1; V = 2 * N; k = atoi(argv[2]); double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int dopoints = argc > 5;
    int32_t *tmp = malloc(4 * (size_t)N * q1); if (fread(tmp, 4, (size_t)N * q1, fh) != (size_t)N * q1) return 1; fclose(fh);
    lp = malloc(sizeof(int) * N * q1); pl = malloc(sizeof(int) * N * q1); int *cnt = calloc(N, sizeof(int));
    for (int i = 0; i < N * q1; i++) lp[i] = tmp[i];
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) { int p = lp[l * q1 + j]; pl[p * q1 + cnt[p]++] = l; }
    /* BFS parents to enumerate geodesics: for opposite (l1,l2): for each point p1 on l1, unique path p1 -> l2 of
       length 5.  We get it by BFS from l2 recording distance; then walk down. */
    int *dist = malloc(sizeof(int) * V), *qu = malloc(sizeof(int) * V);
    long cap = (long)N * 300 * q1 + 16; geo = malloc(sizeof(Geo) * cap); ngeo = 0; npairs = 0;
    long pcap = (long)N * 300 + 16; pairstart = malloc(sizeof(int) * pcap);
    int nsides = dopoints ? 2 : 1;
    for (int side = 0; side < nsides; side++)
    for (int a = 0; a < N; a++) {
        int src = side == 0 ? N + a : a;   /* side 0: lines, side 1: points */
        for (int x = 0; x < V; x++) dist[x] = -1;
        int hh = 0, tl = 0; dist[src] = 0; qu[tl++] = src;
        while (hh < tl) { int x = qu[hh++]; for (int j = 0; j < q1; j++) { int y = x < N ? N + pl[x * q1 + j] : lp[(x - N) * q1 + j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[tl++] = y; } } }
        /* opposite elements b > a of same side */
        for (int b = a + 1; b < N; b++) {
            int tgt = side == 0 ? N + b : b;
            if (dist[tgt] != 6) continue;
            if (ngeo + q1 > cap) { cap *= 2; geo = realloc(geo, sizeof(Geo) * cap); }
            if (npairs + 2 > pcap) { pcap *= 2; pairstart = realloc(pairstart, sizeof(int) * pcap); }
            pairstart[npairs++] = (int)ngeo;
            /* geodesics from tgt down to src: tgt's neighbours are at distance 5 */
            for (int j = 0; j < q1; j++) {
                int path[7]; path[0] = tgt; path[1] = tgt < N ? N + pl[tgt * q1 + j] : lp[(tgt - N) * q1 + j];
                int ok = dist[path[1]] == 5;
                for (int s = 2; s <= 6 && ok; s++) {
                    int x = path[s - 1], found = -1;
                    for (int jj = 0; jj < q1; jj++) { int y = x < N ? N + pl[x * q1 + jj] : lp[(x - N) * q1 + jj]; if (dist[y] == 6 - s) { found = y; break; } }
                    path[s] = found; if (found < 0) ok = 0;
                }
                if (!ok) { fprintf(stderr, "geodesic error\n"); return 1; }
                Geo g;
                for (int s = 0; s < 6; s++) {
                    int x = path[s], y = path[s + 1];
                    if (x < N) { g.f[s] = flag_of(x, y - N); g.s[s] = 1; } else { g.f[s] = flag_of(y, x - N); g.s[s] = -1; }
                }
                geo[ngeo++] = g;
            }
        }
    }
    pairstart[npairs] = (int)ngeo;
    fprintf(stderr, "q=%d k=%d pairs=%ld geodesics=%ld\n", q, k, npairs, ngeo);
    int F = N * q1;
    /* flag -> geodesic occurrence lists */
    flagocc_start = calloc(F + 1, sizeof(long));
    for (long g = 0; g < ngeo; g++) for (int s = 0; s < 6; s++) flagocc_start[geo[g].f[s] + 1]++;
    for (int f = 0; f < F; f++) flagocc_start[f + 1] += flagocc_start[f];
    flagocc = malloc(sizeof(long) * ngeo * 6); long *fill = calloc(F, sizeof(long));
    for (long g = 0; g < ngeo; g++) for (int s = 0; s < 6; s++) { int f = geo[g].f[s]; flagocc[flagocc_start[f] + fill[f]++] = g; }
    int *g2p = malloc(sizeof(int) * ngeo);
    for (long pi = 0; pi < npairs; pi++) for (long g = pairstart[pi]; g < pairstart[pi + 1]; g++) g2p[g] = (int)pi;
    sig = malloc(sizeof(int) * F); for (int f = 0; f < F; f++) sig[f] = rnd() % k;
    int *gv = malloc(sizeof(int) * ngeo);
    int target = k < q1 ? k : q1;
    #define GV(g) ({ int _v = 0; for (int _s = 0; _s < 6; _s++) _v += geo[g].s[_s] * sig[geo[g].f[_s]]; ((_v % k) + k) % k; })
    for (long g = 0; g < ngeo; g++) gv[g] = GV(g);
    int *pc = malloc(sizeof(int) * npairs);  /* missing count per pair */
    long cost = 0;
    int cntv[128];
    for (long pi = 0; pi < npairs; pi++) {
        memset(cntv, 0, sizeof(int) * k); int d = 0;
        for (long g = pairstart[pi]; g < pairstart[pi + 1]; g++) if (!cntv[gv[g]]++) d++;
        pc[pi] = target - d; cost += pc[pi];
    }
    fprintf(stderr, "random sigma: cost %ld (%.3f per pair)\n", cost, (double)cost / npairs);
    long best = cost; double t0 = now(), T0 = 2.0, T1 = 0.05; long it = 0;
    int *touched = malloc(sizeof(int) * npairs); char *mark = calloc(npairs, 1);
    while (now() - t0 < secs && best > 0) {
        double T = T0 * pow(T1 / T0, (now() - t0) / secs);
        int f = rnd() % F, old = sig[f], nv = rnd() % k; if (nv == old) continue;
        sig[f] = nv; int nt = 0;
        for (long o = flagocc_start[f]; o < flagocc_start[f + 1]; o++) { long g = flagocc[o]; int pi = g2p[g]; if (!mark[pi]) { mark[pi] = 1; touched[nt++] = pi; } }
        long delta = 0;
        static int newpc[1 << 20];
        for (int i = 0; i < nt; i++) {
            int pi = touched[i]; memset(cntv, 0, sizeof(int) * k); int d = 0;
            for (long g = pairstart[pi]; g < pairstart[pi + 1]; g++) { int v = GV(g); if (!cntv[v]++) d++; }
            newpc[i] = target - d; delta += newpc[i] - pc[pi];
        }
        it++;
        if (delta <= 0 || exp(-delta / T) > (rnd() >> 11) * (1.0 / 9007199254740992.0)) {
            for (int i = 0; i < nt; i++) pc[touched[i]] = newpc[i];
            cost += delta; if (cost < best) best = cost;
        } else sig[f] = old;
        for (int i = 0; i < nt; i++) mark[touched[i]] = 0;
    }
    printf("RESULT q=%d k=%d pairs=%ld best=%ld (%.4f per pair) it=%ld\n", q, k, npairs, best, (double)best / npairs, it);
    return 0;
}
