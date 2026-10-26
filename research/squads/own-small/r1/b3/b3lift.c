// b3lift: anneal cotree voltages of a regular G-cover of a cubic base (|G| <= 12, base <= 400 vertices).
// Convention: base edge e=(u,v) with voltage a: lift (u,g)~(v,g*a). Left translation is an automorphism.
// Cost = sum over roots u of #{(v,g): dist((u,e),(v,g)) > 10} = 2*far/|G| (0 iff diameter <= 10).
// usage: b3lift BASE GROUP SECONDS SEED OUTPREFIX [T0 T1]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 400
#define MAXG 12
#define DIAM 10
#define MAXE 1000

static int nb, mb, G;
static int eu[MAXE], ev[MAXE], isTree[MAXE], volt[MAXE], bestvolt[MAXE], cot[MAXE], ncot;
static int adjE[MAXN][3], adjCnt[MAXN];
static int mul[MAXG][MAXG], invg[MAXG];
static uint16_t R[MAXG][1 << MAXG];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static long cost(void) {
    static uint16_t D[MAXN], N2[MAXN];
    static int nbr[MAXN][3], tix[MAXN][3];
    for (int v = 0; v < nb; v++)
        for (int k = 0; k < 3; k++) {
            int e = adjE[v][k];
            if (eu[e] == v) { nbr[v][k] = ev[e]; tix[v][k] = invg[volt[e]]; }
            else { nbr[v][k] = eu[e]; tix[v][k] = volt[e]; }
        }
    long total = 0;
    for (int u = 0; u < nb; u++) {
        for (int v = 0; v < nb; v++) D[v] = 0;
        D[u] = 1;
        for (int lev = 0; lev < DIAM; lev++) {
            for (int v = 0; v < nb; v++) {
                uint16_t x = D[v];
                for (int k = 0; k < 3; k++) x |= R[tix[v][k]][D[nbr[v][k]]];
                N2[v] = x;
            }
            memcpy(D, N2, sizeof(uint16_t) * nb);
        }
        for (int v = 0; v < nb; v++) total += G - __builtin_popcount(D[v]);
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: BASE GROUP SECONDS SEED OUTPREFIX [T0 T1]\n"); return 1; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double T0 = argc > 6 ? atof(argv[6]) : 6.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d %d", &nb, &mb) != 2) { fprintf(stderr, "bad base\n"); return 1; }
    if (nb > MAXN || mb > MAXE) { fprintf(stderr, "base too big\n"); return 1; }
    memset(adjCnt, 0, sizeof adjCnt);
    for (int e = 0; e < mb; e++) {
        if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) return 1;
        adjE[eu[e]][adjCnt[eu[e]]++] = e;
        adjE[ev[e]][adjCnt[ev[e]]++] = e;
    }
    fclose(f);
    for (int v = 0; v < nb; v++) if (adjCnt[v] != 3) { fprintf(stderr, "not cubic\n"); return 1; }
    /* spanning tree by BFS from 0 */
    int seen[MAXN] = {0}, q[MAXN], qh = 0, qt = 0;
    q[qt++] = 0; seen[0] = 1;
    while (qh < qt) {
        int v = q[qh++];
        for (int k = 0; k < 3; k++) {
            int e = adjE[v][k], w = eu[e] == v ? ev[e] : eu[e];
            if (!seen[w]) { seen[w] = 1; isTree[e] = 1; q[qt++] = w; }
        }
    }
    if (qt != nb) { fprintf(stderr, "base disconnected\n"); return 1; }
    ncot = 0;
    for (int e = 0; e < mb; e++) if (!isTree[e]) cot[ncot++] = e;
    /* group */
    FILE *g = fopen(argv[2], "r");
    if (!g || fscanf(g, "%d", &G) != 1 || G > MAXG) { fprintf(stderr, "bad group\n"); return 1; }
    for (int a = 0; a < G; a++) for (int b = 0; b < G; b++) if (fscanf(g, "%d", &mul[a][b]) != 1) return 1;
    fclose(g);
    for (int a = 0; a < G; a++) { if (mul[0][a] != a || mul[a][0] != a) { fprintf(stderr, "identity not 0\n"); return 1; } }
    for (int a = 0; a < G; a++) for (int b = 0; b < G; b++) for (int c = 0; c < G; c++)
        if (mul[mul[a][b]][c] != mul[a][mul[b][c]]) { fprintf(stderr, "not associative\n"); return 1; }
    for (int a = 0; a < G; a++) for (int b = 0; b < G; b++) if (mul[a][b] == 0) invg[a] = b;
    for (int h = 0; h < G; h++) for (int mask = 0; mask < (1 << G); mask++) {
        int x = 0;
        for (int k = 0; k < G; k++) if (mask >> k & 1) x |= 1 << mul[k][h];
        R[h][mask] = (uint16_t)x;
    }
    /* init */
    for (int e = 0; e < mb; e++) volt[e] = 0;
    for (int c = 0; c < ncot; c++) volt[cot[c]] = rnd() % G;
    long cur = cost(), best = cur;
    memcpy(bestvolt, volt, sizeof volt);
    double t0 = now(); long it = 0;
    while (best > 0) {
        double el = now() - t0;
        if (el >= secs) break;
        double T = T0 * pow(T1 / T0, el / secs);
        int e = cot[rnd() % ncot];
        int old = volt[e];
        int nv = rnd() % (G - 1); if (nv >= old) nv++;
        volt[e] = nv;
        long nc = cost();
        long d = nc - cur;
        if (d <= 0 || (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < exp(-d / T)) {
            cur = nc;
            if (cur < best) { best = cur; memcpy(bestvolt, volt, sizeof volt); }
        } else volt[e] = old;
        it++;
    }
    memcpy(volt, bestvolt, sizeof volt);
    long nl = (long)nb * G;
    long far = (long)G * best / 2;
    printf("RESULT base=%s group=%s G=%d n=%ld cost=%ld far=%ld iters=%ld\n", argv[1], argv[2], G, nl, best, far, it);
    /* outputs */
    char fn[1024];
    snprintf(fn, sizeof fn, "%s.edges", argv[5]);
    FILE *o = fopen(fn, "w");
    fprintf(o, "%ld\n", nl);
    for (int e = 0; e < mb; e++)
        for (int x = 0; x < G; x++)
            fprintf(o, "%ld %ld\n", (long)eu[e] * G + x, (long)ev[e] * G + mul[x][volt[e]]);
    fclose(o);
    snprintf(fn, sizeof fn, "%s.volts", argv[5]);
    o = fopen(fn, "w");
    for (int c = 0; c < ncot; c++) fprintf(o, "%d %d %d\n", eu[cot[c]], ev[cot[c]], volt[cot[c]]);
    fclose(o);
    return 0;
}
