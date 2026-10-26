/* z6lift.c: exact cost of a Z6 voltage lift of a bipartite base + doubled matching, with ARBITRARY Z6 voltages on
   every flag and on both copies of every matching edge (the DM family is flags in {0,3}, copies 1 and 4), and
   simulated annealing on that exact cost.  Cost = number of pairs (source (v,0), target lift vertex) at distance > 5
   (sources at sheet 0 suffice: Z6 acts on the sheets).  Cost 0 = diameter <= 5.
   usage: z6lift base.in   env: NU (one 0/1 per flag, flag = l*dg + slot; flag voltage 3*nu), VOLT (voltage file
   written by OUTV: flag voltages then 2n jump voltages), SECS, SEED, T0, T1, PJ (prob of a jump-voltage move),
   PS (prob of a sigma swap), HOT=1 (restrict moves to edges near failing vertices), OUTV, SCORE=1.
   Writes the lift edge list with EDGES=file (vertex (x,h) = 6x + h, x < n points, n + l lines). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
#define M 6
int n, dg, V, NF, NE; int *ln, *sig;
int *eu, *ev, *eg;              /* edges: u point, v line (base ids, line = n + l), voltage u -> v */
int *ioff, *iadj, *ie, *isg;    /* incidence per base vertex: neighbour, edge id, sign */
uint64_t *cur, *nxt, *seen; uint8_t *hotv;
static void build_inc(void) {
    int *deg = calloc(V, 4); for (int e = 0; e < NE; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    ioff[0] = 0; for (int x = 0; x < V; x++) ioff[x + 1] = ioff[x] + deg[x];
    memset(deg, 0, 4L * V);
    for (int e = 0; e < NE; e++) { int a = eu[e], b = ev[e];
        int i = ioff[a] + deg[a]++; iadj[i] = b; ie[i] = e; isg[i] = 1;
        i = ioff[b] + deg[b]++; iadj[i] = a; ie[i] = e; isg[i] = -1; }
    free(deg);
}
static long cost(int mark) {
    long c = 0; if (mark) memset(hotv, 0, V);
    for (int s0 = 0; s0 < V; s0 += 64) {
        int ns = V - s0 < 64 ? V - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(cur, 0, 8L * V * M); for (int k = 0; k < ns; k++) cur[(s0 + k) * M] |= 1ULL << k;
        memcpy(seen, cur, 8L * V * M);
        for (int d = 1; d <= 5; d++) {
            memset(nxt, 0, 8L * V * M);
            for (int x = 0; x < V; x++) {
                const uint64_t *cx = cur + x * M; uint64_t any = cx[0] | cx[1] | cx[2] | cx[3] | cx[4] | cx[5]; if (!any) continue;
                for (int i = ioff[x]; i < ioff[x + 1]; i++) { int y = iadj[i]; int g = eg[ie[i]]; if (isg[i] < 0) g = (M - g) % M;
                    uint64_t *ny = nxt + y * M; for (int h = 0; h < M; h++) { int h2 = h + g; if (h2 >= M) h2 -= M; ny[h2] |= cx[h]; } }
            }
            for (int i = 0; i < V * M; i++) seen[i] |= nxt[i];
            uint64_t *t = cur; cur = nxt; nxt = t;
        }
        for (int i = 0; i < V * M; i++) { uint64_t bad = ~seen[i] & full; if (bad) { c += __builtin_popcountll(bad);
            if (mark) { hotv[i / M] = 1; while (bad) { int k = __builtin_ctzll(bad); bad &= bad - 1; hotv[s0 + k] = 1; } } } }
    }
    return c;
}
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n; NF = n * dg; NE = NF + 2 * n;
    ln = malloc(4L * NF); for (int i = 0; i < NF; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    eu = malloc(4L * NE); ev = malloc(4L * NE); eg = calloc(NE, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int e = l * dg + k; eu[e] = ln[e]; ev[e] = n + l; }
    for (int p = 0; p < n; p++) for (int c = 0; c < 2; c++) { int e = NF + 2 * p + c; eu[e] = p; ev[e] = n + sig[p]; eg[e] = c ? 4 : 1; }
    if (getenv("NU")) { FILE *g = fopen(getenv("NU"), "r"); for (int i = 0; i < NF; i++) { int v; if (fscanf(g, "%d", &v) != 1) return 1; eg[i] = 3 * (v & 1); } fclose(g); }
    if (getenv("VOLT")) { FILE *g = fopen(getenv("VOLT"), "r"); for (int i = 0; i < NE; i++) if (fscanf(g, "%d", &eg[i]) != 1) return 1; fclose(g); }
    ioff = malloc(4L * (V + 1)); iadj = malloc(8L * NE); ie = malloc(8L * NE); isg = malloc(8L * NE); build_inc();
    cur = malloc(8L * V * M); nxt = malloc(8L * V * M); seen = malloc(8L * V * M); hotv = calloc(V, 1);
    clock_t c0 = clock(); long c = cost(1); double tev = (double)(clock() - c0) / CLOCKS_PER_SEC;
    int nh = 0; for (int x = 0; x < V; x++) nh += hotv[x];
    printf("lift vertices %d, cost %ld, hot base vertices %d (eval %.4fs)\n", V * M, c, nh, tev); fflush(stdout);
    if (getenv("EDGES")) { FILE *g = fopen(getenv("EDGES"), "w"); fprintf(g, "%d\n", V * M);
        for (int e = 0; e < NE; e++) for (int h = 0; h < M; h++) fprintf(g, "%d %d\n", eu[e] * M + h, ev[e] * M + (h + eg[e]) % M); fclose(g); }
    if (getenv("SCORE")) return 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 2, T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    double PJ = getenv("PJ") ? atof(getenv("PJ")) : 0.2; int HOT = getenv("HOT") ? atoi(getenv("HOT")) : 1;
    long best = c; int *beg = malloc(4L * NE); memcpy(beg, eg, 4L * NE);
    /* hot edge list: edges with an endpoint within distance 1 of a hot base vertex */
    int *hel = malloc(4L * NE), nhe = 0;
    #define REHOT() do { nhe = 0; for (int e = 0; e < NE; e++) { int a = eu[e], b = ev[e], h = hotv[a] || hotv[b]; \
        if (!h && HOT > 1) { for (int i = ioff[a]; i < ioff[a + 1] && !h; i++) h = hotv[iadj[i]]; for (int i = ioff[b]; i < ioff[b + 1] && !h; i++) h = hotv[iadj[i]]; } \
        if (h) hel[nhe++] = e; } } while (0)
    REHOT(); printf("hot edges %d\n", nhe); fflush(stdout);
    clock_t t0 = clock(); long it = 0;
    while (best > 0) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, el / secs); it++;
        int e;
        if (HOT && nhe && urand() < 0.9) e = hel[rnd() % nhe]; else e = rnd() % NE;
        if ((e >= NF) != (urand() < PJ)) { /* bias the mix: retry once with the other class */ e = (urand() < PJ) ? NF + rnd() % (2 * n) : rnd() % NF; }
        int old = eg[e], nw = (old + 1 + rnd() % (M - 1)) % M; eg[e] = nw;
        long c2 = cost(0);
        if (c2 <= c || urand() < exp((c - c2) / T)) c = c2; else eg[e] = old;
        if (c < best) { best = c; memcpy(beg, eg, 4L * NE); printf("t=%.0f it=%ld cost=%ld T=%.3f\n", el, it, c, T); fflush(stdout);
            cost(1); REHOT(); }
        if ((it & 1023) == 0) { cost(1); REHOT(); }
    }
    memcpy(eg, beg, 4L * NE);
    printf("RESULT best=%ld iters=%ld\n", best, it);
    if (getenv("OUTV")) { FILE *g = fopen(getenv("OUTV"), "w"); for (int e = 0; e < NE; e++) fprintf(g, "%d\n", eg[e]); fclose(g); }
    return 0;
}
