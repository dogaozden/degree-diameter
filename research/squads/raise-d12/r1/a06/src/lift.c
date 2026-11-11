/* a06: anneal voltage lifts of H(3) (728-vertex, 4-regular, girth 12, diam 6) over a group Gamma of order m.
   Lift vertex (v,g) = v*m+g; base edge (a,b) with voltage w: (a,g)~(b,g*w). Spanning tree voltages = identity.
   Cost(source u) = #{lift vertices not within distance D of (u,e)}; full cost = sum over all 728 sources.
   Usage: lift BASE GROUP D secs seed K T OUT [INIT]
   BASE: "V E" then E lines "a b" (a<b not required). GROUP: m, m rows (i*j table), inv row.
   Writes OUT ("e value" per cotree edge) and OUT.lift (edge list of the lift, n first line) when full cost is 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }

static int V, E, m, D, K;
static int *ea, *eb, *M, *INV;
static int *nb, *dv;     /* per base vertex 4 incidences: neighbour, directed voltage */
static int *inc_e;       /* edge id per incidence */
static int *vol, *tree, ntree;
static uint32_t *stamp; static uint8_t *dep; static int *q;
static uint32_t cur_stamp = 1;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void setdv(void){
    for (int v = 0; v < V; v++) for (int k = 0; k < 4; k++) {
        int e = inc_e[4*v+k];
        int w = (ea[e] == v) ? vol[e] : INV[vol[e]];
        dv[4*v+k] = w;
    }
}
/* uncovered count for source u */
static long cost_src(int u){
    int N = V*m;
    cur_stamp++;
    int head = 0, tail = 0;
    int s = u*m + 0;
    stamp[s] = cur_stamp; dep[s] = 0; q[tail++] = s;
    long seen = 1;
    while (head < tail) {
        int x = q[head++];
        int d = dep[x];
        if (d >= D) continue;
        int v = x / m, g = x - v*m;
        for (int k = 0; k < 4; k++) {
            int y = nb[4*v+k]*m + M[g*m + dv[4*v+k]];
            if (stamp[y] != cur_stamp) { stamp[y] = cur_stamp; dep[y] = d+1; q[tail++] = y; seen++; }
        }
    }
    return N - seen;
}
static long cost_set(int *S, int ns){
    long c = 0; for (int i = 0; i < ns; i++) c += cost_src(S[i]); return c;
}
static long cost_full(void){
    int *S = malloc(sizeof(int)*V); for (int i=0;i<V;i++) S[i]=i;
    long c = cost_set(S, V); free(S); return c;
}
static void write_state(const char *out){
    char fn[512]; sprintf(fn, "%s", out);
    FILE *f = fopen(fn, "w"); for (int e = 0; e < E; e++) fprintf(f, "%d %d\n", e, vol[e]); fclose(f);
}
static void write_lift(const char *out){
    char fn[512]; sprintf(fn, "%s.lift", out);
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", V*m);
    for (int e = 0; e < E; e++) for (int g = 0; g < m; g++)
        fprintf(f, "%d %d\n", ea[e]*m + g, eb[e]*m + M[g*m + vol[e]]);
    fclose(f);
}
int main(int argc, char **argv){
    if (argc < 9) { fprintf(stderr, "usage: lift BASE GROUP D secs seed K T OUT [INIT]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &V, &E) != 2) return 1;
    ea = malloc(sizeof(int)*E); eb = malloc(sizeof(int)*E);
    for (int e = 0; e < E; e++) if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) return 1;
    fclose(f);
    f = fopen(argv[2], "r");
    if (fscanf(f, "%d", &m) != 1) return 1;
    M = malloc(sizeof(int)*m*m); INV = malloc(sizeof(int)*m);
    for (int i = 0; i < m*m; i++) if (fscanf(f, "%d", &M[i]) != 1) return 1;
    for (int i = 0; i < m; i++) if (fscanf(f, "%d", &INV[i]) != 1) return 1;
    fclose(f);
    D = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for(int i=0;i<10;i++) rnd();
    K = atoi(argv[6]); double T = atof(argv[7]); const char *out = argv[8];
    /* incidences */
    nb = malloc(sizeof(int)*4*V); dv = malloc(sizeof(int)*4*V); inc_e = malloc(sizeof(int)*4*V);
    int *deg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {
        int a = ea[e], b = eb[e];
        inc_e[4*a + deg[a]] = e; nb[4*a + deg[a]] = b; deg[a]++;
        inc_e[4*b + deg[b]] = e; nb[4*b + deg[b]] = a; deg[b]++;
    }
    for (int v = 0; v < V; v++) if (deg[v] != 4) { fprintf(stderr, "base not 4-regular\n"); return 1; }
    /* spanning tree by BFS from 0 */
    vol = calloc(E, sizeof(int)); tree = calloc(E, sizeof(int));
    int *seen = calloc(V, sizeof(int)); int *bq = malloc(sizeof(int)*V); int bh=0, bt=0;
    seen[0]=1; bq[bt++]=0;
    while (bh < bt) { int v = bq[bh++]; for (int k=0;k<4;k++){ int w=nb[4*v+k]; if(!seen[w]){ seen[w]=1; tree[inc_e[4*v+k]]=1; ntree++; bq[bt++]=w; } } }
    stamp = calloc(V*m, sizeof(uint32_t)); dep = malloc(V*m); q = malloc(sizeof(int)*V*m);
    /* initial voltages */
    if (argc > 9) {
        FILE *g = fopen(argv[9], "r"); int e, val;
        while (fscanf(g, "%d %d", &e, &val) == 2) vol[e] = val;
        fclose(g);
    } else {
        for (int e = 0; e < E; e++) vol[e] = tree[e] ? 0 : (int)(rnd() % m);
    }
    for (int e = 0; e < E; e++) if (tree[e]) vol[e] = 0;
    setdv();
    int *cot = malloc(sizeof(int)*E); int nc = 0;
    for (int e = 0; e < E; e++) if (!tree[e]) cot[nc++] = e;
    fprintf(stderr, "V=%d E=%d m=%d tree=%d cotree=%d D=%d K=%d T=%g\n", V, E, m, ntree, nc, D, K, T);
    long full = cost_full();
    fprintf(stderr, "initial full cost %ld\n", full);
    if (full == 0) { write_state(out); write_lift(out); printf("FOUND full cost 0 at start\n"); return 0; }
    double t0 = wall();
    long best_full = full;
    int *S = malloc(sizeof(int)*K);
    long iter = 0, round = 0;
    while (1) {
        /* new sample set each round */
        round++;
        for (int i = 0; i < K; i++) S[i] = rnd() % V;
        long cs = cost_set(S, K);
        long best_s = cs; int round_iters = 0;
        for (int it = 0; it < 4000; it++, iter++) {
            if ((iter & 63) == 0 && wall()-t0 > secs) goto done;
            int e = cot[rnd() % nc];
            int old = vol[e];
            int nw = (int)(rnd() % m);
            if (nw == old) continue;
            vol[e] = nw;
            int a = ea[e], b = eb[e];
            /* update dv entries for both endpoints */
            for (int k=0;k<4;k++) if (inc_e[4*a+k]==e) dv[4*a+k] = nw;
            for (int k=0;k<4;k++) if (inc_e[4*b+k]==e) dv[4*b+k] = INV[nw];
            long cn = cost_set(S, K);
            long delta = cn - cs;
            int acc = (delta <= 0) || ((double)(rnd()%1000000)/1e6 < exp(-(double)delta / T));
            if (acc) { cs = cn; if (cs < best_s) best_s = cs; }
            else {
                vol[e] = old;
                for (int k=0;k<4;k++) if (inc_e[4*a+k]==e) dv[4*a+k] = old;
                for (int k=0;k<4;k++) if (inc_e[4*b+k]==e) dv[4*b+k] = INV[old];
            }
            if (cs == 0) {
                long fc = cost_full();
                if (fc < best_full) best_full = fc;
                fprintf(stderr, "sample cost 0 at iter %ld, full cost %ld\n", iter, fc);
                if (fc == 0) { write_state(out); write_lift(out); printf("FOUND m=%d N=%d iter=%ld\n", m, V*m, iter); fflush(stdout); return 0; }
                break; /* resample */
            }
        }
        if ((round % 5) == 0) {
            long fc = cost_full(); if (fc < best_full) best_full = fc;
            fprintf(stderr, "round %ld iter %ld t=%.1fs sampled cost %ld full %ld (best full %ld)\n", round, iter,
                    wall()-t0, cs, fc, best_full);
            if (fc == 0) { write_state(out); write_lift(out); printf("FOUND m=%d N=%d\n", m, V*m); return 0; }
        }
    }
done:
    {
        long fc = cost_full();
        printf("END m=%d N=%d iter=%ld full=%ld best_full=%ld\n", m, V*m, iter, fc, best_full);
        write_state(out);
    }
    return 0;
}
