/* Haar-like graphs over a loop (or group) table.
   Vertices: A x -> x, B y -> n+y. Edges (x,A) ~ (s*x, B) for s in S, |S|=6.
   cost = number of ordered same-side pairs at distance > 4 (bitset ball-of-radius-4 computation).
   usage: hloop TABLE SECONDS SEED OUTPREFIX [T0] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define K 6
static int n, NV, W;
static int *M, *Linv;          /* M[s*n+x] = s*x ; Linv[s*n+y] = x with s*x=y */
static uint64_t *R, *R2;       /* NV * W words */
static uint64_t Amask[64*1024/64+8], Bmask[64*1024/64+8];

static uint64_t rng_s;
static inline uint64_t rnd(void){ rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void){ return (rnd() >> 11) * (1.0/9007199254740992.0); }

static int cost_of(const int *S){
    /* neighbours: A x -> B (M[s][x]) ; B y -> A (Linv[s][y]) ; vertex id: A x = x, B y = n+y */
    static int nb[1400][K];
    for(int x=0;x<n;x++) for(int k=0;k<K;k++) nb[x][k] = n + M[S[k]*n + x];
    for(int y=0;y<n;y++) for(int k=0;k<K;k++) nb[n+y][k] = Linv[S[k]*n + y];
    memset(R, 0, sizeof(uint64_t)*(size_t)NV*W);
    for(int v=0;v<NV;v++) R[(size_t)v*W + (v>>6)] |= 1ULL << (v&63);
    for(int it=0; it<4; it++){
        for(int v=0; v<NV; v++){
            uint64_t *dst = R2 + (size_t)v*W;
            const uint64_t *src = R + (size_t)v*W;
            memcpy(dst, src, sizeof(uint64_t)*W);
            for(int k=0;k<K;k++){
                const uint64_t *u = R + (size_t)nb[v][k]*W;
                for(int w=0; w<W; w++) dst[w] |= u[w];
            }
        }
        uint64_t *t = R; R = R2; R2 = t;
    }
    int c = 0;
    for(int v=0; v<NV; v++){
        const uint64_t *mask = (v < n) ? Amask : Bmask;
        int cnt = 0;
        const uint64_t *src = R + (size_t)v*W;
        for(int w=0; w<W; w++) cnt += __builtin_popcountll(src[w] & mask[w]);
        c += n - cnt;
    }
    return c;
}

static void write_edges(const char *fn, const int *S){
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", NV);
    for(int x=0;x<n;x++) for(int k=0;k<K;k++) fprintf(f, "%d %d\n", x, n + M[S[k]*n + x]);
    fclose(f);
}

int main(int argc, char **argv){
    if(argc < 5){ fprintf(stderr, "usage: hloop TABLE SECONDS SEED OUTPREFIX [T0]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if(fscanf(f, "%d", &n)!=1) return 1;
    M = malloc(sizeof(int)*n*n); Linv = malloc(sizeof(int)*n*n);
    for(int i=0;i<n*n;i++) if(fscanf(f, "%d", &M[i])!=1) return 1;
    fclose(f);
    for(int s=0;s<n;s++) for(int x=0;x<n;x++) Linv[s*n + M[s*n+x]] = x;
    NV = 2*n; W = (NV + 63)/64;
    R = calloc((size_t)NV*W, 8); R2 = calloc((size_t)NV*W, 8);
    memset(Amask,0,sizeof Amask); memset(Bmask,0,sizeof Bmask);
    for(int v=0; v<NV; v++){ if(v<n) Amask[v>>6] |= 1ULL<<(v&63); else Bmask[v>>6] |= 1ULL<<(v&63); }
    double secs = atof(argv[2]); rng_s = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[3]) * 2654435761ULL; if(!rng_s) rng_s=1;
    const char *outp = argv[4];
    double T0 = argc > 5 ? atof(argv[5]) : 3.0;
    clock_t t0 = clock();
    int best = 1<<30; int bestS[K];
    int S[K]; long total = 0; int restarts = 0;
    while(((double)(clock()-t0))/CLOCKS_PER_SEC < secs){
        /* random initial S */
        int inS[1400]; memset(inS, 0, sizeof(int)*n);
        for(int k=0;k<K;k++){ int e; do e = rnd()%n; while(inS[e]); inS[e]=1; S[k]=e; }
        int cur = cost_of(S);
        long iters = 60000; restarts++;
        for(long it=0; it<iters; it++){
            double T = T0 * pow(0.02/1.0, (double)it/iters);
            int k = rnd()%K; int e; do e = rnd()%n; while(inS[e]);
            int old = S[k];
            S[k] = e;
            int c = cost_of(S); total++;
            int d = c - cur;
            if(d <= 0 || urand() < exp(-d / T)){
                inS[old]=0; inS[e]=1; cur = c;
                if(cur < best){ best = cur; memcpy(bestS, S, sizeof S);
                    if(best==0) break; }
            } else S[k] = old;
            if(best==0) break;
        }
        if(best==0) break;
        if(((double)(clock()-t0))/CLOCKS_PER_SEC > secs) break;
    }
    printf("n=%d best_cost=%d evals=%ld restarts=%d S=", n, best, total, restarts);
    for(int k=0;k<K;k++) printf("%d ", bestS[k]);
    printf("\n");
    if(best==0){ char fn[512]; sprintf(fn, "%s.edges", outp); write_edges(fn, bestS); printf("wrote %s\n", fn); }
    return 0;
}
