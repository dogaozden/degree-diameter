/* b04: repair c31's graph by targeted 2-switch simulated annealing.
   Energy = number of unordered far pairs (distance > 8). Bipartite-preserving 2-switches only.
   usage: sa IN.edges OUT.edges SECONDS SEED T0 T1 PTARGET */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2400
#define D 4
static int n, W;
static int adj[MAXN][D];
static int side[MAXN];
static uint64_t *bufA, *bufB;
static uint64_t rs;

static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void){ return (rnd() >> 11) * (1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9*t.tv_nsec; }

/* compute ball radius 8 bitsets; returns far unordered count; B8 left in bufA (after 8 steps) */
static uint64_t *B8;
static long eval(void){
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t)*(size_t)n*W);
    for (int v = 0; v < n; v++) cur[(size_t)v*W + v/64] |= 1ULL << (v%64);
    for (int k = 0; k < 8; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v*W; const uint64_t *c = cur + (size_t)v*W;
            for (int j = 0; j < W; j++) o[j] = c[j];
            for (int d = 0; d < D; d++) {
                const uint64_t *u = cur + (size_t)adj[v][d]*W;
                for (int j = 0; j < W; j++) o[j] |= u[j];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    B8 = cur;
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int j = 0; j < W; j++) c += __builtin_popcountll(cur[(size_t)v*W+j]);
        tot += n - c;
    }
    return tot/2;
}

static int hasedge(int a, int b){ for (int d=0; d<D; d++) if (adj[a][d]==b) return 1; return 0; }
static void repl(int v, int from, int to){ for (int d=0; d<D; d++) if (adj[v][d]==from){ adj[v][d]=to; return; } fprintf(stderr,"repl fail\n"); exit(1); }
/* edges (a1,b1),(a2,b2) -> (a1,b2),(a2,b1); a's in side 0, b's in side 1 */
static int valid_switch(int a1,int b1,int a2,int b2){
    if (a1==a2 || b1==b2) return 0;
    if (hasedge(a1,b2) || hasedge(a2,b1)) return 0;
    return 1;
}
static void do_switch(int a1,int b1,int a2,int b2){
    repl(a1,b1,b2); repl(b1,a1,a2); repl(a2,b2,b1); repl(b2,a2,a1);
}

static int *farU, *farV; static long nfar;
static void extract_far(void){
    nfar = 0;
    for (int v = 0; v < n; v++) {
        uint64_t *r = B8 + (size_t)v*W;
        for (int j = 0; j < W; j++) {
            uint64_t z = ~r[j];
            while (z) {
                int b = __builtin_ctzll(z); z &= z-1;
                int w = j*64 + b;
                if (w >= n) break;
                if (w > v) { farU[nfar] = v; farV[nfar] = w; nfar++; }
            }
        }
    }
}

static int walk(int x, int L){ int y = x; for (int i=0;i<L;i++) y = adj[y][rnd()%D]; return y; }

int main(int argc, char **argv){
    if (argc < 8) { fprintf(stderr, "usage: sa IN OUT SECONDS SEED T0 T1 PTARGET\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &n) != 1) return 1;
    int *deg = calloc(n, sizeof(int));
    for (int i = 0; i < n; i++) deg[i]=0;
    int m; long cap = 0; int (*E)[2] = NULL; m = 0;
    E = malloc(sizeof(int)*2*(size_t)n*D);
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) { E[m][0]=u; E[m][1]=v; m++; deg[u]++; deg[v]++; if (deg[u]>D||deg[v]>D){fprintf(stderr,"deg>4\n");return 1;} adj[u][deg[u]-1]=v; adj[v][deg[v]-1]=u; }
    fclose(f);
    for (int i=0;i<n;i++) if (deg[i]!=D) { fprintf(stderr,"degree not 4 at %d\n",i); return 1; }
    /* 2-color */
    for (int i=0;i<n;i++) side[i]=-1;
    int *q = malloc(sizeof(int)*n); int qh=0, qt=0; side[0]=0; q[qt++]=0;
    while (qh<qt){ int x=q[qh++]; for(int d=0;d<D;d++){ int y=adj[x][d]; if(side[y]<0){side[y]=1-side[x]; q[qt++]=y;} else if (side[y]==side[x]){fprintf(stderr,"not bipartite\n");return 1;} } }
    W = (n+63)/64;
    bufA = malloc(sizeof(uint64_t)*(size_t)n*W); bufB = malloc(sizeof(uint64_t)*(size_t)n*W);
    farU = malloc(sizeof(int)*n*n/4+64); farV = malloc(sizeof(int)*n*n/4+64);
    double secs = atof(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4])*2654435761ULL; if(!rs) rs=1;
    double T0 = atof(argv[5]), T1 = atof(argv[6]); double pt = atof(argv[7]);
    long cur = eval(); extract_far();
    long best = cur; static int bestadj[MAXN][D]; memcpy(bestadj, adj, sizeof(adj));
    fprintf(stderr, "start far=%ld\n", cur);
    double t0 = now(), T = T0; long it = 0, acc = 0;
    while (1) {
        if ((it & 63) == 0) { double el = now()-t0; if (el > secs) break; double fr = el/secs; T = T0*pow(T1/T0, fr); }
        it++;
        int a1,b1,a2,b2;
        if (nfar > 0 && urand() < pt) {
            long k = rnd()%nfar; int x = farU[k], y = farV[k];
            if (rnd()&1) { int t=x; x=y; y=t; }
            int p1 = walk(x, 1 + rnd()%3);
            int p2 = walk(y, 1 + rnd()%3);
            int z1 = adj[p1][rnd()%D], z2 = adj[p2][rnd()%D];
            if (side[p1]==0){a1=p1;b1=z1;} else {a1=z1;b1=p1;}
            if (side[p2]==0){a2=p2;b2=z2;} else {a2=z2;b2=p2;}
        } else {
            int pa = -1; /* random A vertex */
            do { pa = rnd()%n; } while (side[pa]!=0);
            a1 = pa; b1 = adj[pa][rnd()%D];
            do { pa = rnd()%n; } while (side[pa]!=0);
            a2 = pa; b2 = adj[pa][rnd()%D];
        }
        if (!valid_switch(a1,b1,a2,b2)) continue;
        do_switch(a1,b1,a2,b2);
        long nw = eval();
        long delta = nw - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nw; acc++; extract_far();
            if (cur < best) { best = cur; memcpy(bestadj, adj, sizeof(adj)); fprintf(stderr, "t=%.1f it=%ld best=%ld T=%.3f\n", now()-t0, it, best, T); if (best==0) break; }
        } else {
            do_switch(a1,b2,a2,b1); /* undo */
        }
    }
    memcpy(adj, bestadj, sizeof(adj));
    /* write best */
    FILE *o = fopen(argv[2], "w"); fprintf(o, "%d\n", n);
    for (int a=0;a<n;a++) if (side[a]==0) for (int d=0; d<D; d++) fprintf(o, "%d %d\n", a, adj[a][d]);
    fclose(o);
    printf("RESULT best_far=%ld final=%ld iters=%ld accepted=%ld time=%.1f\n", best, cur, it, acc, now()-t0);
    return 0;
}
