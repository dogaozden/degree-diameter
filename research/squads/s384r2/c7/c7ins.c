/* c7 (s384r2): insert a vertex pair into the 684 Haar record H(G,S), G = C6 x (C19:C3).
 * Step 1 (calibration): anneal a 6-set S until H(G,S) has bad = 0 (diameter 5, 684 vertices).
 * Step 2: choose a 6-edge matching M = {(a_i,b_i)} of H; delete M, add u0 ~ all b_i and u1 ~ all a_i.
 *         Result: bipartite, 6-regular, 686 vertices. Anneal over M.
 * Cost = unordered vertex pairs at distance > 5 (bitset ball-5 computation, exact).
 * Usage: c7ins SEED ITERS_S ITERS_M OUTPREFIX
 * Output: OUTPREFIX_best.edges (686-vertex edge list, apsp format) when the best cost is written.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define ORD 342
#define NH 684
#define NI 686
#define MAXW 12
#define DEG 6
#define TABU_STEPS 2000

static int mulT[ORD][ORD], invT[ORD];
static uint64_t rs;
static uint64_t rnd(void){ uint64_t z=(rs+=0x9E3779B97F4A7C15ULL); z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL; z=(z^(z>>27))*0x94D049BB133111EBULL; return z^(z>>31); }
static double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }

static void build_group(void){
    static const int pw[3]={1,7,11};   /* 7 has order 3 mod 19 */
    for (int x=0;x<ORD;x++) for (int y=0;y<ORD;y++){
        int c1=x/57, a1=(x%57)/3, b1=x%3, c2=y/57, a2=(y%57)/3, b2=y%3;
        int c=(c1+c2)%6, a=(a1+pw[b1]*a2)%19, b=(b1+b2)%3;
        mulT[x][y]=c*57+a*3+b;
    }
    for (int x=0;x<ORD;x++) for (int y=0;y<ORD;y++) if (mulT[x][y]==0) invT[x]=y;
}

/* side-0 vertex g, side-1 vertex ORD+h; (g,0)~(h,1) iff g^-1 h in S, i.e. h = g s */
static void build_haar(const int *S, int *adj){
    for (int g=0; g<ORD; g++) for (int k=0;k<DEG;k++) adj[g*DEG+k] = ORD + mulT[g][S[k]];
    for (int h=0; h<ORD; h++) for (int k=0;k<DEG;k++) adj[(ORD+h)*DEG+k] = mulT[h][invT[S[k]]];
}

static uint64_t BB[2][NI][MAXW];
static long bad_pairs(int N, const int *adj){
    int W=(N+63)/64;
    for (int v=0; v<N; v++){ for (int w=0; w<W; w++) BB[0][v][w]=0; BB[0][v][v>>6] |= 1ULL<<(v&63); }
    int cur=0;
    for (int step=0; step<5; step++){
        int nx=cur^1;
        for (int v=0; v<N; v++){
            uint64_t *dst=BB[nx][v]; const uint64_t *src=BB[cur][v];
            for (int w=0; w<W; w++) dst[w]=src[w];
            for (int k=0;k<DEG;k++){ const uint64_t *u=BB[cur][adj[v*DEG+k]]; for (int w=0; w<W; w++) dst[w] |= u[w]; }
        }
        cur=nx;
    }
    long cnt=0;
    for (int v=0; v<N; v++){ long pc=0; for (int w=0; w<W; w++) pc+=__builtin_popcountll(BB[cur][v][w]); cnt += N-pc; }
    return cnt/2;
}

static int inset(const int *S, int n, int t){ for (int i=0;i<n;i++) if (S[i]==t) return 1; return 0; }

static long cost_S(const int *S){ static int adj[NH*DEG]; build_haar(S, adj); return bad_pairs(NH, adj); }

static int find_S(long iters, int *Sout){
    int S[DEG];
    for (int k=0;k<DEG;k++){ int t; do t=rnd()%ORD; while (inset(S,k,t)); S[k]=t; }
    long c=cost_S(S), best=c; memcpy(Sout,S,sizeof S);
    for (long it=0; it<iters && best>0; it++){
        double T = 150.0*pow(0.02,(double)it/iters)+0.5;
        int k=rnd()%DEG, t=rnd()%ORD; if (inset(S,DEG,t)) continue;
        int old=S[k]; S[k]=t;
        long c2=cost_S(S);
        if (c2<=c || urand() < exp(-(double)(c2-c)/T)){
            c=c2;
            if (c<best){ best=c; memcpy(Sout,S,sizeof S); fprintf(stderr,"S-anneal it %ld best %ld\n",it,best); }
        } else S[k]=old;
    }
    return best==0;
}


/* tabu over S: sampled neighbourhood (SAMP random single-element swaps per step) */
static int find_S_tabu(long steps, int samp, int *Sout){
    int S[DEG]; static long tabu_until[ORD];
    for (int k=0;k<DEG;k++){ int t; do t=rnd()%ORD; while (inset(S,k,t)); S[k]=t; }
    for (int t=0;t<ORD;t++) tabu_until[t]=0;
    long c=cost_S(S), best=c; memcpy(Sout,S,sizeof S);
    for (long st=0; st<steps && best>0; st++){
        long bc=-1; int bk=-1, bt=-1;
        for (int s=0;s<samp;s++){
            int k=rnd()%DEG, t=rnd()%ORD; if (inset(S,DEG,t)) continue;
            int old=S[k]; S[k]=t; long c2=cost_S(S); S[k]=old;
            if (tabu_until[t]>st && c2>=best) continue;
            if (bc<0 || c2<bc || (c2==bc && (rnd()&1))){ bc=c2; bk=k; bt=t; }
        }
        if (bk<0) continue;
        tabu_until[S[bk]] = st + 12;
        S[bk]=bt; c=bc;
        if (c<best){ best=c; memcpy(Sout,S,sizeof S); fprintf(stderr,"tabu step %ld best %ld\n",st,best); }
    }
    return best==0;
}

static int adjH[NH*DEG];
static int EA[NH*DEG/2], EB[NH*DEG/2], nE=0;

static long cost_M(const int *MA, const int *MB){
    static int adj[NI*DEG];
    memcpy(adj, adjH, sizeof(int)*NH*DEG);
    for (int i=0;i<DEG;i++){
        int a=MA[i], b=MB[i];
        for (int k=0;k<DEG;k++) if (adj[a*DEG+k]==b){ adj[a*DEG+k]=685; break; }
        for (int k=0;k<DEG;k++) if (adj[b*DEG+k]==a){ adj[b*DEG+k]=684; break; }
    }
    for (int i=0;i<DEG;i++){ adj[684*DEG+i]=MB[i]; adj[685*DEG+i]=MA[i]; }
    return bad_pairs(NI, adj);
}

static void write_graph(const char *fn, const int *MA, const int *MB){
    static int adj[NI*DEG];
    memcpy(adj, adjH, sizeof(int)*NH*DEG);
    for (int i=0;i<DEG;i++){
        int a=MA[i], b=MB[i];
        for (int k=0;k<DEG;k++) if (adj[a*DEG+k]==b){ adj[a*DEG+k]=685; break; }
        for (int k=0;k<DEG;k++) if (adj[b*DEG+k]==a){ adj[b*DEG+k]=684; break; }
    }
    for (int i=0;i<DEG;i++){ adj[684*DEG+i]=MB[i]; adj[685*DEG+i]=MA[i]; }
    FILE *f=fopen(fn,"w"); fprintf(f,"%d\n",NI);
    for (int v=0; v<NI; v++) for (int k=0;k<DEG;k++){ int w=adj[v*DEG+k]; if (v<w) fprintf(f,"%d %d\n",v,w); }
    fclose(f);
}

int main(int argc, char **argv){
    if (argc<5){ fprintf(stderr,"usage: c7ins SEED ITERS_S ITERS_M OUTPREFIX\n"); return 1; }
    rs = strtoull(argv[1],0,10)*7919ULL + 12345ULL;
    long itS = atol(argv[2]), itM = atol(argv[3]);
    build_group();
    int S[DEG];
    if (!find_S(itS, S) && !find_S_tabu(TABU_STEPS, 400, S)){ printf("no 684 Haar graph found in S-anneal\n"); return 0; }
    printf("S (group elements c*57+a*3+b):"); for (int k=0;k<DEG;k++) printf(" %d",S[k]); printf("\n");
    build_haar(S, adjH);
    printf("calibration cost of H(G,S) = %ld (must be 0)\n", bad_pairs(NH, adjH));
    /* list the edges of H */
    nE=0; for (int g=0; g<ORD; g++) for (int k=0;k<DEG;k++){ EA[nE]=g; EB[nE]=adjH[g*DEG+k]; nE++; }

    int MA[DEG], MB[DEG];
    /* random initial matching */
    for (int i=0;i<DEG;i++){
        for (;;){ int e=rnd()%nE; int a=EA[e], b=EB[e], ok=1;
            for (int j=0;j<i;j++) if (MA[j]==a || MB[j]==b) ok=0;
            if (ok){ MA[i]=a; MB[i]=b; break; } }
    }
    long c=cost_M(MA,MB), best=c; int BA[DEG], BB2[DEG]; memcpy(BA,MA,sizeof MA); memcpy(BB2,MB,sizeof MB);
    printf("initial M cost %ld\n", c); fflush(stdout);
    for (long it=0; it<itM && best>0; it++){
        double T = 4.0*pow(0.02,(double)it/itM)+0.05;
        int i=rnd()%DEG, e=rnd()%nE, a=EA[e], b=EB[e], ok=1;
        for (int j=0;j<DEG;j++) if (j!=i && (MA[j]==a || MB[j]==b)) { ok=0; break; }
        if (!ok) continue;
        int oa=MA[i], ob=MB[i]; MA[i]=a; MB[i]=b;
        long c2=cost_M(MA,MB);
        if (c2<=c || urand() < exp(-(double)(c2-c)/T)){
            c=c2;
            if (c<best){ best=c; memcpy(BA,MA,sizeof MA); memcpy(BB2,MB,sizeof MB); }
        } else { MA[i]=oa; MB[i]=ob; }
        if (it%50000==0){ fprintf(stderr,"M it %ld T %.3f cur %ld best %ld\n",it,T,c,best); }
    }
    printf("best insertion cost (bad pairs at 686 vertices) = %ld\n", best);
    char fn[512]; snprintf(fn,sizeof fn,"%s_best.edges",argv[4]);
    write_graph(fn, BA, BB2);
    printf("wrote %s\n", fn);
    return 0;
}
