/* c6 (s384r3): optimise the insertion of new vertices into the 684 Haar record H(G,S), G = C6 x (C19:C3).
 * Mode 6 (c7 construction): delete a 6-matching M = {(a_i,b_i)} of H; u0 (=684) ~ all b_i, u1 (=685) ~ all a_i.
 * Mode 5: delete a 5-matching, same attachments for 5 pairs, plus edge u0-u1 (both degree 6).
 * Symmetry: G acts on H by left translation, transitively on the edges with a given label s in S, so WLOG the
 * matching contains the edge (identity, s_k) for some k; that edge is fixed and the other edges are annealed.
 * Cost = unordered vertex pairs at distance > 5 in the 686-vertex graph (exact bitset ball-5 count).
 * Usage: c6ins SEED SECONDS_PER_RUN RUNS MODE OUTPREFIX [S0 S1 S2 S3 S4 S5]
 *   If S is not given, S is found by tabu search (same as c7) on the 684 Haar graph.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ORD 342
#define NH 684
#define NI 686
#define MAXW 12
#define DEG 6

static int mulT[ORD][ORD], invT[ORD];
static uint64_t rs;
static uint64_t rnd(void){ uint64_t z=(rs+=0x9E3779B97F4A7C15ULL); z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL; z=(z^(z>>27))*0x94D049BB133111EBULL; return z^(z>>31); }
static double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

static void build_group(void){
    static const int pw[3]={1,7,11};
    for (int x=0;x<ORD;x++) for (int y=0;y<ORD;y++){
        int c1=x/57, a1=(x%57)/3, b1=x%3, c2=y/57, a2=(y%57)/3, b2=y%3;
        int c=(c1+c2)%6, a=(a1+pw[b1]*a2)%19, b=(b1+b2)%3;
        mulT[x][y]=c*57+a*3+b;
    }
    for (int x=0;x<ORD;x++) for (int y=0;y<ORD;y++) if (mulT[x][y]==0) invT[x]=y;
}

/* side-0 vertex g, side-1 vertex ORD+h; (g,0)~(h,1) iff h = g s */
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

/* tabu over S (as in c7): sampled neighbourhood, 400 random single-element swaps per step */
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
        if (c<best){ best=c; memcpy(Sout,S,sizeof S); }
    }
    return best==0;
}

static int adjH[NH*DEG];
static int EA[ORD*DEG], EB[ORD*DEG], nE=0;
static int K=6;   /* matched edges */

/* build the 686-vertex graph: u0 = 684 (adjacent to the b_i), u1 = 685 (adjacent to the a_i) */
static void build_ins(const int *MA, const int *MB, int *adj){
    memcpy(adj, adjH, sizeof(int)*NH*DEG);
    for (int i=0;i<K;i++){
        int a=MA[i], b=MB[i];
        for (int k=0;k<DEG;k++) if (adj[a*DEG+k]==b){ adj[a*DEG+k]=685; break; }
        for (int k=0;k<DEG;k++) if (adj[b*DEG+k]==a){ adj[b*DEG+k]=684; break; }
    }
    for (int i=0;i<K;i++){ adj[684*DEG+i]=MB[i]; adj[685*DEG+i]=MA[i]; }
    if (K==5){ adj[684*DEG+5]=685; adj[685*DEG+5]=684; }
}

static long cost_M(const int *MA, const int *MB){
    static int adj[NI*DEG];
    build_ins(MA, MB, adj);
    return bad_pairs(NI, adj);
}

static void write_graph(const char *fn, const int *MA, const int *MB){
    static int adj[NI*DEG];
    build_ins(MA, MB, adj);
    FILE *f=fopen(fn,"w"); if (!f){ fprintf(stderr,"cannot open %s\n",fn); exit(1); } fprintf(f,"%d\n",NI);
    for (int v=0; v<NI; v++) for (int k=0;k<DEG;k++){ int w=adj[v*DEG+k]; if (v<w) fprintf(f,"%d %d\n",v,w); }
    fclose(f);
}

static int disjoint_ok(const int *MA, const int *MB, int i, int a, int b){
    for (int j=0;j<K;j++) if (j!=i && (MA[j]==a || MB[j]==b)) return 0;
    return 1;
}

int main(int argc, char **argv){
    if (argc<6){ fprintf(stderr,"usage: c6ins SEED SECONDS_PER_RUN RUNS MODE OUTPREFIX [S0..S5]\n"); return 1; }
    rs = strtoull(argv[1],0,10)*7919ULL + 12345ULL;
    double secs = atof(argv[2]); int runs = atoi(argv[3]); int mode = atoi(argv[4]);
    const char *outp = argv[5];
    K = (mode==5) ? 5 : 6;
    build_group();
    int S[DEG];
    if (argc>=5+DEG){ for (int k=0;k<DEG;k++) S[k]=atoi(argv[6+k]); }
    else {
        if (!find_S_tabu(2000, 400, S)){ printf("no 684 Haar graph found\n"); return 0; }
    }
    printf("S:"); for (int k=0;k<DEG;k++) printf(" %d",S[k]); printf("\n");
    build_haar(S, adjH);
    printf("calibration bad(H) = %ld\n", bad_pairs(NH, adjH));
    nE=0; for (int g=0; g<ORD; g++) for (int k=0;k<DEG;k++){ EA[nE]=g; EB[nE]=adjH[g*DEG+k]; nE++; }

    long gbest=-1; int GA[DEG], GB[DEG];
    for (int run=0; run<runs && gbest!=0; run++){
        int k0 = run % DEG;   /* the fixed edge (identity, S[k0]) is in the matching */
        int MA[DEG], MB[DEG];
        MA[0]=0; MB[0]=ORD+S[k0];
        for (int i=1;i<K;i++){
            for (;;){ int e=rnd()%nE; int a=EA[e], b=EB[e];
                if (disjoint_ok(MA,MB,i,a,b)){ MA[i]=a; MB[i]=b; break; } }
        }
        long c=cost_M(MA,MB), best=c; int BA[DEG], BBm[DEG]; memcpy(BA,MA,sizeof MA); memcpy(BBm,MB,sizeof MB);
        double t0=now(), T0=8.0, T1=0.2; long it=0, acc=0;
        while (1){
            double el=now()-t0; if (el>=secs || best==0) break;
            double T = T0*pow(T1/T0, el/secs);
            int i=1+rnd()%(K-1), e=rnd()%nE, a=EA[e], b=EB[e];
            if (!disjoint_ok(MA,MB,i,a,b)) continue;
            int oa=MA[i], ob=MB[i]; MA[i]=a; MB[i]=b;
            long c2=cost_M(MA,MB); it++;
            if (c2<=c || urand() < exp(-(double)(c2-c)/T)){
                c=c2; acc++;
                if (c<best){ best=c; memcpy(BA,MA,sizeof MA); memcpy(BBm,MB,sizeof MB); }
            } else { MA[i]=oa; MB[i]=ob; }
        }
        printf("run %d k0 %d (S[k0]=%d) iters %ld acc %ld best %ld\n", run, k0, S[k0], it, acc, best);
        fflush(stdout);
        if (gbest<0 || best<gbest){ gbest=best; memcpy(GA,BA,sizeof BA); memcpy(GB,BBm,sizeof BBm); }
    }
    printf("best insertion cost (bad pairs at 686 vertices) = %ld\n", gbest);
    printf("matching A:"); for (int i=0;i<K;i++) printf(" %d",GA[i]); printf("\nmatching B:"); for (int i=0;i<K;i++) printf(" %d",GB[i]); printf("\n");
    char fn[512]; snprintf(fn,sizeof fn,"%s_best.edges",outp);
    write_graph(fn, GA, GB);
    printf("wrote %s\n", fn);
    return 0;
}
