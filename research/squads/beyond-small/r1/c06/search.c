/* c06: route-chart lift of the (16,5) controller with one extra fibre translation e_k on each edge k of a
   base perfect matching M (so degree 17). Base = K33 + doubled matching (12 base edges), voltage lift by Z_N.
   Fibre F4^4, id = sum_t comp_t 4^t, addition = XOR.  Lift edge: ((i,g),x) ~ ((j,g+v_k),A_c x + w),
   w in F4 b_c (+ e_k if k in M).  Vertex numbering as build_d16D5_n33792.py.
   usage: search mode N seed seconds K T0 T1 statefile outprefix
     mode=check : N=22 builder data, M empty, expects full cost 0 (calibration).
     mode=anneal: simulated annealing over v, letters c, matching M, e's; cost = uncovered ordered pairs
                  summed over K fibre sources per base type (Z_N symmetry: sources have g=0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NB 12
#define STRIDE 17
#define FIB 256

static const int MULT[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static const int AM[4][4][4] = {
 {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}},
 {{0,1,3,0},{1,0,2,3},{3,2,1,3},{1,2,3,1}},
 {{0,1,3,2},{3,0,2,3},{0,3,1,2},{0,1,0,3}},
 {{1,0,3,3},{1,0,3,0},{0,0,1,1},{2,3,1,2}}};
static const int BV[4][4] = {{1,2,0,2},{0,1,1,2},{1,0,0,2},{0,1,3,2}};
static const int BI[NB]  = {0,0,0,0,1,1,1,1,2,2,2,2};
static const int BJ[NB]  = {0,0,1,2,1,1,0,2,2,2,0,1};
static const int BV0[NB] = {0,15,0,0,7,3,0,19,6,17,0,8};
static const int BC[NB]  = {0,2,1,3,0,2,3,1,0,2,1,3};
static const int PA[3][2] = {{0,1},{4,5},{8,9}};

static int N, nA, nV, nMS;
static int MS[64][3];
static int AX[4][FIB], LAMB[4][4], invc[4];
static int *adj, *mark, *qb, nsrc, *srcs, D = 17, stampc = 0;
static unsigned char *dg;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int rndi(int n){ return (int)(rnd()%(uint64_t)n); }
static double rnd01(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

typedef struct { int v[NB], c[NB], M, e[NB]; } State;

static int vecmulb(int lam,int c){ int r=0; for(int t=0;t<4;t++) r|=MULT[lam][BV[c][t]]<<(2*t); return r; }
static int matvec(int c,int x){
    int r=0;
    for(int row=0;row<4;row++){ int s=0; for(int t=0;t<4;t++) s^=MULT[AM[c][row][t]][(x>>(2*t))&3]; r|=s<<(2*row); }
    return r;
}
static void init_tables(void){
    for(int c=0;c<4;c++){
        int seen[FIB]; memset(seen,0,sizeof seen); int ok=1;
        for(int x=0;x<FIB;x++){ AX[c][x]=matvec(c,x); if(seen[AX[c][x]]) ok=0; seen[AX[c][x]]=1; }
        invc[c]=ok;
        for(int l=0;l<4;l++) LAMB[c][l]=vecmulb(l,c);
    }
    nMS=0;
    for(int a=0;a<NB;a++) for(int b=a+1;b<NB;b++) for(int c=b+1;c<NB;c++){
        int id[3][2]={{BI[a],3+BJ[a]},{BI[b],3+BJ[b]},{BI[c],3+BJ[c]}};
        int used[6]={0,0,0,0,0,0}, ok=1;
        for(int q=0;q<3;q++) for(int r=0;r<2;r++){ if(used[id[q][r]]) ok=0; used[id[q][r]]=1; }
        if(ok){ MS[nMS][0]=a; MS[nMS][1]=b; MS[nMS][2]=c; nMS++; }
    }
}
static int evalid_for(int e,int c){ for(int l=0;l<4;l++) if(LAMB[c][l]==e) return 0; return 1; }
static int pick_e(int c){ int e; do{ e=rndi(FIB); }while(!evalid_for(e,c)); return e; }
static int inMk(const State*s,int k){ if(s->M<0) return 0; for(int t=0;t<3;t++) if(MS[s->M][t]==k) return 1; return 0; }

static int valid(const State*s){
    for(int p=0;p<3;p++) if(s->v[PA[p][0]]==s->v[PA[p][1]]) return 0;
    for(int k=0;k<NB;k++){ if(s->v[k]<0||s->v[k]>=N) return 0; if(!invc[s->c[k]]) return 0; }
    if(s->M>=0) for(int t=0;t<3;t++){ int k=MS[s->M][t]; if(!evalid_for(s->e[k],s->c[k])) return 0; }
    return 1;
}

static int build(const State*s){
    nA = 3*N*FIB; nV = 2*nA;
    memset(dg,0,(size_t)nV);
    int inM[NB]={0,0,0,0,0,0,0,0,0,0,0,0};
    if(s->M>=0) for(int t=0;t<3;t++) inM[MS[s->M][t]]=1;
    for(int k=0;k<NB;k++){
        int i=BI[k], j=BJ[k], v=s->v[k], c=s->c[k];
        int ws[5], nw=0;
        for(int l=0;l<4;l++) ws[nw++]=LAMB[c][l];
        if(inM[k]) ws[nw++]=s->e[k];
        for(int g=0;g<N;g++){
            int hg=(g+v)%N;
            for(int x=0;x<FIB;x++){
                int a=(i*N+g)*FIB+x, ax=AX[c][x];
                for(int t=0;t<nw;t++){
                    int b=nA+(j*N+hg)*FIB+(ax^ws[t]);
                    if(dg[a]>=STRIDE||dg[b]>=STRIDE) return 0;
                    adj[(size_t)a*STRIDE+dg[a]++]=b;
                    adj[(size_t)b*STRIDE+dg[b]++]=a;
                }
            }
        }
    }
    int want=(s->M>=0)?17:16;
    for(int u=0;u<nV;u++) if(dg[u]!=want) return 0;
    D=want;
    return 1;
}

static long bfs_unc(int src){
    stampc++;
    int head=0, tail=0, start=0, depth=0;
    qb[tail++]=src; mark[src]=stampc; (void)head;
    while(depth<5){
        int end=tail; if(start==end) break;
        for(int q=start;q<end;q++){
            const int*au=adj+(size_t)qb[q]*STRIDE;
            for(int t=0;t<D;t++){ int w=au[t]; if(mark[w]!=stampc){ mark[w]=stampc; qb[tail++]=w; } }
        }
        start=end; depth++;
    }
    return nV-tail;
}
static uint64_t *rA, *rB;
/* bit-parallel BFS: 64 sources per pass, depth <= 5; returns sum over sources of vertices at distance > 5 */
static long cost_src(void){
    if(!rA){ rA=malloc(sizeof(uint64_t)*nV); rB=malloc(sizeof(uint64_t)*nV); }
    long total=0;
    for(int base=0;base<nsrc;base+=64){
        int nb=nsrc-base<64?nsrc-base:64;
        memset(rA,0,sizeof(uint64_t)*nV);
        for(int b=0;b<nb;b++) rA[srcs[base+b]] |= (uint64_t)1<<b;
        for(int dep=0;dep<5;dep++){
            for(int v=0;v<nV;v++){
                uint64_t acc=rA[v];
                const int*av=adj+(size_t)v*STRIDE;
                for(int t=0;t<D;t++) acc|=rA[av[t]];
                rB[v]=acc;
            }
            uint64_t*tmp=rA; rA=rB; rB=tmp;
        }
        long reached=0;
        for(int v=0;v<nV;v++) reached+=__builtin_popcountll(rA[v]);
        total += (long)nb*nV - reached;
    }
    return total;
}
static void make_sources(int K){
    nsrc=0; free(srcs); srcs=malloc(sizeof(int)*6*FIB);
    for(int t=0;t<6;t++){
        int perm[FIB]; for(int x=0;x<FIB;x++) perm[x]=x;
        for(int x=FIB-1;x>0;x--){ int y=rndi(x+1); int tmp=perm[x]; perm[x]=perm[y]; perm[y]=tmp; }
        for(int q=0;q<K;q++){
            int x=perm[q];
            srcs[nsrc++] = (t<3) ? (t*N)*FIB+x : nA+((t-3)*N)*FIB+x;
        }
    }
}

static void write_state(const char*fn,const State*s){
    FILE*f=fopen(fn,"w"); if(!f) return;
    fprintf(f,"%d %d\n",N,s->M);
    for(int k=0;k<NB;k++) fprintf(f,"%d %d %d\n",s->v[k],s->c[k],s->e[k]);
    fclose(f);
}
static int read_state(const char*fn,State*s){
    FILE*f=fopen(fn,"r"); if(!f) return 0;
    int n; if(fscanf(f,"%d %d",&n,&s->M)!=2){ fclose(f); return 0; }
    if(n!=N){ fclose(f); return 0; }
    for(int k=0;k<NB;k++) if(fscanf(f,"%d %d %d",&s->v[k],&s->c[k],&s->e[k])!=3){ fclose(f); return 0; }
    fclose(f); return 1;
}
static void write_edges(const char*fn){
    FILE*f=fopen(fn,"w"); if(!f) return;
    fprintf(f,"%d\n",nV);
    for(int u=0;u<nV;u++) for(int t=0;t<D;t++){ int w=adj[(size_t)u*STRIDE+t]; if(w>u) fprintf(f,"%d %d\n",u,w); }
    fclose(f);
}

static void mutate(State*s){
    int r=rndi(100);
    if(r<40){ int k=rndi(NB); s->v[k]=rndi(N); }
    else if(r<55){
        int k=rndi(NB); s->c[k]=rndi(4);
        if(inMk(s,k) && !evalid_for(s->e[k],s->c[k])) s->e[k]=pick_e(s->c[k]);
    }
    else if(r<72){
        int m=rndi(nMS); s->M=m;
        for(int t=0;t<3;t++){ int k=MS[m][t]; if(!evalid_for(s->e[k],s->c[k])) s->e[k]=pick_e(s->c[k]); }
    }
    else if(s->M>=0){
        int k=MS[s->M][rndi(3)];
        if(rnd()&1){ s->e[k]=pick_e(s->c[k]); }
        else { s->e[k]^=1<<rndi(8); if(!evalid_for(s->e[k],s->c[k])) s->e[k]=pick_e(s->c[k]); }
    }
}

int main(int argc,char**argv){
    if(argc<10){ fprintf(stderr,"usage: search mode N seed seconds K T0 T1 statefile outprefix\n"); return 1; }
    const char*mode=argv[1];
    N=atoi(argv[2]); rs ^= (uint64_t)atoll(argv[3])*0x2545F4914F6CDD1DULL; for(int i=0;i<10;i++) rnd();
    double limit=atof(argv[4]); int K=atoi(argv[5]); double T0=atof(argv[6]), T1=atof(argv[7]);
    const char*sfn=argv[8], *outp=argv[9];
    init_tables();
    for(int c=0;c<4;c++) if(!invc[c]){ fprintf(stderr,"letter %d not invertible\n",c); return 1; }
    nA=3*N*FIB; nV=2*nA;
    adj=malloc(sizeof(int)*(size_t)nV*STRIDE); mark=calloc(nV,sizeof(int)); qb=malloc(sizeof(int)*nV);
    dg=malloc(nV);
    srand(1);
    make_sources(FIB);  /* full sources for final checks */
    int *fullsrc=srcs; int fullns=nsrc; srcs=NULL;
    State cur, best;
    if(!strcmp(mode,"check")){
        State s; memset(&s,0,sizeof s); s.M=-1;
        for(int k=0;k<NB;k++){ s.v[k]=BV0[k]; s.c[k]=BC[k]; }
        srcs=fullsrc; nsrc=fullns;
        if(!build(&s)){ printf("RESULT build failed\n"); return 1; }
        long c=cost_src();
        printf("check N=%d D=%d full_cost=%ld\n",N,D,c);
        if(c==0){ write_edges(outp); printf("wrote %s\n",outp); }
        return 0;
    }
    /* anneal */
    srcs=NULL; make_sources(K);
    if(!read_state(sfn,&cur)){
        int ok=0;
        for(int tries=0;tries<100000&&!ok;tries++){
            memset(&cur,0,sizeof cur);
            cur.M=rndi(nMS);
            for(int k=0;k<NB;k++){ cur.v[k]=BV0[k]%N; cur.c[k]=BC[k]; cur.e[k]=0; }
            for(int k=0;k<NB;k++) if(inMk(&cur,k)) cur.e[k]=pick_e(cur.c[k]);
            if(rndi(2)) for(int k=0;k<NB;k++) cur.v[k]=rndi(N);
            ok = valid(&cur) && build(&cur);
        }
        if(!ok){ printf("RESULT no valid start\n"); return 1; }
    } else {
        if(!valid(&cur)||!build(&cur)){ printf("RESULT bad state file\n"); return 1; }
    }
    long curc=cost_src(); long bestc=curc; best=cur;
    double t0=now(); long it=0, acc=0;
    printf("start cost(sample K=%d)=%ld\n",K,curc); fflush(stdout);
    while(bestc>0){
        double el=now()-t0; if(el>limit) break;
        double T=T0*pow(T1/T0, el/limit);
        State cand=cur; mutate(&cand);
        if(!valid(&cand)) continue;
        if(!build(&cand)) continue;
        long cc=cost_src(); it++;
        if(cc<=curc || rnd01()<exp(-(double)(cc-curc)/T)){
            cur=cand; curc=cc; acc++;
            if(cc<bestc){ bestc=cc; best=cur; }
        }
    }
    printf("iters=%ld acc=%ld best_sample_cost=%ld cur=%ld\n",it,acc,bestc,curc);
    write_state(sfn,&best);
    if(!build(&best)){ printf("RESULT best rebuild failed\n"); return 1; }
    srcs=fullsrc; nsrc=fullns;
    long full=cost_src();
    printf("best full cost (all 1536 sources)=%ld  M=%d e=",full,best.M);
    for(int t=0;t<3&&best.M>=0;t++){ int k=MS[best.M][t]; printf("[k%d v%d c%d e%d] ",k,best.v[k],best.c[k],best.e[k]); }
    printf("\n");
    if(full==0){ write_edges(outp); printf("wrote %s n=%d\n",outp,nV); }
    return 0;
}
