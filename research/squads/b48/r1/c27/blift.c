/* c27: anneal voltages of a general base (4-regular, bipartite) lifted by a small group G (table file).
   Bit-parallel cost: bit u of R_t[p] = dist((u,e), p) <= t, roots = base vertices (u,e).
   cost = b*n - sum_p popcount(R_8[p])  (== lift tool cost).
   Usage: blift BASE GTABLE seconds seed T0 T1 OUT
   GTABLE: text "N" then N rows of N ints (mul table, identity 0). Writes OUT (n then "u v" lift edges) and OUT.volt. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXE 4096
#define MAXB 4096
static int b, m, G, n, W, D = 8;
static int eu[MAXE], ev[MAXE], volt[MAXE], istree[MAXE];
static int mul[64][64], inv[64];
static int incOther[MAXB][4], incE[MAXB][4], incFwd[MAXB][4];
static uint64_t *R0, *R1;
static int *nbrs; /* lift adjacency: nbrs[p*4+k] */
static int nb_cnt[MAXB*64];
static uint64_t rng;
static inline uint64_t xr(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

static void build_nbrs(void){
    for(int u=0;u<b;u++) for(int x=0;x<G;x++){
        int p=u*G+x;
        for(int k=0;k<4;k++){
            int o=incOther[u][k], e=incE[u][k];
            int y = incFwd[u][k] ? mul[x][volt[e]] : mul[x][inv[volt[e]]];
            nbrs[p*4+k]=o*G+y;
        }
    }
}
static long long cost_eval(void){
    /* init */
    memset(R0,0,sizeof(uint64_t)*n*W);
    for(int u=0;u<b;u++){ int p=u*G; R0[(size_t)p*W + (u>>6)] |= 1ULL<<(u&63); }
    for(int t=0;t<D;t++){
        for(int p=0;p<n;p++){
            uint64_t *dst=R1+(size_t)p*W, *src=R0+(size_t)p*W;
            for(int w=0;w<W;w++) dst[w]=src[w];
            for(int k=0;k<4;k++){
                uint64_t *q=R0+(size_t)nbrs[p*4+k]*W;
                for(int w=0;w<W;w++) dst[w]|=q[w];
            }
        }
        uint64_t *tmp=R0; R0=R1; R1=tmp;
    }
    long long cov=0;
    for(int p=0;p<n;p++) for(int w=0;w<W;w++) cov+=__builtin_popcountll(R0[(size_t)p*W+w]);
    return (long long)b*n - cov;
}
int main(int argc,char**argv){
    if(argc<8){fprintf(stderr,"usage: blift BASE GTABLE seconds seed T0 T1 OUT\n");return 2;}
    FILE*f=fopen(argv[1],"r"); if(!f){perror("base");return 1;}
    if(fscanf(f,"%d %d",&b,&m)!=2) return 1;
    for(int e=0;e<m;e++){ if(fscanf(f,"%d %d",&eu[e],&ev[e])!=2) return 1; }
    fclose(f);
    f=fopen(argv[2],"r"); if(!f){perror("gtable");return 1;}
    if(fscanf(f,"%d",&G)!=1) return 1;
    for(int i=0;i<G;i++) for(int j=0;j<G;j++) if(fscanf(f,"%d",&mul[i][j])!=1) return 1;
    fclose(f);
    for(int i=0;i<G;i++) for(int j=0;j<G;j++) if(mul[i][j]==0) inv[i]=j;
    /* base degree check and incidence */
    int deg[MAXB]; memset(deg,0,sizeof deg);
    for(int e=0;e<m;e++){ 
        int u=eu[e], v=ev[e];
        incOther[u][deg[u]]=v; incE[u][deg[u]]=e; incFwd[u][deg[u]]=1; deg[u]++;
        incOther[v][deg[v]]=u; incE[v][deg[v]]=e; incFwd[v][deg[v]]=0; deg[v]++;
    }
    for(int u=0;u<b;u++) if(deg[u]!=4){fprintf(stderr,"base vertex %d has degree %d\n",u,deg[u]);return 1;}
    /* spanning tree (BFS from 0): tree edges voltage identity */
    int seen[MAXB]; memset(seen,0,sizeof seen); int qq[MAXB],qh=0,qt=0; qq[qt++]=0; seen[0]=1;
    memset(istree,0,sizeof istree);
    while(qh<qt){ int u=qq[qh++]; for(int k=0;k<4;k++){ int v=incOther[u][k]; if(!seen[v]){seen[v]=1; istree[incE[u][k]]=1; qq[qt++]=v;} } }
    double secs=atof(argv[3]); rng = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[4])*0xBF58476D1CE4E5B9ULL);
    double T0=atof(argv[5]), T1=atof(argv[6]); const char*out=argv[7];
    n=b*G; W=(b+63)/64;
    R0=malloc(sizeof(uint64_t)*n*W); R1=malloc(sizeof(uint64_t)*n*W); nbrs=malloc(sizeof(int)*n*4);
    int freeE[MAXE], nf=0;
    for(int e=0;e<m;e++){ if(istree[e]) volt[e]=0; else { volt[e]=xr()%G; freeE[nf++]=e; } }
    build_nbrs();
    long long cur=cost_eval(), best=cur; int bestv[MAXE]; memcpy(bestv,volt,sizeof(int)*m);
    double t0=now(); long long ev_n=1;
    while(1){
        double el=now()-t0; if(el>secs) break;
        double frac=el/secs; double T=T0*pow(T1/T0,frac);
        int e=freeE[xr()%nf]; int old=volt[e]; int nv=(old+1+xr()%(G-1))%G;
        volt[e]=nv; build_nbrs();
        long long c=cost_eval(); ev_n++;
        long long d=c-cur;
        if(d<=0 || (double)(xr()%1000000)/1e6 < exp(-d/T)){ cur=c; if(c<best){best=c; memcpy(bestv,volt,sizeof(int)*m);} if(best==0) break; }
        else { volt[e]=old; build_nbrs(); }
    }
    memcpy(volt,bestv,sizeof(int)*m); build_nbrs();
    long long cc=cost_eval();
    printf("RESULT b=%d G=%d n=%d best=%lld miss=%.4f evals=%lld time=%.1f\n", b, G, n, cc, (double)cc/b, ev_n, now()-t0);
    /* write lift edge list */
    char buf[512]; sprintf(buf,"%s.edges",out);
    FILE*o=fopen(buf,"w"); fprintf(o,"%d\n",n);
    for(int e=0;e<m;e++) for(int x=0;x<G;x++) fprintf(o,"%d %d\n", eu[e]*G+x, ev[e]*G+mul[x][bestv[e]]);
    fclose(o);
    sprintf(buf,"%s.volt",out); o=fopen(buf,"w"); for(int e=0;e<m;e++) fprintf(o,"%d\n",bestv[e]); fclose(o);
    return cc==0?0:0;
}
