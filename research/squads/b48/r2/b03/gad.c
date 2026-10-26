// b03: insertion gadgets on a valid 2184-vertex bipartite degree-4 seed.
// Delete k edges a_i b_i; add x (side A) and y (side B). x attaches to a subset of the b_i (xa[i]),
// y attaches to a subset of the a_i (ya[i]), optional x-y edge (xy). Degrees must stay <= 4.
// Cost = unordered far pairs (distance > 8) on the new n = 2186 graph, via bitset BFS to depth 8.
// usage: gad SEED k SECONDS RNG mode(0 sample,1 anneal) fixxy(-1 rand,0,1) OUT T0 T1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define NMAX 2200
#define WMAX 36
#define BIG (1<<30)
static int n0, ne0, N, W;
static int eu[5000], ev[5000], ea[5000], eb[5000];
static int colr[NMAX];
static int sadj[NMAX][4], sdeg[NMAX], seid[NMAX][4];
static int adj[NMAX][4], deg[NMAX];
static uint64_t R0[NMAX][WMAX], R1[NMAX][WMAX];
static int pv[NMAX], curpv[NMAX];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int rndi(int m){ return (int)(rnd()%(uint64_t)m); }
static inline double rndf(void){ return (double)(rnd()>>11)*(1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
typedef struct { int k; int D[8]; int xa[8], ya[8]; int xy; } Cfg;

static int has(int u,int v){ for(int j=0;j<deg[u];j++) if(adj[u][j]==v) return 1; return 0; }
static int addE(int u,int v){ if(deg[u]>=4||deg[v]>=4||has(u,v)) return 0; adj[u][deg[u]++]=v; adj[v][deg[v]++]=u; return 1; }
static void delOne(int u,int v){ for(int j=0;j<deg[u];j++) if(adj[u][j]==v){ adj[u][j]=adj[u][--deg[u]]; return; } }
static int build(const Cfg *c){
  memcpy(adj,sadj,sizeof sadj); memcpy(deg,sdeg,sizeof sdeg);
  for(int v=n0; v<N; v++) deg[v]=0;
  for(int i=0;i<c->k;i++){ int e=c->D[i]; delOne(ea[e],eb[e]); delOne(eb[e],ea[e]); }
  int x=n0, y=n0+1;
  for(int i=0;i<c->k;i++){ int e=c->D[i];
    if(c->xa[i] && !addE(x,eb[e])) return 0;
    if(c->ya[i] && !addE(y,ea[e])) return 0; }
  if(c->xy && !addE(x,y)) return 0;
  return 1;
}
static int evalc(const Cfg *c){
  if(!build(c)) return BIG;
  for(int v=0; v<N; v++){
    memset(R0[v],0,sizeof R0[v]);
    R0[v][v>>6] |= 1ULL<<(v&63);
    for(int j=0;j<deg[v];j++){ int u=adj[v][j]; R0[v][u>>6] |= 1ULL<<(u&63); }
  }
  uint64_t (*cur)[WMAX]=R0, (*nxt)[WMAX]=R1;
  for(int d=2; d<=8; d++){
    for(int v=0; v<N; v++){
      memcpy(nxt[v], cur[v], W*8);
      for(int j=0;j<deg[v];j++){ int u=adj[v][j]; for(int w=0;w<W;w++) nxt[v][w] |= cur[u][w]; }
    }
    uint64_t (*t)[WMAX]=cur; cur=nxt; nxt=t;
  }
  long tot=0;
  for(int v=0; v<N; v++){ int c2=0; for(int w=0;w<W;w++) c2+=__builtin_popcountll(cur[v][w]); pv[v]=N-c2; tot+=N-c2; }
  return (int)(tot/2);
}
static int inD(const Cfg *c,int e){ for(int i=0;i<c->k;i++) if(c->D[i]==e) return 1; return 0; }
static void randcfg(Cfg *c,int k,int fixxy){
  c->k=k;
  for(int i=0;i<k;i++){ int e; do{ e=rndi(ne0);}while(inD(c,e)); c->D[i]=e; }
  for(int i=0;i<k;i++){ c->xa[i]=rndi(2); c->ya[i]=rndi(2); }
  c->xy = fixxy<0 ? rndi(2) : fixxy;
}
static void mutate(Cfg *c,int fixxy){
  double r=rndf();
  if(r<0.3){ int i=rndi(c->k); int e; do{ e=rndi(ne0);}while(inD(c,e)); c->D[i]=e; }
  else if(r<0.5){ // targeted: start at a far-pair vertex, walk <=2 seed steps, delete an edge there
    int v, tries=0; do{ v=rndi(N); tries++; }while((v>=n0 || curpv[v]==0) && tries<100000);
    if(v>=n0) v=rndi(n0);
    int w=v, st=rndi(3);
    for(int s=0;s<st;s++) w=sadj[w][rndi(4)];
    int e=seid[w][rndi(4)];
    if(!inD(c,e)){ c->D[rndi(c->k)]=e; }
  }
  else if(r<0.7){ c->xa[rndi(c->k)]^=1; }
  else if(r<0.9){ c->ya[rndi(c->k)]^=1; }
  else if(fixxy<0){ c->xy^=1; }
}
static void writeout(const char *out,const Cfg *c){
  build(c);
  char fn[512]; snprintf(fn,sizeof fn,"%s.edges",out);
  FILE *f=fopen(fn,"w"); fprintf(f,"%d\n",N);
  for(int v=0;v<N;v++) for(int j=0;j<deg[v];j++) if(adj[v][j]>v) fprintf(f,"%d %d\n",v,adj[v][j]);
  fclose(f);
  f=fopen(out,"w");
  fprintf(f,"k=%d xy=%d\n",c->k,c->xy);
  for(int i=0;i<c->k;i++){ int e=c->D[i]; fprintf(f,"del a=%d b=%d xa=%d ya=%d\n",ea[e],eb[e],c->xa[i],c->ya[i]); }
  fclose(f);
}
static void printcfg(const Cfg *c){
  printf("k=%d xy=%d",c->k,c->xy);
  for(int i=0;i<c->k;i++){ int e=c->D[i]; printf(" [a%d b%d xa%d ya%d]",ea[e],eb[e],c->xa[i],c->ya[i]); }
  printf("\n");
}
int main(int argc,char **argv){
  if(argc<10){ fprintf(stderr,"usage: gad SEED k SECONDS RNG mode fixxy OUT T0 T1\n"); return 1; }
  int k=atoi(argv[2]); double secs=atof(argv[3]); rs ^= (uint64_t)atoll(argv[4])*0x9E3779B97F4A7C15ULL; if(!rs) rs=1;
  int mode=atoi(argv[5]), fixxy=atoi(argv[6]); const char *out=argv[7];
  double T0=atof(argv[8]), T1=atof(argv[9]);
  FILE *f=fopen(argv[1],"r"); if(!f){perror("seed"); return 1;}
  if(fscanf(f,"%d",&n0)!=1) return 1;
  ne0=0; while(fscanf(f,"%d %d",&eu[ne0],&ev[ne0])==2) ne0++;
  fclose(f);
  N=n0+2; W=(N+63)/64;
  memset(sdeg,0,sizeof sdeg);
  for(int e=0;e<ne0;e++){ int u=eu[e], v=ev[e]; sadj[u][sdeg[u]]=v; seid[u][sdeg[u]++]=e; sadj[v][sdeg[v]]=u; seid[v][sdeg[v]++]=e; }
  for(int v=0;v<n0;v++) if(sdeg[v]!=4){ fprintf(stderr,"seed not 4-regular\n"); return 1; }
  for(int v=0;v<n0;v++) colr[v]=-1;
  int q[NMAX], qh=0, qt=0; colr[0]=0; q[qt++]=0;
  while(qh<qt){ int u=q[qh++]; for(int j=0;j<4;j++){ int v=sadj[u][j]; if(colr[v]<0){ colr[v]=1-colr[u]; q[qt++]=v; } else if(colr[v]==colr[u]){ fprintf(stderr,"not bipartite\n"); return 1; } } }
  for(int e=0;e<ne0;e++){ if(colr[eu[e]]==0){ ea[e]=eu[e]; eb[e]=ev[e]; } else { ea[e]=ev[e]; eb[e]=eu[e]; } }
  Cfg cur, cand, best; int bestc=BIG;
  double t0=now();
  if(mode==0){
    int hist[64]={0}; int S=0; int mn=BIG; double sum=0;
    while(now()-t0<secs){
      Cfg c; randcfg(&c,k,fixxy); int v=evalc(&c);
      if(v>=BIG) continue; S++; sum+=v; if(v<mn){ mn=v; best=c; }
      int b = v<640 ? v/10 : 63; hist[b]++;
    }
    printf("sample k=%d fixxy=%d valid_samples=%d min_far=%d mean_far=%.1f\n",k,fixxy,S,mn,S?sum/S:0);
    printcfg(&best);
    if(mn<BIG){ evalc(&best); writeout(out,&best); }
    return 0;
  }
  // anneal
  do{ randcfg(&cur,k,fixxy); } while(evalc(&cur)>=BIG);
  double cc=evalc(&cur); memcpy(curpv,pv,sizeof pv); best=cur; bestc=(int)cc;
  long it=0, acc=0;
  while(now()-t0<secs){
    cand=cur; mutate(&cand,fixxy); it++;
    int cn=evalc(&cand); if(cn>=BIG) continue;
    double frac=(now()-t0)/secs; double T=T0*pow(T1/T0,frac);
    if(cn<=cc || rndf()<exp(-(cn-cc)/T)){
      cur=cand; cc=cn; memcpy(curpv,pv,sizeof pv); acc++;
      if(cn<bestc){ bestc=cn; best=cur; printf("it=%ld t=%.1f best_far=%d ",it,now()-t0,bestc); printcfg(&best); fflush(stdout); }
    }
  }
  printf("done it=%ld acc=%ld best_far=%d ",it,acc,bestc); printcfg(&best);
  if(bestc<BIG){ evalc(&best); writeout(out,&best); }
  return 0;
}
