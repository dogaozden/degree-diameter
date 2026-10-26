// c31: grow the 2184 seed by adding x (side A) and y (side B), then 2-switch simulated annealing
// on the number of unordered far pairs (distance > 8). Bit-parallel ball computation.
// usage: grow SEED.edges SECONDS RNGSEED T0 T1 OUT.edges [INIT_TRIPLE_SEED]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#define MAXN 2200
#define W 35   /* 35*64 = 2240 >= 2186 */
#define D 8
static int N;                 /* current vertex count */
static int adj[MAXN][4];
static int deg[MAXN];
static int side[MAXN];
static uint64_t bufA[MAXN][W], bufB[MAXN][W];
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

static long far_pairs(void){
  uint64_t (*cur)[W] = bufA, (*nxt)[W] = bufB;
  memset(cur,0,sizeof(bufA));
  for(int v=0;v<N;v++) cur[v][v>>6] |= 1ULL<<(v&63);
  for(int k=0;k<D;k++){
    for(int v=0;v<N;v++){
      uint64_t *o = nxt[v];
      memcpy(o, cur[v], W*8);
      for(int t=0;t<deg[v];t++){
        uint64_t *s = cur[adj[v][t]];
        for(int w=0;w<W;w++) o[w] |= s[w];
      }
    }
    uint64_t (*tmp)[W] = cur; cur = nxt; nxt = tmp;
  }
  long tot=0;
  for(int v=0;v<N;v++){
    long c=0; for(int w=0;w<W;w++) c += __builtin_popcountll(cur[v][w]);
    tot += N - c;
  }
  return tot/2;
}

static int has_edge(int a,int b){ for(int t=0;t<deg[a];t++) if(adj[a][t]==b) return 1; return 0; }
static void repl(int u,int old,int nw){ for(int t=0;t<deg[u];t++) if(adj[u][t]==old){ adj[u][t]=nw; return; } fprintf(stderr,"repl fail\n"); exit(1); }

/* edges as pairs (A-vertex, B-vertex) */
static int EA[MAXN*2], EB[MAXN*2], M;
static void do_switch(int i,int j){
  /* (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) */
  int a1=EA[i], b1=EB[i], a2=EA[j], b2=EB[j];
  repl(a1,b1,b2); repl(b1,a1,a2); repl(a2,b2,b1); repl(b2,a2,a1);
  EB[i]=b2; EB[j]=b1;
}

int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage\n"); return 1; }
  FILE *f=fopen(argv[1],"r"); int n0; if(fscanf(f,"%d",&n0)!=1) return 1;
  static int E0u[MAXN*2],E0v[MAXN*2]; int m0=0;
  while(fscanf(f,"%d %d",&E0u[m0],&E0v[m0])==2) m0++;
  fclose(f);
  double secs=atof(argv[2]); rs = strtoull(argv[3],0,10)*2654435761ULL+88172645463325252ULL;
  double T0=atof(argv[4]), T1=atof(argv[5]); const char*out=argv[6];
  /* sides by BFS colouring */
  static int col[MAXN]; for(int v=0;v<n0;v++) col[v]=-1;
  static int ad0[MAXN][4], dg0[MAXN]; memset(dg0,0,sizeof(dg0));
  for(int e=0;e<m0;e++){ int u=E0u[e],v=E0v[e]; ad0[u][dg0[u]++]=v; ad0[v][dg0[v]++]=u; }
  static int q[MAXN]; int qh=0,qt=0; col[0]=0; q[qt++]=0;
  while(qh<qt){ int u=q[qh++]; for(int t=0;t<dg0[u];t++){ int w=ad0[u][t]; if(col[w]<0){col[w]=1-col[u]; q[qt++]=w;} } }
  int nA=0; for(int v=0;v<n0;v++) if(col[v]==0) nA++;
  fprintf(stderr,"seed n=%d m=%d sideA=%d sideB=%d\n",n0,m0,nA,n0-nA);
  /* build base graph: edges u(A)-v(B) */
  M=0; for(int e=0;e<m0;e++){ int u=E0u[e],v=E0v[e]; if(col[u]==1){int t=u;u=v;v=t;} EA[M]=u; EB[M]=v; M++; }
  /* new vertices */
  int x=n0, y=n0+1; N=n0+2;
  /* list of A and B vertices */
  int Alist[MAXN],Blist[MAXN];
  for(int v=0;v<n0;v++){ side[v]=col[v]; }
  side[x]=0; side[y]=1;
  for(int v=0;v<N;v++) deg[v]=0;
  for(int e=0;e<M;e++){ int a=EA[e],b=EB[e]; adj[a][deg[a]++]=b; adj[b][deg[b]++]=a; }
  /* choose 3 edges to delete with distinct endpoints */
  rs ^= 0x9e3779b97f4a7c15ULL*(uint64_t)(atoll(argv[3])+1);
  int chosen[3]; int ok=0;
  while(!ok){
    for(int k=0;k<3;k++) chosen[k]=rnd()%M;
    ok = chosen[0]!=chosen[1] && chosen[0]!=chosen[2] && chosen[1]!=chosen[2]
      && EA[chosen[0]]!=EA[chosen[1]] && EA[chosen[0]]!=EA[chosen[2]] && EA[chosen[1]]!=EA[chosen[2]]
      && EB[chosen[0]]!=EB[chosen[1]] && EB[chosen[0]]!=EB[chosen[2]] && EB[chosen[1]]!=EB[chosen[2]];
  }
  /* surgery: remove a_k b_k, add x-b_k, y-a_k, x-y. Edge list: keep M edges, replace chosen by (a_k,y),(x,b_k) */
  int aS[3],bS[3];
  for(int k=0;k<3;k++){ int e=chosen[k]; aS[k]=EA[e]; bS[k]=EB[e]; }
  for(int k=0;k<3;k++){
    /* adjacency: a_k loses b_k gains y ; b_k loses a_k gains x */
    repl(aS[k],bS[k],y); repl(bS[k],aS[k],x);
    adj[y][deg[y]++]=aS[k]; adj[x][deg[x]++]=bS[k];
  }
  adj[x][deg[x]++]=y; adj[y][deg[y]++]=x;
  /* edge list: replace chosen 3 by (aS_k, y) pairs... but we need M edges with pairs (A,B):
     new pairs are (a_k,y) k=0..2 and (x,b_k) k=0..2 and (x,y). Total M-3+7 = M+4 edges. Store the
     surgery edges as the first three slots; append the rest.  The 2-switch needs to act on the whole list. */
  for(int k=0;k<3;k++){ EA[chosen[k]]=aS[k]; EB[chosen[k]]=y; }
  int ne=M; /* append (x,b_k) and (x,y) */
  for(int k=0;k<3;k++){ EA[ne]=x; EB[ne]=bS[k]; ne++; }
  EA[ne]=x; EB[ne]=y; ne++;
  M=ne;
  /* degrees check */
  for(int v=0;v<N;v++) if(deg[v]!=4){ fprintf(stderr,"deg %d = %d\n",v,deg[v]); return 1; }
  long cur=far_pairs(), best=cur;
  fprintf(stderr,"initial far_pairs=%ld (n=%d, m=%d)\n",cur,N,M);
  static int bestA[MAXN*2],bestB[MAXN*2];
  memcpy(bestA,EA,sizeof(int)*M); memcpy(bestB,EB,sizeof(int)*M);
  double t0=now(), tend=t0+secs, Tcur=T0; long it=0, acc=0;
  while(1){
    double tn=now(); if(tn>tend) break;
    double frac=(tn-t0)/secs; Tcur=T0*pow(T1/T0,frac);
    if((it&31)==0) {}
    int i=rnd()%M, j=rnd()%M; if(i==j) continue;
    int a1=EA[i],b1=EB[i],a2=EA[j],b2=EB[j];
    if(a1==a2||b1==b2) continue;
    if(has_edge(a1,b2)||has_edge(a2,b1)) continue;
    do_switch(i,j);
    long nw=far_pairs(); it++;
    long d=nw-cur;
    if(d<=0 || urand()<exp(-d/Tcur)){
      cur=nw; acc++;
      if(cur<best){ best=cur; memcpy(bestA,EA,sizeof(int)*M); memcpy(bestB,EB,sizeof(int)*M);
        fprintf(stderr,"  t=%.1f it=%ld best=%ld T=%.3f\n",tn-t0,it,best,Tcur); if(best==0) break; }
    } else {
      /* undo: (a1,b2),(a2,b1) -> (a1,b1),(a2,b2) */
      do_switch(i,j);
    }
  }
  fprintf(stderr,"done it=%ld acc=%ld best=%ld\n",it,acc,best);
  /* write best */
  memcpy(EA,bestA,sizeof(int)*M); memcpy(EB,bestB,sizeof(int)*M);
  FILE *g=fopen(out,"w"); fprintf(g,"%d\n",N);
  for(int e=0;e<M;e++) fprintf(g,"%d %d\n",EA[e],EB[e]);
  fclose(g);
  printf("RESULT n=%d far_pairs=%ld miss=%.4f iters=%ld\n",N,best,2.0*best/N,it);
  return 0;
}
