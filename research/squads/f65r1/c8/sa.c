/* c8: chamber graph (630) + 28 A-hubs + 28 B-hubs (net +56 = 686), built by deleting a random matching
   of 168 edges and attaching hubs to the freed slots; then simulated annealing over double-edge swaps
   (all degrees stay 6, bipartition kept). Cost = unordered same-side pairs at distance > 4. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
#define NV 686
#define HALF 343
#define W 11
#define DEG 6
#define NE (NV*DEG/2)
typedef uint64_t u64;
static int adj[NV][DEG];
static int eA[NE], eB[NE];
static u64 R[2][NV][W];
static u64 maskA[W], maskB[W];

static double urand(void){ return drand48(); }

static int cost_full(void){
  int cur=0;
  memset(R[0],0,sizeof(R[0]));
  for(int v=0;v<NV;v++) R[0][v][v>>6] |= 1ULL<<(v&63);
  for(int lvl=1;lvl<=4;lvl++){
    int nx=lvl&1, cu=(lvl-1)&1;
    for(int v=0;v<NV;v++){
      for(int w=0;w<W;w++) R[nx][v][w]=R[cu][v][w];
      for(int k=0;k<DEG;k++){ int u=adj[v][k];
        for(int w=0;w<W;w++) R[nx][v][w] |= R[cu][u][w]; }
    }
    cur=nx;
  }
  long bad=0;
  for(int v=0;v<NV;v++){
    u64 *m = (v<HALF)? maskA: maskB;
    for(int w=0;w<W;w++) bad += __builtin_popcountll(m[w] & ~R[cur][v][w]);
  }
  return (int)(bad/2);
}

static int has_edge(int a,int b){ for(int k=0;k<DEG;k++) if(adj[a][k]==b) return 1; return 0; }
static void repl(int v,int old,int nw){ for(int k=0;k<DEG;k++) if(adj[v][k]==old){ adj[v][k]=nw; return; } fprintf(stderr,"repl fail\n"); exit(1); }

int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage: sa SEED SECS T0 T1 CHAMBER_EDGES OUT [init_only]\n"); return 1; }
  unsigned long seed=strtoul(argv[1],0,10); double secs=atof(argv[2]);
  double T0=atof(argv[3]), T1=atof(argv[4]); const char*inf=argv[5], *outf=argv[6];
  int init_only = argc>7;
  srand48(seed);
  for(int w=0;w<W;w++){maskA[w]=0;maskB[w]=0;}
  for(int v=0;v<NV;v++){ if(v<HALF) maskA[v>>6]|=1ULL<<(v&63); else maskB[v>>6]|=1ULL<<(v&63); }

  /* read chamber graph */
  FILE*f=fopen(inf,"r"); int n; if(fscanf(f,"%d",&n)!=1) return 1;
  int cu[2000],cv[2000],m=0; int x,y;
  while(fscanf(f,"%d %d",&x,&y)==2){ cu[m]=x; cv[m]=y; m++; }
  fclose(f);
  int nb=n; int *col=malloc(sizeof(int)*n); for(int i=0;i<n;i++) col[i]=-1;
  /* bipartition by BFS */
  int *q=malloc(sizeof(int)*n); int qh=0,qt=0; col[0]=0; q[qt++]=0;
  while(qh<qt){ int u=q[qh++]; for(int e=0;e<m;e++){ int v=-1; if(cu[e]==u) v=cv[e]; else if(cv[e]==u) v=cu[e]; if(v>=0 && col[v]<0){ col[v]=1-col[u]; q[qt++]=v; } } }
  int idx[630]; int ca=0,cb=HALF;
  for(int i=0;i<n;i++){ if(col[i]==0) idx[i]=ca++; else idx[i]=cb++; }
  /* edges as (A,B) pairs */
  int ea[2000],eb[2000];
  for(int e=0;e<m;e++){ int a,b; if(col[cu[e]]==0){a=idx[cu[e]]; b=idx[cv[e]];} else {a=idx[cv[e]]; b=idx[cu[e]];} ea[e]=a; eb[e]=b; }
  /* random matching of 168 edges */
  int ord[2000]; for(int e=0;e<m;e++) ord[e]=e;
  for(int e=m-1;e>0;e--){ int j=(int)(urand()*(e+1)); int t=ord[e]; ord[e]=ord[j]; ord[j]=t; }
  static int usedA[HALF], usedB[HALF]; int removed[2000]; memset(removed,0,sizeof(removed));
  int nrem=0;
  for(int i=0;i<m && nrem<168;i++){ int e=ord[i]; if(!usedA[ea[e]] && !usedB[eb[e]-HALF]){ usedA[ea[e]]=1; usedB[eb[e]-HALF]=1; removed[e]=1; nrem++; } }
  int FA[168],FB[168]; int na=0,nbf=0;
  for(int a=0;a<315;a++) if(usedA[a]) FA[na++]=a;   /* old A vertices with a freed slot */
  for(int b=HALF;b<HALF+315;b++) if(usedB[b-HALF]) FB[nbf++]=b;
  for(int i=167;i>0;i--){ int j=(int)(urand()*(i+1)); int t=FA[i]; FA[i]=FA[j]; FA[j]=t; t=FB[i]; FB[i]=FB[j]; FB[j]=t; }
  /* build edge list */
  int E=0; for(int e=0;e<m;e++) if(!removed[e]){ eA[E]=ea[e]; eB[E]=eb[e]; E++; }
  /* A-hubs: indices 315..342 get free B slots FB; B-hubs 658..685 get free A slots FA */
  for(int i=0;i<28;i++){ for(int k=0;k<6;k++){ eA[E]=315+i; eB[E]=FB[6*i+k]; E++; } }
  for(int i=0;i<28;i++){ for(int k=0;k<6;k++){ eA[E]=FA[6*i+k]; eB[E]=HALF+315+i; E++; } }
  if(E!=NE){ fprintf(stderr,"E=%d\n",E); return 1; }
  memset(adj,-1,sizeof(adj)); int dg[NV]; memset(dg,0,sizeof(dg));
  for(int e=0;e<NE;e++){ int a=eA[e], b=eB[e]; adj[a][dg[a]++]=b; adj[b][dg[b]++]=a; }
  for(int v=0;v<NV;v++) if(dg[v]!=6){ fprintf(stderr,"deg %d = %d\n",v,dg[v]); return 1; }
  int cost=cost_full();
  fprintf(stderr,"initial cost (unordered same-side pairs at dist>4) = %d\n",cost);
  if(init_only){ printf("%d\n",cost); }
  int best=cost; int bestA[NE],bestB[NE]; memcpy(bestA,eA,sizeof(eA)); memcpy(bestB,eB,sizeof(eB));
  clock_t t0=clock(); long it=0, acc=0;
  while(!init_only && best>0){
    it++;
    if((it&1023)==0){ double el=(double)(clock()-t0)/CLOCKS_PER_SEC; if(el>secs) break;
      double fr=el/secs; double T=T0*pow(T1/T0,fr);
      if((it&((1<<17)-1))==0) fprintf(stderr,"it %ld cost %d best %d T %.3f acc %ld\n",it,cost,best,T,acc); }
    double el_frac=(double)(clock()-t0)/CLOCKS_PER_SEC/secs; double T=T0*pow(T1/T0,el_frac>1?1:el_frac);
    int i=(int)(urand()*NE), j=(int)(urand()*NE); if(i==j) continue;
    int a1=eA[i],b1=eB[i],a2=eA[j],b2=eB[j];
    if(a1==a2||b1==b2) continue;
    if(has_edge(a1,b2)||has_edge(a2,b1)) continue;
    repl(a1,b1,b2); repl(b1,a1,a2); repl(a2,b2,b1); repl(b2,a2,a1);
    eB[i]=b2; eB[j]=b1;
    int nc=cost_full();
    int d=nc-cost;
    if(d<=0 || urand()<exp(-d/T)){ cost=nc; acc++;
      if(cost<best){ best=cost; memcpy(bestA,eA,sizeof(eA)); memcpy(bestB,eB,sizeof(eB)); }
    } else {
      repl(a1,b2,b1); repl(b1,a2,a1); repl(a2,b1,b2); repl(b2,a1,a2);
      eB[i]=b1; eB[j]=b2;
    }
  }
  fprintf(stderr,"done it %ld best %d\n",it,best);
  /* write best */
  memcpy(eA,bestA,sizeof(eA)); memcpy(eB,bestB,sizeof(eB));
  FILE*o=fopen(outf,"w"); fprintf(o,"%d\n",NV);
  for(int e=0;e<NE;e++) fprintf(o,"%d %d\n",eA[e],eB[e]);
  fclose(o);
  printf("best %d\n",best);
  return 0;
}
