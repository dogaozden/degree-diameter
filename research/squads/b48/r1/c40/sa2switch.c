// c40: start from the best Singer-orbit incidence graph of PG(6,3) (4-regular, girth >= 6, 2186 vertices),
// then simulated annealing over bipartite 2-switches, cost = unordered pairs at distance > 8.
// usage: sa2switch ORBITS SECONDS SEED OUT.edges T0 T1
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define NP 1093
#define NV 2186
#define W 35
typedef uint64_t u64;
static int nb[NV][4];
static u64 A0[NV][W], A1[NV][W];
static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static long far_cost(void){
  memset(A0,0,sizeof A0);
  for(int v=0;v<NV;v++) A0[v][v>>6] |= 1ULL<<(v&63);
  for(int k=0;k<8;k++){
    for(int v=0;v<NV;v++){
      u64 *d=A1[v]; const u64 *s=A0[v];
      for(int w=0;w<W;w++) d[w]=s[w];
      for(int j=0;j<4;j++){ const u64 *t=A0[nb[v][j]]; for(int w=0;w<W;w++) d[w]|=t[w]; }
    }
    memcpy(A0,A1,sizeof A0);
  }
  long tot=0;
  for(int v=0;v<NV;v++){ int pc=0; for(int w=0;w<W;w++) pc+=__builtin_popcountll(A0[v][w]); tot+=NV-pc; }
  return tot/2;
}
static int idx(int v,int u){ for(int j=0;j<4;j++) if(nb[v][j]==u) return j; return -1; }
static int has(int v,int u){ return idx(v,u)>=0; }
static int load_orbit(FILE *f, int o_unused){
  // fills nb from NP lines (each "p1 p2 p3 p4"); returns 0 if not 4-regular
  int cnt[NV]; memset(cnt,0,sizeof cnt);
  for(int l=0;l<NP;l++){
    int p[4]; for(int j=0;j<4;j++) if(fscanf(f,"%d",&p[j])!=1) return -1;
    for(int j=0;j<4;j++){
      int v=p[j]; if(cnt[v]>=4) return 0;
      nb[v][cnt[v]++]=NP+l;
      nb[NP+l][j]=v;
    }
  }
  for(int v=0;v<NP;v++) if(cnt[v]!=4) return 0;
  return 1;
}
int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage\n"); return 1; }
  FILE *f=fopen(argv[1],"r"); int K; if(fscanf(f,"%d",&K)!=1) return 1;
  double secs=atof(argv[2]); rs ^= (u64)atoll(argv[3])*0x9E3779B97F4A7C15ULL; for(int i=0;i<10;i++) rnd();
  double T0=atof(argv[5]), T1=atof(argv[6]);
  static int bestnb[NV][4]; long bestk=-1; long bestcost=1L<<40;
  // evaluate every orbit, keep the best start
  static int orbit_costs[256];
  for(int o=0;o<K;o++){
    if(load_orbit(f,o)!=1){ fprintf(stderr,"orbit %d not 4-regular\n",o); orbit_costs[o]=-1; continue; }
    long c=far_cost(); orbit_costs[o]=(int)c;
    if(c<bestcost){ bestcost=c; bestk=o; memcpy(bestnb,nb,sizeof nb); }
  }
  fclose(f);
  printf("orbit far-pair costs (first 91, min %ld in orbit %ld):\n",bestcost,bestk);
  for(int o=0;o<K;o++) printf("%d%c",orbit_costs[o],(o%20==19||o==K-1)?'\n':' ');
  memcpy(nb,bestnb,sizeof nb);
  long cur=bestcost, best=bestcost;
  static int bestSA[NV][4]; memcpy(bestSA,nb,sizeof nb);
  double t0=now(), elapsed=0, Tcur=T0; long it=0, acc=0;
  while(1){
    elapsed=now()-t0; if(elapsed>secs) break;
    double frac=elapsed/secs; Tcur=T0*pow(T1/T0,frac);
    int a=rnd()%NP, ia=rnd()%4; int b=nb[a][ia];
    int c=rnd()%NP, ic=rnd()%4; int d=nb[c][ic];
    if(a==c) continue;
    if(has(a,d) || has(c,b)) continue;
    // apply: edges (a,b),(c,d) -> (a,d),(c,b)
    nb[a][ia]=d; int ib=idx(b,a); nb[b][ib]=c; nb[c][ic]=b; int id=idx(d,c); nb[d][id]=a;
    long nc=far_cost(); it++;
    long delta=nc-cur;
    if(delta<=0 || (double)(rnd()%1000000007ULL)/1000000007.0 < exp(-(double)delta/Tcur)){
      cur=nc; acc++;
      if(cur<best){ best=cur; memcpy(bestSA,nb,sizeof nb); }
      if(cur==0) break;
    } else {
      nb[a][ia]=b; int jb=idx(b,c); nb[b][jb]=a; nb[c][ic]=d; int jd=idx(d,a); nb[d][jd]=c;
    }
  }
  memcpy(nb,bestSA,sizeof nb);
  long fin=far_cost();
  FILE *o=fopen(argv[4],"w"); fprintf(o,"%d\n",NV);
  for(int p=0;p<NP;p++) for(int j=0;j<4;j++) fprintf(o,"%d %d\n",p,nb[p][j]);
  fclose(o);
  printf("SA iters=%ld accepted=%ld time=%.1fs T0=%g T1=%g\n",it,acc,now()-t0,T0,T1);
  printf("RESULT c40 n=2186 far_pairs=%ld miss=%.4f start_orbit=%ld start_cost=%ld\n",fin,2.0*fin/2186.0,bestk,bestcost);
  return 0;
}
