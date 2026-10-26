// Structured configuration: points = F_7^3, blocks = lines of 7 parallel classes (fixed directions),
// each line loses one point (sig: line -> deleted point, a bijection). SA over sig via alternating cycles.
// Cost = same-side ordered pairs at distance > 4 (both sides).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define NP 343
#define NL 343
#define NV 686
static int linept[NL][7];
static int sig[NL], own[NP];
static int adj[NV][6], deg[NV];
static unsigned long long rs=88172645463325252ULL;
static unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static int online(int l,int p){ for(int k=0;k<7;k++) if(linept[l][k]==p) return 1; return 0; }
static int cost(void){
  for(int v=0;v<NV;v++) deg[v]=0;
  for(int l=0;l<NL;l++) for(int k=0;k<7;k++){
    int p=linept[l][k]; if(p==sig[l]) continue;
    int b=343+l; adj[p][deg[p]++]=b; adj[b][deg[b]++]=p; }
  int total=0; static int dist[NV], qu[NV];
  for(int s=0;s<NV;s++){
    for(int v=0;v<NV;v++) dist[v]=-1;
    int h=0,t=0; qu[t++]=s; dist[s]=0;
    while(h<t){ int x=qu[h++]; if(dist[x]>=4) continue;
      for(int k=0;k<deg[x];k++){ int y=adj[x][k]; if(dist[y]<0){ dist[y]=dist[x]+1; qu[t++]=y; } } }
    for(int v=0;v<NV;v++) if(((v<343)==(s<343)) && dist[v]<0) total++;
  }
  return total;
}
static void dump(const char*fn){
  FILE*f=fopen(fn,"w"); fprintf(f,"%d\n",NV);
  for(int l=0;l<NL;l++) for(int k=0;k<7;k++){ int p=linept[l][k]; if(p==sig[l]) continue; fprintf(f,"%d %d\n",p,343+l); }
  fclose(f);
}
int main(int argc,char**argv){
  // args: seed iters T0 T1 outprefix
  unsigned long long seed=strtoull(argv[1],0,10); long iters=atol(argv[2]);
  double T0=atof(argv[3]), T1=atof(argv[4]); const char*outp=argv[5];
  rs ^= seed*2654435761ULL+12345; for(int i=0;i<10;i++) rnd();
  FILE*f=fopen("/home/user/degree-diameter/research/squads/f65r1/c13/lines.txt","r");
  for(int l=0;l<NL;l++) for(int k=0;k<7;k++) fscanf(f,"%d",&linept[l][k]);
  fclose(f);
  f=fopen("/home/user/degree-diameter/research/squads/f65r1/c13/init_sig.txt","r");
  for(int l=0;l<NL;l++) fscanf(f,"%d",&sig[l]);
  fclose(f);
  for(int l=0;l<NL;l++) own[sig[l]]=l;
  int cur=cost(), best=cur; static int bestsig[NL]; memcpy(bestsig,sig,sizeof sig);
  fprintf(stderr,"init cost %d\n",cur);
  for(long it=0; it<iters && best>0; it++){
    double T = T0*pow(T1/T0,(double)it/iters);
    int L[16], X[16], old[16]; int len=0;
    int L1=rnd()%NL; int old1=sig[L1];
    int x=linept[L1][rnd()%7]; if(x==old1) continue;
    static int used[NL]; memset(used,0,sizeof used);
    used[L1]=1; L[0]=L1; X[0]=x; len=1;
    int nxt=own[x]; int closed=0;
    while(len<12){
      if(used[nxt]) break;
      used[nxt]=1; L[len]=nxt;
      if(online(nxt,old1)){ X[len]=old1; len++; closed=1; break; }
      int z=linept[nxt][rnd()%7];
      if(z==sig[nxt]) break;
      X[len]=z; len++;
      nxt=own[z];
    }
    if(!closed) continue;
    for(int t=0;t<len;t++) old[t]=sig[L[t]];
    for(int t=0;t<len;t++) sig[L[t]]=X[t];
    for(int t=0;t<len;t++) own[X[t]]=L[t];
    int nc=cost(); int d=nc-cur;
    if(d<=0 || urand()<exp(-d/T)){
      cur=nc;
      if(cur<best){ best=cur; memcpy(bestsig,sig,sizeof sig);
        fprintf(stderr,"it %ld T %.3f best %d\n",it,T,best); }
    } else {
      for(int t=0;t<len;t++) sig[L[t]]=old[t];
      for(int t=0;t<len;t++) own[old[t]]=L[t];
    }
    if(it%20000==0) fprintf(stderr,"it %ld T %.3f cur %d best %d\n",it,T,cur,best);
  }
  memcpy(sig,bestsig,sizeof sig);
  printf("best %d\n",best);
  char fn[512]; sprintf(fn,"%s.edges",outp); dump(fn);
  return 0;
}
