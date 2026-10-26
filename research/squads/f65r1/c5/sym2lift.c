// c5: symmetric voltage lifts of 2+2 bases with sigma: a0<->a1, b0<->b1.
// Base (6-regular, bipartite): a0-b0 x P, a1-b1 x P, a0-b1 x (6-P), a1-b0 x (6-P).
// Voltage constraint: v(sigma e) = f(v(e)), f = alpha (mode 0) or alpha∘inv (mode 1), alpha an involution.
// Free: 6 orbit voltages. Lift vertex (x,g) = x*n+g, edge (x,g)~(y, a*g) for base edge x->y voltage a.
// Cost = sum over the 4 base vertices of same-side vertices at distance > 4 (or unreachable).
// usage: sym2lift GROUPFILE AUTFILE P MODE SECONDS SEED OUTPREFIX
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int n, *mul, *inv_, *al, *fal, P, N;
static int Ef[12], Et[12], Eo[12], Er[12];
static int *adj, *deg, *dist, *q;
static int v[6];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long xr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int rnd(int m){ return (int)(xr()%(unsigned long long)m); }
static inline double urand(void){ return (xr()>>11)*(1.0/9007199254740992.0); }

static void setup_edges(void){
  int e=0;
  for(int i=0;i<P;i++){
    Ef[e]=0;Et[e]=2;Eo[e]=i;Er[e]=1;e++;
    Ef[e]=1;Et[e]=3;Eo[e]=i;Er[e]=0;e++;
  }
  for(int j=0;j<6-P;j++){
    Ef[e]=0;Et[e]=3;Eo[e]=P+j;Er[e]=1;e++;
    Ef[e]=1;Et[e]=2;Eo[e]=P+j;Er[e]=0;e++;
  }
}

static void build(void){
  int a[12];
  for(int e=0;e<12;e++) a[e] = Er[e] ? v[Eo[e]] : fal[v[Eo[e]]];
  memset(deg,0,sizeof(int)*N);
  for(int g=0;g<n;g++) for(int e=0;e<12;e++){
    int u=Ef[e]*n+g, w=Et[e]*n+mul[a[e]*n+g];
    adj[u*6+deg[u]++]=w; adj[w*6+deg[w]++]=u;
  }
}

static int cost(void){
  build();
  int total=0;
  for(int x0=0;x0<4;x0++){
    int s=x0*n;
    for(int i=0;i<N;i++) dist[i]=-1;
    dist[s]=0; int h=0,t=0; q[t++]=s;
    while(h<t){
      int x=q[h++];
      for(int k=0;k<6;k++){ int y=adj[x*6+k]; if(dist[y]<0){ dist[y]=dist[x]+1; q[t++]=y; } }
    }
    int side=x0/2;
    for(int z=0;z<N;z++){
      if((z/n)/2!=side) continue;
      if(dist[z]<0 || dist[z]>4) total++;
    }
  }
  return total;
}

static int valid_state(void){
  for(int i=0;i<P;i++) for(int j=i+1;j<P;j++) if(v[i]==v[j]) return 0;
  for(int i=P;i<6;i++) for(int j=i+1;j<6;j++) if(v[i]==v[j]) return 0;
  return 1;
}

static void write_edges(const char* fn){
  FILE* f=fopen(fn,"w"); if(!f) return;
  fprintf(f,"%d\n",N);
  for(int g=0;g<n;g++) for(int e=0;e<12;e++){
    int a = Er[e] ? v[Eo[e]] : fal[v[Eo[e]]];
    fprintf(f,"%d %d\n", Ef[e]*n+g, Et[e]*n+mul[a*n+g]);
  }
  fclose(f);
}

int main(int argc,char**argv){
  if(argc<8){ fprintf(stderr,"usage: GROUP AUT P MODE SECONDS SEED OUTPREFIX\n"); return 1; }
  FILE* f=fopen(argv[1],"r"); if(fscanf(f,"%d",&n)!=1) return 1;
  mul=malloc(sizeof(int)*n*n); for(int i=0;i<n*n;i++) if(fscanf(f,"%d",&mul[i])!=1) return 1; fclose(f);
  inv_=malloc(sizeof(int)*n);
  for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(mul[i*n+j]==0) inv_[i]=j;
  al=malloc(sizeof(int)*n); fal=malloc(sizeof(int)*n);
  f=fopen(argv[2],"r"); for(int i=0;i<n;i++) if(fscanf(f,"%d",&al[i])!=1) return 1; fclose(f);
  P=atoi(argv[3]); int mode=atoi(argv[4]); double secs=atof(argv[5]);
  rs ^= (unsigned long long)atoll(argv[6])*0x9E3779B97F4A7C15ULL; for(int i=0;i<10;i++) xr();
  const char* outp=argv[7];
  for(int i=0;i<n;i++) fal[i] = mode==0 ? al[i] : inv_[al[i]];
  // check involution-consistency: f must be an involution for sigma^2 = id
  for(int i=0;i<n;i++) if(fal[fal[i]]!=i && mode==0){ fprintf(stderr,"alpha not involution\n"); return 1; }
  N=4*n;
  adj=malloc(sizeof(int)*N*6); deg=malloc(sizeof(int)*N); dist=malloc(sizeof(int)*N); q=malloc(sizeof(int)*N);
  setup_edges();
  do{ for(int k=0;k<6;k++) v[k]=rnd(n); } while(!valid_state());
  int cur=cost(), best=cur; int bestv[6]; memcpy(bestv,v,sizeof v);
  double T0=6.0, T1=0.3;
  clock_t st=clock(); long it=0;
  while(best>0){
    double el=(double)(clock()-st)/CLOCKS_PER_SEC;
    if(el>=secs) break;
    double fr=el/secs; double T=T0*pow(T1/T0,fr);
    int k=rnd(6); int old=v[k];
    v[k]=rnd(n);
    if(!valid_state()){ v[k]=old; continue; }
    int c=cost(); it++;
    if(c<=cur || urand()<exp(-(double)(c-cur)/T)){
      cur=c;
      if(cur<best){ best=cur; memcpy(bestv,v,sizeof v); }
    } else v[k]=old;
  }
  memcpy(v,bestv,sizeof v);
  int c=cost();
  char fn[512]; snprintf(fn,sizeof fn,"%s.sol",outp);
  FILE* so=fopen(fn,"w"); fprintf(so,"n %d P %d mode %d cost %d v",n,P,mode,c); for(int k=0;k<6;k++) fprintf(so," %d",v[k]); fprintf(so,"\n"); fclose(so);
  snprintf(fn,sizeof fn,"%s.edges",outp); write_edges(fn);
  printf("RESULT n=%d P=%d mode=%d best_cost=%d iters=%ld voltages",N,P,mode,c,it);
  for(int k=0;k<6;k++) printf(" %d",v[k]); printf("\n");
  return 0;
}
