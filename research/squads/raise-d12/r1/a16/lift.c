// a16: voltage lifts of the W(3) incidence graph (80 base vertices, 4-regular) over Z_n x|_r Z_k.
// Lift vertex (u,g) index u*M+g. Base edge e=(eu,ev) with voltage phi: (eu,g)~(ev,g*phi).
// Tree edges (BFS tree of base) get identity; 81 cotree edges get free voltages.
// cost = number of (source u, lift vertex x) pairs with dist((u,e),x) > 12, summed over 80 sources.
// usage: lift N K R secs seed prefix [initfile|-] [mode]   mode "stat": sample 300 random assignments
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#define NB 80
#define NE 160
#define DEG 4
#define DMAX 12
static int NSRC=40; // point sources only (lines are mirror images of points); full cost: NSRC=80
static int N_, K_, R_, M_, NV;
static int *powr_, *inv_;
static uint16_t *mul_;
static int eu[NE], ev[NE], istree[NE], cot[NE], ncot;
static int volt[NE];
static int slt[NB][DEG], sle[NB][DEG], sld[NB][DEG];
static int *nbr;
static uint8_t *dist;
static int *queue_;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline int rndm(int k){ return (int)(rnd() % (uint64_t)k); }
static inline double rnd01(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

static int gmul(int x,int y){
  int a1=x/K_, b1=x%K_, a2=y/K_, b2=y%K_;
  int a=(int)((a1 + (long)powr_[b1]*a2) % N_);
  int b=(b1+b2)%K_;
  return a*K_+b;
}
static void setup_group(void){
  M_=N_*K_; NV=NB*M_;
  powr_=malloc(sizeof(int)*K_); powr_[0]=1%N_;
  for(int b=1;b<K_;b++) powr_[b]=(int)((long)powr_[b-1]*R_%N_);
  if((long)powr_[0]*0+ (long)powr_[K_-1]*R_%N_ != 1%N_) { fprintf(stderr,"r^k != 1 mod n\n"); exit(1);}
  mul_=malloc(sizeof(uint16_t)*(size_t)M_*M_);
  for(int x=0;x<M_;x++) for(int y=0;y<M_;y++) mul_[(size_t)x*M_+y]=(uint16_t)gmul(x,y);
  inv_=malloc(sizeof(int)*M_);
  for(int x=0;x<M_;x++){ int f=-1; for(int y=0;y<M_;y++) if(mul_[(size_t)x*M_+y]==0){f=y;break;} inv_[x]=f; }
  nbr=malloc(sizeof(int)*(size_t)NV*DEG);
  dist=malloc(NV); queue_=malloc(sizeof(int)*NV);
}
static void read_base(const char*fn){
  FILE*f=fopen(fn,"r"); int nb,ne; if(fscanf(f,"%d %d",&nb,&ne)!=2) exit(1);
  for(int e=0;e<NE;e++) if(fscanf(f,"%d %d",&eu[e],&ev[e])!=2) exit(1);
  fclose(f);
  // BFS spanning tree from 0
  int seen[NB]={0}, Q[NB], h=0,t=0; seen[0]=1; Q[t++]=0;
  memset(istree,0,sizeof istree);
  while(h<t){ int x=Q[h++]; for(int e=0;e<NE;e++){ int y=-1; if(eu[e]==x) y=ev[e]; else if(ev[e]==x) y=eu[e]; if(y>=0 && !seen[y]){seen[y]=1; istree[e]=1; Q[t++]=y;} } }
  ncot=0; for(int e=0;e<NE;e++) if(!istree[e]) cot[ncot++]=e;
  int cnt[NB]={0};
  for(int e=0;e<NE;e++){
    int u=eu[e], v=ev[e];
    slt[u][cnt[u]]=v; sle[u][cnt[u]]=e; sld[u][cnt[u]]=0; cnt[u]++;
    slt[v][cnt[v]]=u; sle[v][cnt[v]]=e; sld[v][cnt[v]]=1; cnt[v]++;
  }
  for(int x=0;x<NB;x++) if(cnt[x]!=DEG){fprintf(stderr,"not regular\n");exit(1);}
}
static void build_nbr(void){
  for(int u=0;u<NB;u++) for(int s=0;s<DEG;s++){
    int e=sle[u][s]; int a = sld[u][s]==0 ? volt[e] : inv_[volt[e]];
    int tg=slt[u][s];
    for(int g=0; g<M_; g++){
      nbr[((size_t)u*M_+g)*DEG+s] = tg*M_ + mul_[(size_t)g*M_+a];
    }
  }
}
// returns cost; per-source uncovered counts in pers if non-null
static long cost_full(int *pers){
  build_nbr();
  long total=0;
  for(int src=0;src<NSRC;src++){
    int s0=src*M_;
    memset(dist,255,NV);
    int h=0,t=0; queue_[t++]=s0; dist[s0]=0;
    while(h<t){
      int x=queue_[h++]; int d=dist[x]; if(d>=DMAX) continue;
      const int *nb=&nbr[(size_t)x*DEG];
      for(int s=0;s<DEG;s++){ int y=nb[s]; if(dist[y]==255){ dist[y]=d+1; queue_[t++]=y; } }
    }
    int unc=NV-t; total+=unc; if(pers) pers[src]=unc;
  }
  return total;
}
static void write_lift(const char*fn){
  FILE*f=fopen(fn,"w"); fprintf(f,"%d\n",NV);
  for(int e=0;e<NE;e++) for(int g=0;g<M_;g++){
    int a=volt[e]; int x=eu[e]*M_+g, y=ev[e]*M_+mul_[(size_t)g*M_+a];
    fprintf(f,"%d %d\n",x,y);
  }
  fclose(f);
}
static void save_volt(const char*fn){
  FILE*f=fopen(fn,"w"); fprintf(f,"%d %d %d\n",N_,K_,R_);
  for(int e=0;e<NE;e++) fprintf(f,"%d\n",volt[e]);
  fclose(f);
}
int main(int argc,char**argv){
  if(argc<7){fprintf(stderr,"usage: lift N K R secs seed prefix [init|-] [stat]\n");return 1;}
  N_=atoi(argv[1]); K_=atoi(argv[2]); R_=atoi(argv[3]);
  double secs=atof(argv[4]); rs ^= (uint64_t)atoll(argv[5])*0x9E3779B97F4A7C15ULL; if(!rs) rs=1;
  const char*prefix=argv[6];
  if(getenv("FULL")) NSRC=80;
  setup_group();
  read_base("base.txt");
  // derived tables
  for(int e=0;e<NE;e++) volt[e]=0;
  char fn[512];
  int have_init = argc>7 && strcmp(argv[7],"-")!=0;
  if(have_init){
    FILE*f=fopen(argv[7],"r"); int a,b,c; if(fscanf(f,"%d %d %d",&a,&b,&c)!=3) return 1;
    if(a!=N_||b!=K_||c!=R_){fprintf(stderr,"init group mismatch\n");return 1;}
    for(int e=0;e<NE;e++) if(fscanf(f,"%d",&volt[e])!=1) return 1;
    fclose(f);
  } else {
    for(int i=0;i<ncot;i++) volt[cot[i]] = rndm(M_);
  }
  int stat = argc>8 && strcmp(argv[8],"stat")==0;
  double t0=now();
  if(stat){
    long mn=1L<<60; double sum=0; int R=(getenv("R")?atoi(getenv("R")):300); int pers[NB];
    for(int it=0;it<R;it++){
      for(int i=0;i<ncot;i++) volt[cot[i]]=rndm(M_);
      long c=cost_full(pers); sum+=c; if(c<mn) mn=c;
    }
    printf("N=%d K=%d R=%d M=%d NV=%d samples=%d mincost=%ld meancost=%.1f secs_per_eval=%.4f\n",N_,K_,R_,M_,NV,R,mn,sum/R,(now()-t0)/R);
    return 0;
  }
  long cur=cost_full(NULL), best=cur;
  int bestvolt[NE]; memcpy(bestvolt,volt,sizeof volt);
  double T0=getenv("T0")?atof(getenv("T0")):2.0, T1=getenv("T1")?atof(getenv("T1")):0.15; long it=0;
  printf("start cost %ld  M=%d\n",cur,M_); fflush(stdout);
  while(1){
    double el=now()-t0; if(el>secs) break;
    double T=T0*pow(T1/T0, el/secs);
    int e=cot[rndm(ncot)]; int old=volt[e];
    int nv=rndm(M_); if(nv==old) continue;
    volt[e]=nv;
    long c=cost_full(NULL); it++;
    long d=c-cur;
    if(d<=0 || rnd01()<exp(-d/T)){
      cur=c;
      if(cur<best){ best=cur; memcpy(bestvolt,volt,sizeof volt);
        if(best<=0) break; }
    } else volt[e]=old;
    if(it%200==0){ printf("it %ld t=%.0f T=%.3f cur %ld best %ld\n",it,el,T,cur,best); fflush(stdout); }
  }
  memcpy(volt,bestvolt,sizeof volt);
  printf("done it=%ld best=%ld secs=%.1f M=%d\n",it,best,now()-t0,M_);
  sprintf(fn,"%s_%d_%d_%d.volt",prefix,N_,K_,R_); save_volt(fn);
  if(best==0){ sprintf(fn,"%s_%d_%d_%d.edges",prefix,N_,K_,R_); write_lift(fn); printf("WROTE %s n=%d\n",fn,NV); }
  return 0;
}
