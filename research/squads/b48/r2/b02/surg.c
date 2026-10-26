// b02: choose 3 deleted seed edges (a_i,b_i); x (side A) ~ b1,b2,b3,y; y (side B) ~ a1,a2,a3,x.
// Exact far count (unordered pairs at distance > 8) by bit-parallel BFS (8 rounds of OR over neighbours).
// usage: surg SEEDFILE mode args...
//   sample NSAMP SEED            random triples, report best
//   anneal SECONDS SEED T0 T1 [INIT_a1 b1 a2 b2 a3 b3 as edge-index triple via file? no: use random init]
//   eval e1 e2 e3 [OUT.edges]    evaluate a given triple (edge indices), optionally write the edge list
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#define N0 2184
#define N 2186
#define W 35
#define X (N0)
#define Y (N0+1)
#define HALF 1092
static int EU[N0*2], EV[N0*2], M;
static int NB0[N][4];
static uint64_t BUF[2][N][W];
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec;}
static uint64_t rng_s;
static uint64_t rnd(void){rng_s^=rng_s<<13;rng_s^=rng_s>>7;rng_s^=rng_s<<17;return rng_s;}
static int rndint(int n){return (int)(rnd()%(uint64_t)n);}

static int far_count(const int *t, int nt, int write_out_name_flag, const char *outname){
  // t: edge indices (3). build adjacency
  int nb[N][4]; int deg[N];
  memcpy(nb, NB0, sizeof(int)*4*N0);
  for(int v=N0; v<N; v++) deg[v]=0;
  int A[3],B[3];
  for(int i=0;i<nt;i++){ A[i]=EU[t[i]]; B[i]=EV[t[i]]; }
  for(int i=0;i<nt;i++){
    int a=A[i], b=B[i];
    for(int s=0;s<4;s++) if(nb[a][s]==b){ nb[a][s]=Y; break; }
    for(int s=0;s<4;s++) if(nb[b][s]==a){ nb[b][s]=X; break; }
  }
  for(int i=0;i<nt;i++){ nb[X][i]=B[i]; nb[Y][i]=A[i]; }
  nb[X][3]=Y; nb[Y][3]=X;
  int cur=0;
  for(int v=0;v<N;v++){ memset(BUF[0][v],0,sizeof(uint64_t)*W); BUF[0][v][v>>6] |= 1ULL<<(v&63); }
  for(int k=0;k<8;k++){
    int nx=cur^1;
    for(int v=0;v<N;v++){
      uint64_t *d=BUF[nx][v]; const uint64_t *s=BUF[cur][v];
      const uint64_t *p0=BUF[cur][nb[v][0]], *p1=BUF[cur][nb[v][1]], *p2=BUF[cur][nb[v][2]], *p3=BUF[cur][nb[v][3]];
      for(int w=0;w<W;w++) d[w]=s[w]|p0[w]|p1[w]|p2[w]|p3[w];
    }
    cur=nx;
  }
  long tot=0;
  for(int v=0;v<N;v++){ int c=0; for(int w=0;w<W;w++) c+=__builtin_popcountll(BUF[cur][v][w]); tot += N-c; }
  long far=tot/2;
  if(write_out_name_flag && outname){
    FILE *f=fopen(outname,"w"); fprintf(f,"%d\n",N);
    for(int i=0;i<M;i++){ // seed edges except removed ones
      int skip=0; for(int j=0;j<nt;j++) if(t[j]==i) skip=1;
      if(!skip) fprintf(f,"%d %d\n",EU[i],EV[i]);
    }
    for(int i=0;i<nt;i++){ fprintf(f,"%d %d\n",X,B[i]); fprintf(f,"%d %d\n",Y,A[i]); }
    fprintf(f,"%d %d\n",X,Y); fclose(f);
  }
  return (int)far;
}
static int valid_triple(const int *t){
  for(int i=0;i<3;i++) for(int j=i+1;j<3;j++){
    if(t[i]==t[j]) return 0;
    if(EU[t[i]]==EU[t[j]]) return 0;
    if(EV[t[i]]==EV[t[j]]) return 0;
  }
  return 1;
}
int main(int argc, char **argv){
  if(argc<3){fprintf(stderr,"usage\n");return 1;}
  FILE *f=fopen(argv[1],"r"); int n; if(fscanf(f,"%d",&n)!=1) return 1;
  M=0; int deg[N0]; memset(deg,0,sizeof deg);
  int u,v;
  while(fscanf(f,"%d %d",&u,&v)==2){
    if(u>v){int t=u;u=v;v=t;}
    if(!(u<HALF && v>=HALF)){fprintf(stderr,"edge not A-B: %d %d\n",u,v);return 1;}
    EU[M]=u; EV[M]=v; M++;
    NB0[u][deg[u]++]=v; NB0[v][deg[v]++]=u;
  }
  fclose(f);
  if(M!=2*N0 && M!=4368){ }
  const char *mode=argv[2];
  if(!strcmp(mode,"eval")){
    int t[3]; for(int i=0;i<3;i++) t[i]=atoi(argv[3+i]);
    const char *out = argc>6? argv[6]:NULL;
    double t0=now(); int fc=far_count(t,3,out!=NULL,out);
    printf("far %d time %.4f\n",fc,now()-t0);
    return 0;
  }
  if(!strcmp(mode,"sample")){
    int ns=atoi(argv[3]); rng_s=strtoull(argv[4],0,10)*2654435761ULL+88172645463325252ULL;
    int best=1<<30; int bt[3]={0,0,0}; double t0=now();
    int hist[64]={0}; 
    for(int s=0;s<ns;s++){
      int t[3]; do{ for(int i=0;i<3;i++) t[i]=rndint(M); }while(!valid_triple(t));
      int fc=far_count(t,3,0,NULL);
      int bin=fc/20; if(bin>63)bin=63; hist[bin]++;
      if(fc<best){best=fc; bt[0]=t[0];bt[1]=t[1];bt[2]=t[2]; fprintf(stderr,"sample %d best %d triple %d %d %d\n",s,best,t[0],t[1],t[2]);}
      if(now()-t0>50) { fprintf(stderr,"time stop at %d\n",s); break; }
    }
    printf("best %d triple %d %d %d  evals_time %.1f\n",best,bt[0],bt[1],bt[2],now()-t0);
    for(int b=0;b<64;b++) if(hist[b]) printf("hist %d-%d %d\n",b*20,b*20+19,hist[b]);
    return 0;
  }
  if(!strcmp(mode,"anneal")){
    double secs=atof(argv[3]); rng_s=strtoull(argv[4],0,10)*2654435761ULL+88172645463325252ULL;
    double T0=atof(argv[5]), T1=atof(argv[6]);
    const char *out = argc>7? argv[7]:NULL;
    int t[3]; do{ for(int i=0;i<3;i++) t[i]=rndint(M); }while(!valid_triple(t));
    int cur=far_count(t,3,0,NULL); int best=cur; int bt[3]={t[0],t[1],t[2]};
    double t0=now(); long it=0;
    while(1){
      double el=now()-t0; if(el>secs) break;
      double frac=el/secs; double T=T0*pow(T1/T0,frac);
      int nt[3]={t[0],t[1],t[2]};
      int i=rndint(3);
      int e;
      if(rndint(2)==0) e=rndint(M);
      else {
        // local move: random walk from an endpoint of a current edge, then an incident edge
        int base = (rndint(2)? EU[nt[i]] : EV[nt[i]]);
        int w=base; int steps=1+rndint(4);
        for(int s=0;s<steps;s++) w=NB0[w][rndint(4)];
        // pick a random incident edge of w: find edges with EU or EV == w
        int cand[4]; int nc=0;
        for(int d=0;d<4;d++){ // edge index lookup by endpoints
          int nbv=NB0[w][d]; int a=w,b=nbv; if(a>b){int tt=a;a=b;b=tt;}
          for(int q=0;q<M;q++) if(EU[q]==a && EV[q]==b){ cand[nc++]=q; break; }
        }
        e = cand[rndint(nc)];
      }
      nt[i]=e;
      if(!valid_triple(nt)) continue;
      int fc=far_count(nt,3,0,NULL); it++;
      int dE=fc-cur;
      if(dE<=0 || (double)(rnd()%1000000)/1e6 < __builtin_exp(-dE/T)){
        t[0]=nt[0];t[1]=nt[1];t[2]=nt[2]; cur=fc;
        if(cur<best){best=cur; bt[0]=t[0];bt[1]=t[1];bt[2]=t[2]; fprintf(stderr,"it %ld T %.2f best %d triple %d %d %d\n",it,T,best,bt[0],bt[1],bt[2]);}
      }
    }
    printf("anneal done iters %ld best %d triple %d %d %d\n",it,best,bt[0],bt[1],bt[2]);
    if(out){ far_count(bt,3,1,out); }
    return 0;
  }
  if(!strcmp(mode,"neigh")){
    int t[3]; for(int i=0;i<3;i++) t[i]=atoi(argv[3+i]);
    int cur=far_count(t,3,0,NULL); int best=cur; int bt[3]={t[0],t[1],t[2]};
    printf("start %d\n",cur); double t0=now(); long cnt=0;
    for(int i=0;i<3;i++) for(int e=0;e<M;e++){
      int nt[3]={t[0],t[1],t[2]}; nt[i]=e;
      if(!valid_triple(nt)) continue;
      int fc=far_count(nt,3,0,NULL); cnt++;
      if(fc<best){best=fc; bt[0]=nt[0];bt[1]=nt[1];bt[2]=nt[2]; fprintf(stderr,"neigh best %d triple %d %d %d\n",best,bt[0],bt[1],bt[2]);}
      if(now()-t0>55) {fprintf(stderr,"time stop\n"); goto done;}
    }
    done:
    printf("neigh evals %ld best %d triple %d %d %d\n",cnt,best,bt[0],bt[1],bt[2]);
    if(argc>6) far_count(bt,3,1,argv[6]);
    return 0;
  }
  fprintf(stderr,"unknown mode\n"); return 1;
}
