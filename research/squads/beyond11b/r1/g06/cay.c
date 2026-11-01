/* Cayley graph Cay(PGL(2,p), T) with T in the non-square-determinant coset (index-2 overgroup of PSL(2,p)).
   Bipartite (parts PSL and its coset), |Gamma| = p(p^2-1) = 2|PSL(2,p)| vertices, vertex-transitive:
   diameter = eccentricity of identity. Anneal T = (NINV involutions) + pairs {g, g^-1}, |T| = DEG.
   Usage: cay p-compiled D secs seed NINV DEG OUTPREFIX     env: START=state file, TEMP0, EDGES=1 (write edges on success)
   Cost = number of vertices not within distance D of identity. Build: gcc -O2 -DPP=67 cay.c -o cay67 -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#ifndef PP
#define PP 67
#endif
#define P ((long)PP)
#define NCODE (P*P*P*P)

typedef struct { long a,b,c,d; } M;
static long INV[PP];
static unsigned char SQ[PP];
static uint64_t *VIS;
static uint32_t *ORD;
static long NG;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline long rr(long n){ return (long)(rnd()%(uint64_t)n); }
static inline double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }

static inline M mk(long a,long b,long c,long d){
  a%=P; if(a<0)a+=P; b%=P; if(b<0)b+=P; c%=P; if(c<0)c+=P; d%=P; if(d<0)d+=P;
  long f = a?a:(b?b:(c?c:d));
  long iv = INV[f];
  M m={a*iv%P,b*iv%P,c*iv%P,d*iv%P};
  return m;
}
static inline M mul(M x,M y){ return mk(x.a*y.a+x.b*y.c, x.a*y.b+x.b*y.d, x.c*y.a+x.d*y.c, x.c*y.b+x.d*y.d); }
static inline uint64_t code(M m){ return (((uint64_t)m.a*P+m.b)*P+m.c)*P+m.d; }
static inline M decode(uint64_t c){ M m; m.d=c%P; c/=P; m.c=c%P; c/=P; m.b=c%P; c/=P; m.a=c; return m; }
static inline M minv(M m){ return mk(m.d,-m.b,-m.c,m.a); }

/* BFS from identity to depth D inside Cay(G,T); returns number of vertices reached (<= NG). */
static long bfs(const M *T, int nT, int D){
  M id = mk(1,0,0,1);
  uint64_t idc = code(id);
  long cnt=0;
  VIS[idc>>6] |= 1ULL<<(idc&63); ORD[cnt++]=(uint32_t)idc;
  long lo=0, hi=1;
  for(int lev=1; lev<=D && lo<hi; lev++){
    for(long i=lo;i<hi;i++){
      M x = decode(ORD[i]);
      for(int k=0;k<nT;k++){
        M y = mul(x,T[k]);
        uint64_t yc = code(y);
        if(!((VIS[yc>>6]>>(yc&63))&1ULL)){ VIS[yc>>6]|=1ULL<<(yc&63); ORD[cnt++]=(uint32_t)yc; }
      }
    }
    lo=hi; hi=cnt;
    if(cnt==NG) break;
  }
  for(long i=0;i<cnt;i++){ uint64_t c=ORD[i]; VIS[c>>6]&=~(1ULL<<(c&63)); }
  return cnt;
}

static M rand_elem(int inv){
  for(;;){
    long a=rr(P),b=rr(P),c=rr(P),d=rr(P);
    long det=((a*d-b*c)%P+P)%P;
    if(det==0||SQ[det]) continue;          /* need non-square determinant (coset of PSL) */
    if(inv){ if((a+d)%P) continue; }       /* involution: trace 0 */
    else   { if((a+d)%P==0) continue; }
    return mk(a,b,c,d);
  }
}

#define MAXU 16
static int nu, kind[MAXU], DEG, DD;
static M g[MAXU];
static M TT[32];
static int nT;
static void build(void){
  nT=0;
  for(int i=0;i<nu;i++){ TT[nT++]=g[i]; if(!kind[i]) TT[nT++]=minv(g[i]); }
}
static int distinct(void){
  for(int i=0;i<nT;i++){ uint64_t ci=code(TT[i]); if(ci==code(mk(1,0,0,1))) return 0;
    for(int j=i+1;j<nT;j++) if(code(TT[j])==ci) return 0; }
  return 1;
}
static long cost_now(void){ build(); return NG - bfs(TT,nT,DD); }

static void write_edges(const char*fn){
  uint32_t *idx = malloc(NCODE*sizeof(uint32_t)); memset(idx,0xff,NCODE*sizeof(uint32_t));
  M *els = malloc(NG*sizeof(M)); long n=0;
  for(uint64_t c=0;c<NCODE;c++){
    M m=decode(c);
    long f = m.a?m.a:(m.b?m.b:(m.c?m.c:m.d));
    if(f!=1) continue;
    long det=((m.a*m.d-m.b*m.c)%P+P)%P; if(det==0) continue;
    idx[c]=(uint32_t)n; els[n++]=m;
  }
  FILE *f=fopen(fn,"w"); fprintf(f,"%ld\n",n);
  for(long x=0;x<n;x++) for(int k=0;k<nT;k++){
    M y=mul(els[x],TT[k]); long v=idx[code(y)];
    if(v>x) fprintf(f,"%ld %ld\n",x,v);
  }
  fclose(f); free(idx); free(els);
  fprintf(stderr,"edges written: n=%ld\n",n);
}

static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage: cay D secs seed NINV DEG OUTPREFIX\n"); return 1; }
  DD=atoi(argv[1]); double secs=atof(argv[2]); rs ^= (uint64_t)atoll(argv[3])*0x9E3779B97F4A7C15ULL; if(!rs) rs=1;
  int ninv=atoi(argv[4]); DEG=atoi(argv[5]); const char*OUT=argv[6];
  double T0 = getenv("TEMP0")? atof(getenv("TEMP0")) : 2.0;
  NG = P*(P*P-1);
  for(long x=1;x<P;x++){ long r=1,base=x,e=P-2; while(e){ if(e&1) r=r*base%P; base=base*base%P; e>>=1;} INV[x]=r; }
  for(long i=1;i<P;i++) SQ[i*i%P]=1;
  VIS = calloc((NCODE+63)/64,sizeof(uint64_t)); ORD = malloc(NG*sizeof(uint32_t));
  if(!VIS||!ORD){ fprintf(stderr,"alloc\n"); return 1; }
  int nb = (DEG-ninv); if(nb<0||nb%2){ fprintf(stderr,"bad NINV/DEG\n"); return 1; }
  nb/=2;
  const char*st=getenv("START");
  if(st){
    FILE*f=fopen(st,"r"); if(!f){fprintf(stderr,"no START\n");return 1;}
    if(fscanf(f,"%d",&nu)!=1) return 1;
    for(int i=0;i<nu;i++){ long a,b,c,d; if(fscanf(f,"%d %ld %ld %ld %ld",&kind[i],&a,&b,&c,&d)!=5) return 1; g[i]=mk(a,b,c,d);} fclose(f);
  } else {
    nu=ninv+nb;
    for(int i=0;i<nu;i++){ kind[i]= (i<ninv); g[i]=rand_elem(kind[i]); }
    /* baseline: mean/min cost of random T (questions: hole counts of random T) */
    double sum=0; long mn=NG; int tries=0, ok=0;
    while(ok<12 && tries<200){ tries++;
      int save_nu=nu; (void)save_nu;
      for(int i=0;i<nu;i++) g[i]=rand_elem(kind[i]);
      build(); if(!distinct()) continue;
      long c=NG-bfs(TT,nT,DD); sum+=c; if(c<mn) mn=c; ok++; }
    printf("baseline random T (PGL(2,%ld), N=%ld, D=%d, DEG=%d, inv=%d): mean unreached %.1f min %ld over %d\n",P,NG,DD,DEG,ninv,ok?sum/ok:-1.0,mn,ok);
    for(int i=0;i<nu;i++) g[i]=rand_elem(kind[i]);
    while(!(build(),distinct())) for(int i=0;i<nu;i++) g[i]=rand_elem(kind[i]);
  }
  double t0=now();
  build(); if(!distinct()){ fprintf(stderr,"start not distinct\n"); return 1; }
  long cost=NG-bfs(TT,nT,DD), best=cost; long evals=1;
  M bestg[MAXU]; memcpy(bestg,g,sizeof(g));
  printf("start cost %ld (N=%ld)\n",cost,NG); fflush(stdout);
  while(now()-t0 < secs && cost>0){
    double frac=(now()-t0)/secs;
    double temp = T0*(1.0-frac)+0.02;
    int u = (int)rr(nu);
    M old=g[u];
    M cand=rand_elem(kind[u]);
    g[u]=cand; build();
    if(!distinct()){ g[u]=old; continue; }
    long nc = NG-bfs(TT,nT,DD); evals++;
    if(nc<=cost || urand() < exp(-(double)(nc-cost)/temp)){
      cost=nc; if(cost<best){ best=cost; memcpy(bestg,g,sizeof(g)); }
    } else g[u]=old;
    if(evals%100==0){ printf("eval %ld t=%.0f cost %ld best %ld temp %.2f\n",evals,now()-t0,cost,best,temp); fflush(stdout); }
  }
  memcpy(g,bestg,sizeof(g)); build();
  long fin = NG-bfs(TT,nT,DD); /* unreached */
  printf("RESULT p=%ld D=%d DEG=%d inv=%d N=%ld evals=%ld best_unreached=%ld final_check_unreached=%ld secs=%.1f\n",P,DD,DEG,ninv,NG,evals,best,fin,now()-t0);
  char fn[512];
  snprintf(fn,sizeof fn,"%s.state",OUT); FILE*f=fopen(fn,"w"); fprintf(f,"%d\n",nu);
  for(int i=0;i<nu;i++) fprintf(f,"%d %ld %ld %ld %ld\n",kind[i],g[i].a,g[i].b,g[i].c,g[i].d); fclose(f);
  if(best==0 && fin==0){
    snprintf(fn,sizeof fn,"%s.sol",OUT); f=fopen(fn,"w");
    fprintf(f,"PGL(2,%ld) Cayley, D=%d, DEG=%d, T (matrices normalized):\n",P,DD,DEG);
    for(int i=0;i<nT;i++) fprintf(f,"%ld %ld %ld %ld\n",TT[i].a,TT[i].b,TT[i].c,TT[i].d); fclose(f);
    if(getenv("EDGES")){ snprintf(fn,sizeof fn,"%s.edges",OUT); write_edges(fn); }
    printf("SOLUTION FOUND: %s.sol\n",OUT);
  }
  return 0;
}
