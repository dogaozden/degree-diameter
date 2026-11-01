/* Haar graph search over G = Z_p^2 x| Z_k (Frobenius, generator acts as multiplication by omega in F_{p^2}, order k).
 * Element g = c*P2 + v, v = a + p*b (F_{p^2} = F_p[t]/(t^2-nr)). (v1,c1)(v2,c2) = (v1 + w^{c1} v2, c1+c2).
 * Haar graph: (g,A) ~ (s g,B), s in S (s_0 = e). Cost = #unreached within D from (e,A) + from (e,B) (both sides).
 * Usage: semi p k d D secs seed OUT   (writes OUT on cost 0). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
static int p,k,P2,N,d,D,nr; static uint32_t om;
static uint32_t *MT;               /* MT[c*P2+v] = w^c * v */
static uint64_t rs;
static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int fadd(int x,int y){ int a=(x%p+y%p)%p, b=((x/p)+(y/p))%p; return a+p*b; }
static inline int fneg(int x){ int a=(p-x%p)%p, b=(p-(x/p)%p)%p; return a+p*b; }
static inline int fmulv(int x,int y){ int a=x%p,b=x/p,c=y%p,dd=y/p; int r=(a*c+nr*(b*dd))%p, s=(a*dd+b*c)%p; return r+p*s; }
static inline uint32_t mul(uint32_t s,uint32_t g){ uint32_t cs=s/P2, vs=s%P2, cg=g/P2, vg=g%P2; uint32_t c=(cs+cg)%k;
    return c*P2 + fadd(vs, MT[cs*P2+vg]); }
static inline uint32_t inv(uint32_t s){ uint32_t cs=s/P2, vs=s%P2; uint32_t ci=(k-cs)%k; return ci*P2 + fneg(MT[ci*P2+vs]); }
static uint32_t *L[32],*Li[32],*Lc[32],*Lic[32]; static uint32_t SE[32], SI[32];
static uint32_t *qn; static uint32_t *vis; static uint32_t stamp=0; static uint8_t *dist;
static int bfs(int side, uint32_t src){  /* returns #reached (both sides) within D */
    stamp++; int h=0,t=0; uint32_t x=(side?N:0)+src; vis[x]=stamp; dist[x]=0; qn[t++]=x; int cnt=1;
    while(h<t){ uint32_t y=qn[h++]; int dy=dist[y]; if(dy==D) continue;
        if(y<(uint32_t)N){ for(int i=0;i<d;i++){ uint32_t z=N+L[i][y]; if(vis[z]!=stamp){ vis[z]=stamp; dist[z]=dy+1; qn[t++]=z; cnt++; } } }
        else { uint32_t g=y-N; for(int i=0;i<d;i++){ uint32_t z=Li[i][g]; if(vis[z]!=stamp){ vis[z]=stamp; dist[z]=dy+1; qn[t++]=z; cnt++; } } }
    }
    return cnt; }
static int cost_eval(void){ int r1=bfs(0,0), r2=bfs(1,0); return (2*N-r1)+(2*N-r2); }
static int check_inline(void){ return 0; }
static void build(uint32_t *out,uint32_t *outi,uint32_t s,uint32_t si){ for(int g=0;g<N;g++){ out[g]=mul(s,g); } for(int h=0;h<N;h++) outi[h]=mul(si,h); }
int main(int argc,char**argv){
    if(argc<8){ fprintf(stderr,"usage: semi p k d D secs seed OUT\n"); return 2; }
    p=atoi(argv[1]); k=atoi(argv[2]); d=atoi(argv[3]); D=atoi(argv[4]); double secs=atof(argv[5]); rs=0x9E3779B97F4A7C15ULL^((uint64_t)atoll(argv[6])+1)*2654435761ULL; const char*out=argv[7];
    P2=p*p; N=k*P2;
    /* nonresidue */
    for(nr=2;;nr++){ long e=1,b=nr; for(int i=0;i<(p-1)/2;i++) e=e*nr%p; if(e==p-1) break; }
    /* find omega of order exactly k with b != 0 */
    int found=0; for(int tries=0; tries<100000 && !found; tries++){
        uint32_t x=rnd()%P2; if(x/p==0) continue;
        /* y = x^((P2-1)/k) */
        uint32_t y=1, base=x; long ex=(P2-1)/k; if((P2-1)%k){ fprintf(stderr,"k does not divide p^2-1\n"); return 2; }
        while(ex){ if(ex&1) y=fmulv(y,base); base=fmulv(base,base); ex>>=1; }
        uint32_t z=1; int ord=0; for(int j=1;j<=k;j++){ z=fmulv(z,y); if(z==1){ ord=j; break; } }
        if(ord==k && y/p!=0){ om=y; found=1; } }
    if(!found){ fprintf(stderr,"no omega\n"); return 2; }
    MT=malloc(sizeof(uint32_t)*(size_t)k*P2);
    uint32_t w=1; for(int c=0;c<k;c++){ for(int v=0;v<P2;v++) MT[c*P2+v]=fmulv(w,v); w=fmulv(w,om); }
    for(int i=0;i<d;i++){ L[i]=malloc(4*N); Li[i]=malloc(4*N); Lc[i]=malloc(4*N); Lic[i]=malloc(4*N); }
    qn=malloc(4*2*N); vis=calloc(2*N,4); dist=malloc(2*N);
    /* init S: e plus d-1 random non-identity distinct */
    SE[0]=0; SI[0]=0;
    for(int i=1;i<d;i++){ int ok; uint32_t x; do{ x=rnd()%N; ok=(x!=0); for(int j=0;j<i;j++) if(SE[j]==x) ok=0; }while(!ok); SE[i]=x; }
    for(int i=0;i<d;i++){ SI[i]=inv(SE[i]); build(L[i],Li[i],SE[i],SI[i]); }
    int cur=cost_eval(); int best=cur; uint32_t BS[32]; memcpy(BS,SE,sizeof SE);
    fprintf(stderr,"N=%d (2N=%d) omega=%u start cost %d\n",N,2*N,om,cur);
    double T0=getenv("T0")?atof(getenv("T0")):3.0,T=T0; double TF=getenv("TF")?atof(getenv("TF")):0.15; long it=0, since=0; double t0=wall();
    while(best>0){
        if((it&63)==0 && wall()-t0>secs) break;
        it++; int i=1+rnd()%(d-1); uint32_t x; int ok; do{ x=rnd()%N; ok=(x!=0); for(int j=0;j<d;j++) if(SE[j]==x) ok=0; }while(!ok);
        uint32_t xi=inv(x); build(Lc[i],Lic[i],x,xi);
        uint32_t *oldL=L[i],*oldLi=Li[i]; uint32_t olds=SE[i], oldsi=SI[i];
        L[i]=Lc[i]; Li[i]=Lic[i]; SE[i]=x; SI[i]=xi;
        int nc=cost_eval(); int dl=nc-cur;
        if(dl<=0 || (double)(rnd()%1000000)/1e6 < exp(-dl/T)){ cur=nc; Lc[i]=oldL; Lic[i]=oldLi; 
            if(cur<best){ best=cur; memcpy(BS,SE,sizeof SE); since=0; } else since++; }
        else { L[i]=oldL; Li[i]=oldLi; SE[i]=olds; SI[i]=oldsi; since++; }
        T*=0.9997; if(T<TF) T=TF;
        if(since>20000){ T=T0; since=0; }
        if(it%500==0) fprintf(stderr,"it %ld T %.2f cur %d best %d (%.0fs)\n",it,T,cur,best,wall()-t0);
    }
    printf("RESULT p=%d k=%d d=%d D=%d N=%d 2N=%d best=%d iters=%ld\n",p,k,d,D,N,2*N,best,it);
    if(best==0){ FILE*f=fopen(out,"w"); fprintf(f,"semi %d %d %d %d\n",p,k,d,D); for(int i=0;i<d;i++) fprintf(f,"%u %u %u\n",BS[i]/P2,BS[i]%P2%p,BS[i]%P2/p); fclose(f); printf("WROTE %s\n",out); }
    return 0; }
