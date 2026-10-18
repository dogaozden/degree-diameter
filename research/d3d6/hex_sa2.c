/* Simulated annealing for "Theorem C" copies in a generalized hexagon of order (q,q), Delta = q+2.
   States: cP[p], cL[L] in {0 none, 1 mixed copy, 2 pure copy (twin)}.
   Constraints (see REPORT.md):
     line L : #C on L <= 1 + [L pure],   #W on L <= 1
     point p: #D thru p <= 1 + [p pure], #T thru p <= 1
   Usage: hex_sa inst.txt seconds seed lambda out.txt [init.txt]
   inst.txt: N k  then N lines of k point ids (line k's points). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int N, K; static double CYC=4;
static int *lp;   /* lines -> points, N*K */
static int *pl;   /* points -> lines, N*K */
static int *cP, *cL, *nC, *nW, *nD, *nT, *fP, *prL, *prP; static int PAIRS=1;
static unsigned long long rs; static double T0g=0.6;
static inline unsigned long long rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }

static inline int vline(int L){ int v = nC[L] + prL[L] - 1 - (cL[L]==2); if(v<0)v=0; int w = nW[L]+prL[L]-1; if(w<0)w=0; return v+w; }
static inline int vpt(int p){ int v = nD[p] + prP[p] - 1 - (cP[p]==2); if(v<0)v=0; int w = nT[p]+prP[p]-1; if(w<0)w=0; return v+w; }

/* delta of violation if point p goes to state s */
static int dpoint(int p, int s){
    int old = cP[p], d = 0, i;
    if(old==s) return 0;
    int dc = (s>0)-(old>0), dw = (s==2)-(old==2);
    for(i=0;i<K;i++){ int L = pl[p*K+i]; int b = vline(L); nC[L]+=dc; nW[L]+=dw; d += vline(L)-b; nC[L]-=dc; nW[L]-=dw; }
    int b = vpt(p); cP[p]=s; d += vpt(p)-b; cP[p]=old;
    return d;
}
static void setpoint(int p, int s){
    int old = cP[p], i; int dc = (s>0)-(old>0), dw = (s==2)-(old==2);
    for(i=0;i<K;i++){ int L = pl[p*K+i]; nC[L]+=dc; nW[L]+=dw; }
    cP[p]=s;
}
static int dline(int L, int s){
    int old = cL[L], d = 0, i;
    if(old==s) return 0;
    int dc = (s>0)-(old>0), dw = (s==2)-(old==2);
    for(i=0;i<K;i++){ int p = lp[L*K+i]; int b = vpt(p); nD[p]+=dc; nT[p]+=dw; d += vpt(p)-b; nD[p]-=dc; nT[p]-=dw; }
    int b = vline(L); cL[L]=s; d += vline(L)-b; cL[L]=old;
    return d;
}
static void setline(int L, int s){
    int old = cL[L], i; int dc = (s>0)-(old>0), dw = (s==2)-(old==2);
    for(i=0;i<K;i++){ int p = lp[L*K+i]; nD[p]+=dc; nT[p]+=dw; }
    cL[L]=s;
}

/* pair (P, L = pl[P*K+f]): loads lines through P except L and points of L except P */
static void pairload(int P, int f, int s){
    int i, L = pl[P*K+f];
    for(i=0;i<K;i++){ int M = pl[P*K+i]; if(M!=L) prL[M]+=s; }
    for(i=0;i<K;i++){ int x = lp[L*K+i]; if(x!=P) prP[x]+=s; }
}
static int vaffect(int P, int f){ /* violation sum over affected elements */
    int i, L = pl[P*K+f], v=0;
    for(i=0;i<K;i++){ int M = pl[P*K+i]; if(M!=L) v+=vline(M); }
    for(i=0;i<K;i++){ int x = lp[L*K+i]; if(x!=P) v+=vpt(x); }
    return v;
}
static int dpair(int P, int nf){
    int of = fP[P], d=0;
    if(of==nf) return 0;
    if(of>=0){ int b=vaffect(P,of); pairload(P,of,-1); d += vaffect(P,of)-b; }
    if(nf>=0){ int b=vaffect(P,nf); pairload(P,nf,1); d += vaffect(P,nf)-b; pairload(P,nf,-1); }
    if(of>=0) pairload(P,of,1);
    return d;
}
static void setpair(int P, int nf){ if(fP[P]>=0) pairload(P,fP[P],-1); if(nf>=0) pairload(P,nf,1); fP[P]=nf; }

int main(int argc, char **argv){
    if(argc<6){ fprintf(stderr,"usage\n"); return 1; }
    FILE *f = fopen(argv[1],"r"); double secs = atof(argv[2]); rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[3])*2654435761ULL;
    double lam = atof(argv[4]); if(getenv("CYC")) CYC=atof(getenv("CYC")); if(getenv("T0")) T0g=atof(getenv("T0"));
    if(fscanf(f,"%d %d",&N,&K)!=2) return 1;
    lp = malloc(sizeof(int)*N*K); pl = malloc(sizeof(int)*N*K);
    int *cnt = calloc(N,sizeof(int)), i, j;
    for(i=0;i<N;i++) for(j=0;j<K;j++){ int p; if(fscanf(f,"%d",&p)!=1) return 1; lp[i*K+j]=p; pl[p*K+cnt[p]++]=i; }
    fclose(f);
    cP=calloc(N,sizeof(int)); cL=calloc(N,sizeof(int)); nC=calloc(N,sizeof(int)); nW=calloc(N,sizeof(int)); nD=calloc(N,sizeof(int)); nT=calloc(N,sizeof(int));
    int *bP=calloc(N,sizeof(int)), *bL=calloc(N,sizeof(int)), *bF=malloc(N*sizeof(int));
    fP=malloc(N*sizeof(int)); prL=calloc(N,sizeof(int)); prP=calloc(N,sizeof(int)); for(i=0;i<N;i++){fP[i]=-1;bF[i]=-1;} if(getenv("PAIRS")) PAIRS=atoi(getenv("PAIRS"));
    if(argc>6){ FILE *g=fopen(argv[6],"r"); int t,x,s; while(fscanf(g,"%d %d %d",&t,&x,&s)==3){ if(t==0) setpoint(x,s); else if(t==1) setline(x,s); else setpair(x,s);} fclose(g); }
    long size=0, viol=0;
    for(i=0;i<N;i++){ size += (cP[i]>0)+(cL[i]>0); viol += vline(i)+vpt(i); }
    long best=-1; clock_t t0=clock(); long it=0;
    double T0=T0g, T1=0.05;
    for(;;it++){
        if((it&0xFFFF)==0){
            double el=(double)(clock()-t0)/CLOCKS_PER_SEC; if(el>secs) break;
            if((it&0xFFFFFF)==0) { fprintf(stderr,"t=%.0f size=%ld viol=%ld best=%ld\n",el,size,viol,best); }
        }
        double el=(double)(clock()-t0)/CLOCKS_PER_SEC; (void)el;
        double frac = 0; if((it&0xFF)==0){} 
        static double T=0.6; if((it&0xFFF)==0){ double e=(double)(clock()-t0)/CLOCKS_PER_SEC/secs; T = T0*pow(T1/T0, CYC>1? fmod(e*CYC,1.0) : e); }
        (void)frac;
        int isline = rnd()%(PAIRS?3:2); int x = rnd()%N; int s, old, dv, ds;
        if(isline==2){ s = (int)(rnd()%(K+1))-1; old=fP[x]; if(s==old) continue; dv=dpair(x,s); ds = 2*((s>=0)-(old>=0)); }
        else { s = rnd()%3; old = isline? cL[x]:cP[x]; if(s==old) continue;
        dv = isline? dline(x,s) : dpoint(x,s);
        ds = (s>0)-(old>0); }
        double de = ds - lam*dv;
        if(de>=0 || urand() < exp(de/T)){
            if(isline==2) setpair(x,s); else if(isline) setline(x,s); else setpoint(x,s);
            size += ds; viol += dv;
            if(viol==0 && size>best){
                best=size; memcpy(bP,cP,sizeof(int)*N); memcpy(bL,cL,sizeof(int)*N); memcpy(bF,fP,sizeof(int)*N);
            }
        }
    }
    int np=0,nl=0,wp=0,tl=0; for(i=0;i<N;i++){ np+=bP[i]>0; nl+=bL[i]>0; wp+=bP[i]==2; tl+=bL[i]==2; }
    int npair=0; for(i=0;i<N;i++) npair+=bF[i]>=0; fprintf(stderr,"done best=%ld (C=%d W=%d D=%d T=%d pairs=%d) iters=%ld\n",best,np,wp,nl,tl,npair,it);
    FILE *o=fopen(argv[5],"w"); for(i=0;i<N;i++){ if(bP[i]) fprintf(o,"0 %d %d\n",i,bP[i]); } for(i=0;i<N;i++){ if(bL[i]) fprintf(o,"1 %d %d\n",i,bL[i]); } for(i=0;i<N;i++){ if(bF[i]>=0) fprintf(o,"2 %d %d\n",i,bF[i]); } fclose(o);
    printf("%ld\n",best);
    return 0;
}
