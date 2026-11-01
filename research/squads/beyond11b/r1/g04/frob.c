// Haar graph H(G,S) on G = F_q x| C_k (x -> a x + b, a in C_k <= GF(q)^*, k odd), q = p^e.
// Group element index g = i*q + b (a = zeta^(i*m), m=(q-1)/k, zeta primitive in GF(q)), identity = 0.
// Product (a,b)(a',b') = (a a', a b' + b).  Haar edges (g,A)~(s g,B).
// Cost = #vertices at distance > D from (e,A) plus from (e,B). Right-regular action makes these two BFS exact.
// usage: frob p e k Delta D secs seed OUT
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int p, e, q, k, m, Delta, D, N;
static int *expt, *lg;           // GF(q) exp (length q-1) and log tables
static uint8_t *dig;             // digits of field elements: dig[x*e+j] = coeff of x^j
static int coef[8];              // primitive poly x^e + sum coef[j] x^j
static int32_t **P, **Qp;        // P[j][g] = s_j g ; Qp[j][h] = s_j^{-1} h
static uint32_t *vis; static uint32_t stamp = 0; static int32_t *qu;
static double now(void){struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec;}

static int mulx_digits(int x){ // x * X mod poly
    int d[8], nd[8]; for(int j=0;j<e;j++) d[j]=dig[x*e+j];
    int t=d[e-1]; nd[0]=0; for(int j=1;j<e;j++) nd[j]=d[j-1];
    for(int j=0;j<e;j++) nd[j]=(nd[j]+t*((p-coef[j])%p))%p;
    int r=0,pw=1; for(int j=0;j<e;j++){ r+=nd[j]*pw; pw*=p; } return r;
}
static inline int fadd(int x,int y){ int r=0,pw=1; for(int j=0;j<e;j++){ int s=(dig[x*e+j]+dig[y*e+j])%p; r+=s*pw; pw*=p; } return r; }
static inline int fneg(int x){ int r=0,pw=1; for(int j=0;j<e;j++){ int s=(p-dig[x*e+j])%p; r+=s*pw; pw*=p; } return r; }
static inline int fmulexp(int la,int b){ if(b==0) return 0; return expt[(la + lg[b]) % (q-1)]; }

static int build_field(void){
    int *ex=malloc(sizeof(int)*q);
    int total=1; for(int j=0;j<e;j++) total*=p;
    for(int c=1;c<total;c++){
        int t=c; for(int j=0;j<e;j++){ coef[j]=t%p; t/=p; }
        if(coef[0]==0) continue;
        for(int x=0;x<q;x++){ int y=x; for(int j=0;j<e;j++){ dig[x*e+j]=y%p; y/=p; } }
        int cur=1, ok=1;
        for(int i=0;i<q-1;i++){ ex[i]=cur; cur=mulx_digits(cur); if(cur==1 && i<q-2){ ok=0; break; } }
        if(!ok || cur!=1) continue;
        for(int x=0;x<q;x++) lg[x]=-1;
        int good=1;
        for(int i=0;i<q-1;i++){ if(lg[ex[i]]!=-1){ good=0; break; } lg[ex[i]]=i; }
        if(!good) continue;
        memcpy(expt,ex,sizeof(int)*(q-1)); free(ex); return 1;
    }
    free(ex); return 0;
}
static inline int32_t mulg(int s,int g){ // s*g in index form
    int is=s/q, bs=s%q, ig=g/q, bg=g%q;
    int i2=is+ig; if(i2>=k) i2-=k;
    int b2=fadd(fmulexp(is*m,bg),bs);
    return i2*q+b2;
}
static inline int32_t invg(int s){
    int is=s/q, bs=s%q; int ii=(k-is)%k;
    int b=fneg(fmulexp(ii*m,bs));
    return ii*q+b;
}
static void set_gen(int j,int s){
    int si=invg(s);
    for(int g=0;g<N;g++){ P[j][g]=mulg(s,g); Qp[j][g]=mulg(si,g); }
}
// BFS from node start (node id < N: A-vertex g; >= N: B-vertex id-N) up to depth lim (lim<0: full).
// Returns number of nodes within distance lim (or all reached); *ecc = last level reached.
static long bfs(int start,int lim,int *ecc){
    stamp++; int tail=1,head=0; qu[0]=start; vis[start]=stamp;
    int level=0; long levelend=1;
    while(1){
        if(head==levelend){
            if(levelend==tail){ if(ecc) *ecc=level; return tail; }          // exhausted
            if(lim>=0 && level>=lim){ if(ecc) *ecc=level; return levelend; } // nodes at dist <= lim
            level++; levelend=tail;
        }
        int v=qu[head++];
        if(v<N){ for(int j=0;j<Delta;j++){ int u=N+P[j][v]; if(vis[u]!=stamp){ vis[u]=stamp; qu[tail++]=u; } } }
        else { int h=v-N; for(int j=0;j<Delta;j++){ int u=Qp[j][h]; if(vis[u]!=stamp){ vis[u]=stamp; qu[tail++]=u; } } }
    }
}
static long cost(void){
    long a=bfs(0,D,NULL); long b=bfs(N,D,NULL);
    return (2L*N-a)+(2L*N-b);
}
int main(int argc,char**argv){
    if(argc<9){ fprintf(stderr,"usage: frob p e k Delta D secs seed OUT\n"); return 1; }
    p=atoi(argv[1]); e=atoi(argv[2]); k=atoi(argv[3]); Delta=atoi(argv[4]); D=atoi(argv[5]);
    double secs=atof(argv[6]); unsigned seed=(unsigned)atoi(argv[7]); const char*OUT=argv[8];
    q=1; for(int j=0;j<e;j++) q*=p;
    if((q-1)%k){ fprintf(stderr,"k does not divide q-1\n"); return 1; }
    m=(q-1)/k; N=q*k;
    printf("# p=%d e=%d q=%d k=%d N=%d 2N=%d Delta=%d D=%d seed=%u\n",p,e,q,k,N,2*N,Delta,D,seed); fflush(stdout);
    expt=malloc(sizeof(int)*q); lg=malloc(sizeof(int)*q); dig=malloc((size_t)q*e);
    if(!build_field()){ fprintf(stderr,"no primitive poly\n"); return 1; }
    P=malloc(sizeof(int32_t*)*Delta); Qp=malloc(sizeof(int32_t*)*Delta);
    for(int j=0;j<Delta;j++){ P[j]=malloc(4L*N); Qp[j]=malloc(4L*N); }
    vis=calloc(2L*N,4); qu=malloc(4L*2*N);
    printf("# memory ~ %.1f MB\n",(2.0*Delta*4.0*N+12.0*N)/1e6); fflush(stdout);
    srand(seed); double t0=now();
    int S[16]; S[0]=0;
    if(getenv("SAMPLES")){   // size-law probe: independent random S, print unreached counts
        int ns=atoi(getenv("SAMPLES")); long sum=0, mn=-1;
        for(int r=0;r<ns && now()-t0<secs;r++){
            for(int j=1;j<Delta;j++){ int ok; do{ S[j]=1+rand()%(N-1); ok=1; for(int t=0;t<j;t++) if(S[t]==S[j]) ok=0; }while(!ok); }
            for(int j=0;j<Delta;j++) set_gen(j,S[j]);
            long a=2L*N-bfs(0,D,NULL), b=2L*N-bfs(N,D,NULL);
            printf("# sample %d unreachedA %ld unreachedB %ld t=%.1f\n",r,a,b,now()-t0); fflush(stdout);
            sum+=a+b; if(mn<0||a+b<mn) mn=a+b;
        }
        printf("# SAMPLES done: min cost %ld mean %.1f\n",mn, ns? (double)sum/ns : 0.0);
        return 0;
    }
    for(int j=1;j<Delta;j++){ int ok; do{ S[j]=1+rand()%(N-1); ok=1; for(int t=0;t<j;t++) if(S[t]==S[j]) ok=0; }while(!ok); }
    for(int j=0;j<Delta;j++) set_gen(j,S[j]);
    long cur=cost(); long best=cur;
    printf("# init cost %ld  t=%.1f\n",cur,now()-t0); fflush(stdout);
    long it=0;
    while(now()-t0<secs && cur>0){
        it++;
        int j=1+rand()%(Delta-1);
        int old=S[j]; int nw, ok;
        do{ nw=1+rand()%(N-1); ok=1; for(int t=0;t<Delta;t++) if(S[t]==nw) ok=0; }while(!ok);
        S[j]=nw; set_gen(j,nw);
        long c=cost();
        if(c<=cur){ cur=c; if(c<best){ best=c; printf("# it %ld cost %ld t=%.1f\n",it,c,now()-t0); fflush(stdout); } }
        else { S[j]=old; set_gen(j,old); }
    }
    printf("# done iters %ld best %ld cur %ld t=%.1f\n",it,best,cur,now()-t0);
    if(cur==0){
        int ecA=0,ecB=0;
        long a=bfs(0,-1,&ecA); long b=bfs(N,-1,&ecB);
        int diam = ecA>ecB?ecA:ecB;
        printf("# exact check: reached from (e,A) %ld, from (e,B) %ld of 2N=%d; ecc(eA)=%d ecc(eB)=%d -> diameter %d\n",a,b,2*N,ecA,ecB,diam);
        FILE*f=fopen(OUT,"w");
        fprintf(f,"# frob p=%d e=%d q=%d k=%d N=%d Delta=%d D=%d diameter=%d 2N=%d\n",p,e,q,k,N,Delta,D,diam,2*N);
        fprintf(f,"poly"); for(int j=0;j<e;j++) fprintf(f," %d",coef[j]); fprintf(f,"\n");
        fprintf(f,"S_index"); for(int j=0;j<Delta;j++) fprintf(f," %d",S[j]); fprintf(f,"\n");
        fprintf(f,"# g = i*q+b: a = zeta^(i*m) (zeta = root of poly, m=(q-1)/k), b = field element (digit j = coeff of x^j, base p)\n");
        fprintf(f,"# product (a,b)(a',b') = (a a', a b' + b); Haar edges (g,A)~(s g,B), s in S (S_index)\n");
        fclose(f);
        printf("written %s\n",OUT);
    }
    return 0;
}
