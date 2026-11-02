// affsearch: Haar graph H(G,S), G = F_q x| C_k, q = P^E, (a,j)(b,l) = (a + w^j b, j+l), w = x^((q-1)/k), x primitive.
// alpha(a,j) = (a^(P^I), P^I j mod k), order ORD = E/gcd(E,I). Edges (g,A)~(s g,B).
// Cost of S = #vertices not within D of (e,A) + #vertices not within D of (e,B). Cost 0 = diameter <= D (G transitive on each side).
// usage: affsearch P E K I D secs seed mode OUT
//   mode O: S = {e, f} + one alpha-orbit (size ORD)           (Delta = 2 + ORD)
//   mode F: S = {f1, f2} + one alpha-orbit (no e)            (Delta = 2 + ORD), f1,f2 alpha-fixed non-identity
//   mode R: 5 random distinct elements (no symmetry, baseline)
// Writes OUT.sol (header "P E K I D c0..c(E-1)" then the 5 elements as "a j") on cost 0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
static double wall(void){struct timeval tv;gettimeofday(&tv,0);return tv.tv_sec+1e-6*tv.tv_usec;}
#include <stdint.h>

static int P,E,K,I,Q,QM1,STEP,N,D,ORD,PI;
static int *EXPT,*LOGT,PW[32];
static unsigned char *dA,*dB;
static int *queue;
static uint64_t rs=88172645463325252ULL;
static uint64_t rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static int rndint(int n){return (int)(rnd()%(uint64_t)n);}

static int addF(int a,int b){int r=0;for(int t=0;t<E;t++){r+=((a%P+b%P)%P)*PW[t];a/=P;b/=P;}return r;}
static int negF(int a){int r=0;for(int t=0;t<E;t++){r+=((P-a%P)%P)*PW[t];a/=P;}return r;}
static int mulF(int a,int b){if(!a||!b)return 0;return EXPT[(LOGT[a]+LOGT[b])%QM1];}
static int mulx(int v,const int*c){
  int dig[32],nd[32],tmp=v;
  for(int t=0;t<E;t++){dig[t]=tmp%P;tmp/=P;}
  int top=dig[E-1];
  nd[0]=0;for(int t=1;t<E;t++)nd[t]=dig[t-1];
  for(int t=0;t<E;t++)nd[t]=(((nd[t]-top*c[t])%P)+P)%P;
  int r=0;for(int t=0;t<E;t++)r+=nd[t]*PW[t];
  return r;
}
static int build_field(int*c){
  long total=1;for(int t=0;t<E;t++)total*=P;
  for(long code=0;code<total;code++){
    long cc=code;for(int t=0;t<E;t++){c[t]=cc%P;cc/=P;}
    if(c[0]==0)continue;
    int v=1,ok=1;EXPT[0]=1;
    for(int s=1;s<QM1;s++){
      v=mulx(v,c);
      if(v==0||v==1){ok=0;break;}
      EXPT[s]=v;
    }
    if(!ok)continue;
    if(mulx(v,c)!=1)continue;
    for(int s=0;s<QM1;s++)LOGT[EXPT[s]]=s;
    return 1;
  }
  return 0;
}
static int alphaG(int g){
  int a=g%Q,j=g/Q;
  int aa=a?EXPT[((long)LOGT[a]*PI)%QM1]:0;
  int jj=(int)(((long)PI*j)%K);
  return jj*Q+aa;
}
// S tables
static int M=5;
static int *MUf,*TRf,*MUi,*TRi,jf[8],ji[8];
static void setS(const int*S){
  for(int t=0;t<M;t++){
    int as=S[t]%Q, js=S[t]/Q;
    int lf=(int)(((long)js*STEP)%QM1);
    int li=(QM1-lf)%QM1;
    int b=negF(mulF(EXPT[li],as));   // s^{-1} = (b, -js), b = -(w^{-js} as)
    int *mf=MUf+t*Q,*tf=TRf+t*Q,*mi=MUi+t*Q,*ti=TRi+t*Q;
    for(int a=0;a<Q;a++){
      mf[a]=a?EXPT[(LOGT[a]+lf)%QM1]:0;
      tf[a]=addF(as,a);
      mi[a]=a?EXPT[(LOGT[a]+li)%QM1]:0;
      ti[a]=addF(b,a);
    }
    jf[t]=js; ji[t]=(K-js)%K;
  }
}
// BFS from (src,side) to depth D; returns number of vertices within distance D
static long bfs(int side,int src){
  memset(dA,255,N);memset(dB,255,N);
  int head=0,tail=0;
  if(side==0){dA[src]=0;queue[tail++]=src;} else {dB[src]=0;queue[tail++]=N+src;}
  while(head<tail){
    int v=queue[head++];
    int isB=v>=N; int g=isB?v-N:v;
    unsigned char dv=isB?dB[g]:dA[g];
    if(dv>=D)continue;
    int a=g%Q,j=g/Q;
    if(!isB){
      for(int t=0;t<M;t++){
        int a2=TRf[t*Q+MUf[t*Q+a]];
        int j2=jf[t]+j; if(j2>=K)j2-=K;
        int u=j2*Q+a2;
        if(dB[u]==255){dB[u]=dv+1;queue[tail++]=N+u;}
      }
    }else{
      for(int t=0;t<M;t++){
        int a2=TRi[t*Q+MUi[t*Q+a]];
        int j2=ji[t]+j; if(j2>=K)j2-=K;
        int u=j2*Q+a2;
        if(dA[u]==255){dA[u]=dv+1;queue[tail++]=u;}
      }
    }
  }
  return tail;
}
int main(int argc,char**argv){
  if(argc<10){fprintf(stderr,"usage: P E K I D secs seed mode OUT\n");return 1;}
  P=atoi(argv[1]);E=atoi(argv[2]);K=atoi(argv[3]);I=atoi(argv[4]);D=atoi(argv[5]);
  double secs=atof(argv[6]);
  rs=strtoull(argv[7],0,10)*2654435761ULL+12345ULL;
  char mode=argv[8][0]; const char*OUT=argv[9];
  PW[0]=1;for(int t=1;t<E;t++)PW[t]=PW[t-1]*P;
  Q=PW[E-1]*P; QM1=Q-1;
  if(QM1%K){fprintf(stderr,"K must divide q-1\n");return 1;}
  STEP=QM1/K; N=Q*K;
  int a1=E,b1=I;while(b1){int tt=a1%b1;a1=b1;b1=tt;}
  ORD=E/a1; PI=1;for(int t=0;t<I;t++)PI*=P;
  EXPT=malloc(sizeof(int)*QM1); LOGT=malloc(sizeof(int)*Q);
  int cpoly[32];
  if(!build_field(cpoly)){fprintf(stderr,"no field\n");return 1;}
  MUf=malloc(sizeof(int)*M*Q);TRf=malloc(sizeof(int)*M*Q);MUi=malloc(sizeof(int)*M*Q);TRi=malloc(sizeof(int)*M*Q);
  dA=malloc(N);dB=malloc(N);queue=malloc(sizeof(int)*2*(size_t)N);
  int *fix=malloc(sizeof(int)*N);int nfix=0;
  for(int g=1;g<N;g++)if(alphaG(g)==g)fix[nfix++]=g;
  fprintf(stderr,"q=%d k=%d N=%d 2N=%d ORD=%d PI=%d |Fix\\{e}|=%d primitive-check ok\n",Q,K,N,2*N,ORD,PI,nfix);
  if(M!=2+ORD && mode!='R'){fprintf(stderr,"mode needs Delta=%d; orbit size ORD=%d\n",2+ORD,ORD);}
  int S[8];
  long best=-1; long nsamp=0,nB=0; double t0=wall();
  long hist[4]={0,0,0,0};
  while(wall()-t0 < secs){
    nsamp++;
    if(mode=='R'){
      int ok=1;
      for(int t=0;t<M;t++){S[t]=rndint(N);for(int u=0;u<t;u++)if(S[u]==S[t])ok=0;}
      if(!ok)continue;
    } else {
      int s,ok=1;
      s=rndint(N);
      if(mode=='L'){ static long it=0; int aa,jj; sscanf(getenv("REP"),"%d %d",&aa,&jj); s=jj*Q+aa; if(it>=nfix)break; }
      // orbit of s must have size ORD
      int orb[8];orb[0]=s;for(int t=1;t<ORD;t++)orb[t]=alphaG(orb[t-1]);
      for(int t=1;t<ORD;t++)if(orb[t]==s)ok=0;
      if(!ok)continue;
      int idx=0;
      if(mode=='L'){ static long it2=0; S[idx++]=0; S[idx++]=fix[it2++ % nfix]; }
      else if(mode=='O'){ S[idx++]=0; S[idx++]=fix[rndint(nfix)]; }
      else { int f1=fix[rndint(nfix)],f2=fix[rndint(nfix)]; if(f1==f2)continue; S[idx++]=f1; S[idx++]=f2; }
      for(int t=0;t<ORD;t++)S[idx++]=orb[t];
      if(idx!=M)continue;
      for(int u=0;u<M;u++)for(int v=0;v<u;v++)if(S[u]==S[v])ok=0;
      if(!ok)continue;
    }
    setS(S);
    long costA=2L*N-bfs(0,0);
    long cost=costA;
    if(costA<=30){ long costB=2L*N-bfs(1,0); cost=costA+costB; nB++; }
    if(cost<4){hist[cost]++;} else hist[3]++;
    if(best<0||cost<best){
      best=cost;
      fprintf(stderr,"sample %ld t=%.1fs cost=%ld (A %ld) S=",nsamp,(wall()-t0),cost,costA);
      for(int t=0;t<M;t++)fprintf(stderr,"(%d,%d)",S[t]%Q,S[t]/Q);
      fprintf(stderr,"\n");
    }
    if(cost==0){
      char fn[512];sprintf(fn,"%s.sol",OUT);
      FILE*f=fopen(fn,"w");
      fprintf(f,"%d %d %d %d %d",P,E,K,I,D);
      for(int t=0;t<E;t++)fprintf(f," %d",cpoly[t]);
      fprintf(f,"\n");
      for(int t=0;t<M;t++)fprintf(f,"%d %d\n",S[t]%Q,S[t]/Q);
      fclose(f);
      fprintf(stderr,"FOUND cost 0, wrote %s\n",fn);
      break;
    }
  }
  fprintf(stderr,"done: samples=%ld fullBFS=%ld best=%ld hist(0,1,2,3+)=%ld,%ld,%ld,%ld time=%.1fs\n",
    nsamp,nB,best,hist[0],hist[1],hist[2],hist[3],(wall()-t0));
  printf("%ld %ld\n",best,nsamp);
  return 0;
}
