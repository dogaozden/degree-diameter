/* a14: Haar graph H(G,S) on G = SL(2,8) x Z_p (p = 1 mod 7), S = one free orbit of
   alpha(M,z) = (g M g^-1, u z), g = diag(t,t^-1) of order 7 (t generates GF(8)*), u of order 7 mod p.
   Fix(alpha) = {(M,0): M in torus} has 7 elements.  Bitset BFS from (e,A):
   B-level = S * A-frontier, A-level = S^-1 * B-frontier.  Cost = unvisited B within 11, unvisited A within 12.
   usage: orb7 p seed nsamples            (random orbits, prints cost per sample)
          orb7 p 0 1 M0 z0                (evaluate one orbit of x0=(M0,z0), prints S and cost) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int gfm(int a,int b){int r=0;for(int i=0;i<3;i++)if(b>>i&1)r^=a<<i;
  for(int i=4;i>=3;i--)if(r>>i&1)r^=0xB<<(i-3);return r;}
static int mats[504][4]; static int idx[4096]; static int nm=0;
static uint16_t Lm[504][504];
static int mmul(int x,int y){ /* index product */
  int a1=mats[x][0],b1=mats[x][1],c1=mats[x][2],d1=mats[x][3];
  int a2=mats[y][0],b2=mats[y][1],c2=mats[y][2],d2=mats[y][3];
  int a=gfm(a1,a2)^gfm(b1,c2), b=gfm(a1,b2)^gfm(b1,d2), c=gfm(c1,a2)^gfm(d1,c2), d=gfm(c1,b2)^gfm(d1,d2);
  return idx[((a*8+b)*8+c)*8+d]; }
static int minv(int x){ return idx[((mats[x][3]*8+mats[x][1])*8+mats[x][2])*8+mats[x][0]]; }
static long p, N; static int W; static int idm, cg[504], u;
static inline long enc(int M,long z){return z*504+M;}
static uint64_t *visA,*visB,*fr,*nx; static int verbose=0;

static long cost(int k, int *SM, long *SZ, long *holesA, long *holesB){
  int sm[16],si[16]; long sz[16],sinv_z[16];
  for(int i=0;i<k;i++){ sm[i]=SM[i]; sz[i]=SZ[i]; si[i]=minv(SM[i]); sinv_z[i]=(p-SZ[i])%p; }
  memset(visA,0,W*8); memset(visB,0,W*8); memset(fr,0,W*8); memset(nx,0,W*8);
  long e=enc(idm,0); visA[e>>6]|=1ULL<<(e&63); fr[e>>6]|=1ULL<<(e&63);
  long cntB=0, cntA=1;
  for(int lev=1;lev<=12;lev++){
    int odd=lev&1; uint64_t *vis = odd?visB:visA; memset(nx,0,W*8);
    int *MM = odd?sm:si; long *ZZ = odd?sz:sinv_z;
    for(int w=0;w<W;w++){ uint64_t word=fr[w];
      while(word){ int b=__builtin_ctzll(word); word&=word-1; long x=(long)w*64+b;
        long z=x/504; int M=(int)(x-z*504);
        for(int i=0;i<k;i++){ long zz=z+ZZ[i]; if(zz>=p) zz-=p;
          long y=zz*504+Lm[MM[i]][M];
          uint64_t bit=1ULL<<(y&63); if(!(vis[y>>6]&bit)){ vis[y>>6]|=bit; nx[y>>6]|=bit; if(odd)cntB++; else cntA++; } } } }
    if(lev==11){ *holesB = N-cntB; }
    if(verbose) fprintf(stderr,"LEV %d cumB %ld cumA %ld\n",lev,cntB,cntA);
    uint64_t *t=fr; fr=nx; nx=t;
  }
  *holesA = N-cntA;
  return *holesB + *holesA; /* only B<=11 matters; A<=12 reported */
}

int main(int argc,char**argv){
  p=atol(argv[1]); unsigned long seed=strtoul(argv[2],0,10); int ns=atoi(argv[3]);
  N=504*p; W=(N+63)/64;
  /* GF(8) SL(2,8) enumeration */
  for(int a=0;a<8;a++)for(int b=0;b<8;b++)for(int c=0;c<8;c++)for(int d=0;d<8;d++)
    if((gfm(a,d)^gfm(b,c))==1){ mats[nm][0]=a;mats[nm][1]=b;mats[nm][2]=c;mats[nm][3]=d; idx[((a*8+b)*8+c)*8+d]=nm; nm++; }
  if(nm!=504){fprintf(stderr,"bad SL count %d\n",nm);return 1;}
  for(int i=0;i<504;i++)for(int j=0;j<504;j++)Lm[i][j]=mmul(i,j);
  idm=idx[((1*8+0)*8+0)*8+1];
  /* t = x (=2) generator of GF(8)*, g = diag(t, t^-1) */
  int t=2, tinv=0; for(int i=1;i<8;i++) if(gfm(t,i)==1) tinv=i;
  int g=idx[((t*8+0)*8+0)*8+tinv], gi=minv(g);
  for(int M=0;M<504;M++) cg[M]=mmul(mmul(g,M),gi);
  /* u of order 7 mod p */
  u=0; for(long h=2;h<p && !u;h++){ long v=1,base=h,e=(p-1)/7; while(e){ if(e&1)v=v*base%p; base=base*base%p; e>>=1; }
    if(v!=1) u=(int)v; }
  visA=malloc(W*8);visB=malloc(W*8);fr=malloc(W*8);nx=malloc(W*8);
  uint64_t rs=seed*2654435761ULL+12345; 
  #define RND() (rs^=rs<<13,rs^=rs>>7,rs^=rs<<17,rs)
  int SM[7]; long SZ[7];
  if(argc>=6){ int M0=atoi(argv[4]); long z0=atol(argv[5]);
    for(int i=0;i<7;i++){ SM[i]=M0; SZ[i]=z0; long z=z0; int M=M0; (void)z; }
    /* orbit: alpha^i(x0) = (cg^i M0, u^i z0) */
    int Mi=M0; long zi=z0; for(int i=0;i<7;i++){ SM[i]=Mi; SZ[i]=zi; Mi=cg[Mi]; zi=(zi*u)%p; }
    verbose=1; long hA,hB; long c=cost(7,SM,SZ,&hA,&hB); verbose=0;
    for(int i=0;i<7;i++) printf("S %d %ld\n",SM[i],SZ[i]);
    printf("RESULT p=%ld N=%ld u=%d holesB11=%ld holesA12=%ld cost=%ld\n",p,N,u,hB,hA,c);
    return 0; }
  for(int s=0;s<ns;s++){
    int M0; long z0;
    do{ M0=RND()%504; z0=RND()%p; }while(z0==0 && cg[M0]==M0);
    int Mi=M0; long zi=z0; for(int i=0;i<7;i++){ SM[i]=Mi; SZ[i]=zi; Mi=cg[Mi]; zi=(zi*u)%p; }
    if(getenv("RANDS")){ for(int i=0;i<7;i++){ SM[i]=RND()%504; SZ[i]=RND()%p; } } /* baseline: 7 free random elements */
    if(s==0 && getenv("VERB")) for(int i=0;i<7;i++) printf("S %d %ld\n",SM[i],SZ[i]);
    long hA,hB; clock_t c0=clock(); verbose=(s==0 && getenv("VERB")); long c=cost(7,SM,SZ,&hA,&hB); verbose=0;
    printf("sample %d x0=(%d,%ld) holesB11=%ld holesA12=%ld time=%.2fs\n",s,M0,z0,hB,hA,(double)(clock()-c0)/CLOCKS_PER_SEC);
    fflush(stdout);
  }
  return 0;
}
