// independent BFS on Z_n x| Z_m: element (u,v), u in Z_n, v in Z_m; (u1,v1)(u2,v2)=(u1+u2, v1*r^u2+v2)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  long long m=atoll(argv[1]),n=atoll(argv[2]),r=atoll(argv[3]); int D=atoi(argv[4]); int H=(argc-5)/2;
  long long N=n*m; long long *rp=malloc(n*sizeof(long long)); rp[0]=1%m; for(long long i=1;i<n;i++) rp[i]=(__int128)rp[i-1]*r%m;
  if((__int128)rp[n-1]*r%m!=1%m){printf("r^n!=1\n");return 2;}
  int S=2*H; long long gu[64],gv[64];
  for(int i=0;i<H;i++){ long long u=atoll(argv[5+2*i]),v=atoll(argv[6+2*i]); gu[i]=u;gv[i]=v;
    long long iu=(n-u)%n; long long iv=(m-(long long)((__int128)v*rp[iu]%m))%m; gu[H+i]=iu; gv[H+i]=iv; }
  uint8_t*dist=malloc(N); for(long long i=0;i<N;i++) dist[i]=255;
  int32_t*q=malloc(N*sizeof(int32_t)); long long qh=0,qt=0; q[qt++]=0; dist[0]=0; long long cnt[64]={0}; cnt[0]=1; int ecc=0;
  while(qh<qt){ int32_t x=q[qh++]; long long u1=x/m,v1=x%m; int d=dist[x];
    for(int s=0;s<S;s++){ long long u=(u1+gu[s])%n; long long v=((__int128)v1*rp[gu[s]]+gv[s])%m; long long y=u*m+v;
      if(dist[y]==255){dist[y]=d+1;q[qt++]=y;cnt[d+1]++; if(d+1>ecc)ecc=d+1;} } }
  // check right-multiplication formula consistency: group is vertex-transitive so ecc from identity is the diameter
  printf("order=%lld reached=%lld degree=%d ecc=%d layers:",N,qt,S,ecc); for(int i=0;i<=ecc;i++)printf(" %lld",cnt[i]); printf("\n");
  printf(qt==N&&ecc==D?"VERIFIED_OK\n":"FAIL\n"); return 0; }
