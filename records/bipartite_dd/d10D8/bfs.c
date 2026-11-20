#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
#define D 10
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb"); long nsamp=atol(argv[2]);
  fseek(f,0,SEEK_END); long sz=ftell(f); rewind(f);
  int32_t n=sz/(4*D); int32_t*adj=malloc(sz); if(fread(adj,1,sz,f)!=sz) return 2;
  printf("n=%d\n",n);
  // simple, degree exactly D, distinct, symmetric
  long bad=0;
  for(int v=0;v<n;v++){ for(int i=0;i<D;i++){ int u=adj[(long)v*D+i];
      if(u<0||u>=n||u==v){bad++;continue;}
      for(int j=0;j<i;j++) if(adj[(long)v*D+j]==u) bad++;
      int ok=0; for(int j=0;j<D;j++) if(adj[(long)u*D+j]==v) ok=1; if(!ok) bad++; } }
  printf("structural violations (loop/range/dup/asymmetry)=%ld\n",bad);
  long edges=(long)n*D/2; printf("edges=%ld degree=%d-regular\n",edges,D);
  // bipartite check by sides 0..n/2-1 / n/2..n-1
  long cross=0; for(int v=0;v<n;v++) for(int i=0;i<D;i++) if((v<n/2)==(adj[(long)v*D+i]<n/2)) cross++;
  printf("same-side edges=%ld\n",cross);
  int maxecc=0, minecc=99; long unreach=0;
  uint64_t seed=12345;
  int *src=malloc(sizeof(int)*(nsamp+2)); src[0]=0; src[1]=n/2;
  for(long i=0;i<nsamp;i++){ seed=seed*6364136223846793005ULL+1442695040888963407ULL; src[i+2]=(seed>>20)%n; }
  #pragma omp parallel
  {
    int8_t*dist=malloc(n); int*q=malloc(sizeof(int)*n);
    #pragma omp for schedule(dynamic,4)
    for(long s=0;s<nsamp+2;s++){
      memset(dist,-1,n); int h=0,t=0; q[t++]=src[s]; dist[src[s]]=0; int ecc=0;
      while(h<t){int v=q[h++]; int dv=dist[v]; for(int i=0;i<D;i++){int u=adj[(long)v*D+i]; if(dist[u]<0){dist[u]=dv+1;q[t++]=u; ecc=dv+1;}}}
      #pragma omp critical
      { if(t<n) unreach+=n-t; if(ecc>maxecc)maxecc=ecc; if(ecc<minecc)minecc=ecc;
        if(s<2){ long cnt[16]={0}; for(int v=0;v<n;v++) if(dist[v]>=0) cnt[dist[v]]++; printf("source %d levels:",src[s]); for(int k=0;k<=ecc;k++) printf(" %ld",cnt[k]); printf(" reached=%d\n",t);} }
    }
  }
  printf("sources=%ld min ecc=%d max ecc=%d unreached total=%ld\n",nsamp+2,minecc,maxecc,unreach);
}
