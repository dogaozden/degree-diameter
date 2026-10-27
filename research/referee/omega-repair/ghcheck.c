// Check that the incidence graph of a point-line geometry (hex_q.txt) is a generalized hexagon of order (q,q):
// every vertex has sphere sizes 1, q+1, (q+1)q, ..., (q+1)q^4, q^5 (64-source bit-parallel BFS from all vertices).
// That means girth >= 12 and diameter 6 (the bipartite Moore bound is met).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int q,N; if(fscanf(f,"%d %d",&q,&N)!=2) return 1;
  int V=2*N, k=q+1;
  int *adj=malloc(sizeof(int)*V*k), *dg=calloc(V,sizeof(int));
  for(int l=0;l<N;l++) for(int j=0;j<k;j++){int p; if(fscanf(f,"%d",&p)!=1) return 1; adj[(N+l)*k+dg[N+l]++]=p; adj[p*k+dg[p]++]=N+l;}
  for(int v=0;v<V;v++) if(dg[v]!=k){printf("degree fail\n");return 1;}
  long expect[7]; expect[0]=1; expect[1]=k; for(int i=2;i<=5;i++) expect[i]=expect[i-1]*q; expect[6]=(long)q*q*q*q*q;
  uint64_t *seen=malloc(8*V),*fr=malloc(8*V),*nx=malloc(8*V);
  long bad=0;
  for(int s0=0;s0<V;s0+=64){
    int ns=V-s0<64?V-s0:64;
    for(int v=0;v<V;v++){seen[v]=0;fr[v]=0;}
    for(int i=0;i<ns;i++){seen[s0+i]|=1ULL<<i; fr[s0+i]|=1ULL<<i;}
    for(int r=1;r<=7;r++){
      long cnt[64]={0};
      for(int v=0;v<V;v++){uint64_t m=0; for(int j=0;j<k;j++) m|=fr[adj[v*k+j]]; m&=~seen[v]; nx[v]=m;}
      for(int v=0;v<V;v++){seen[v]|=nx[v]; uint64_t m=nx[v]; while(m){cnt[__builtin_ctzll(m)]++; m&=m-1;}}
      uint64_t*t=fr;fr=nx;nx=t;
      for(int i=0;i<ns;i++){ long e=r<=6?expect[r]:0; if(cnt[i]!=e) bad++; }
    }
  }
  printf("q=%d V=%d: vertices with a sphere of wrong size: %ld -> %s\n",q,V,bad,bad?"FAIL":"generalized hexagon of order (q,q)");
  return 0;
}
