/* Bit-parallel all-pairs BFS: reads "n m" then m lines "u v" (0-based) from stdin.
   Prints: n, m, max degree, bipartite?, connected?, diameter.  Optional argv[1]=limit:
   only sources 0..limit-1 (prints max eccentricity over those). Written for the referee check. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc,char**argv){
  int n; long m; if(scanf("%d %ld",&n,&m)!=2) return 1;
  int *eu=malloc(sizeof(int)*m),*ev=malloc(sizeof(int)*m),*deg=calloc(n,sizeof(int));
  for(long i=0;i<m;i++){ if(scanf("%d %d",&eu[i],&ev[i])!=2) return 1; if(eu[i]==ev[i]){printf("loop\n");return 1;} deg[eu[i]]++;deg[ev[i]]++;}
  long *off=malloc(sizeof(long)*(n+1)); off[0]=0; int maxd=0;
  for(int i=0;i<n;i++){off[i+1]=off[i]+deg[i]; if(deg[i]>maxd)maxd=deg[i];}
  int *adj=malloc(sizeof(int)*2*m); long *pos=malloc(sizeof(long)*n); for(int i=0;i<n;i++)pos[i]=off[i];
  for(long i=0;i<m;i++){adj[pos[eu[i]]++]=ev[i];adj[pos[ev[i]]++]=eu[i];}
  /* simple-graph check */
  int multi=0; int *mark=malloc(sizeof(int)*n); for(int i=0;i<n;i++)mark[i]=-1;
  for(int v=0;v<n;v++){for(long k=off[v];k<off[v+1];k++){int u=adj[k]; if(mark[u]==v)multi=1; mark[u]=v;}}
  /* bipartite + connected from vertex 0 */
  int *col=malloc(sizeof(int)*n); for(int i=0;i<n;i++)col[i]=-1; int *qu=malloc(sizeof(int)*n); int h=0,t=0; col[0]=0;qu[t++]=0; int bip=1;
  while(h<t){int v=qu[h++]; for(long k=off[v];k<off[v+1];k++){int u=adj[k]; if(col[u]<0){col[u]=1-col[v];qu[t++]=u;} else if(col[u]==col[v]) bip=0;}}
  int conn=(t==n);
  int limit=n; if(argc>1) limit=atoi(argv[1]); if(limit>n)limit=n;
  int diam=0;
  if(conn){
  #pragma omp parallel
  {
    uint64_t *vis=malloc(8*(size_t)n),*fr=malloc(8*(size_t)n),*nx=malloc(8*(size_t)n);
    int locd=0;
    #pragma omp for schedule(dynamic)
    for(int b=0;b<limit;b+=64){
      memset(vis,0,8*(size_t)n); memset(fr,0,8*(size_t)n);
      int cnt=(limit-b<64)?limit-b:64; uint64_t full=(cnt==64)?~0ULL:((1ULL<<cnt)-1);
      for(int j=0;j<cnt;j++){vis[b+j]|=1ULL<<j; fr[b+j]|=1ULL<<j;}
      int r=0;
      while(1){
        int any=0;
        for(int v=0;v<n;v++){uint64_t x=0; for(long k=off[v];k<off[v+1];k++) x|=fr[adj[k]]; x&=~vis[v]; nx[v]=x; if(x)any=1;}
        if(!any)break; r++;
        for(int v=0;v<n;v++){vis[v]|=nx[v];}
        uint64_t*tmp=fr;fr=nx;nx=tmp;
      }
      for(int v=0;v<n;v++) if((vis[v]&full)!=full){printf("disconnected?\n");}
      if(r>locd)locd=r;
    }
    #pragma omp critical
    { if(locd>diam)diam=locd; }
    free(vis);free(fr);free(nx);
  }
  }
  printf("n=%d m=%ld maxdeg=%d simple=%d bipartite=%d connected=%d %s=%d\n",n,m,maxd,!multi,bip,conn,limit==n?"diameter":"max_ecc_of_sources",diam);
  return 0;
}
