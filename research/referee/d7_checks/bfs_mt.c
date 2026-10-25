/* referee's own checker: reads "n" then edge lines "a b"; checks simple, bipartite, max degree, BFS from every vertex */
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int n; if(fscanf(f,"%d",&n)!=1) return 1;
  int cap=1<<20,m=0,*ea=malloc(sizeof(int)*cap),*eb=malloc(sizeof(int)*cap),a,b;
  while(fscanf(f,"%d %d",&a,&b)==2){ if(m==cap){cap*=2;ea=realloc(ea,sizeof(int)*cap);eb=realloc(eb,sizeof(int)*cap);} ea[m]=a;eb[m]=b;m++; }
  int*deg=calloc(n,sizeof(int)); for(int i=0;i<m;i++){ if(ea[i]==eb[i]){printf("loop\n");return 1;} deg[ea[i]]++;deg[eb[i]]++; }
  int*off=malloc(sizeof(int)*(n+1)); off[0]=0; int maxd=0,mind=1<<30; for(int i=0;i<n;i++){off[i+1]=off[i]+deg[i]; if(deg[i]>maxd)maxd=deg[i]; if(deg[i]<mind)mind=deg[i];}
  int*adj=malloc(sizeof(int)*2*m),*pos=calloc(n,sizeof(int));
  for(int i=0;i<m;i++){adj[off[ea[i]]+pos[ea[i]]++]=eb[i]; adj[off[eb[i]]+pos[eb[i]]++]=ea[i];}
  /* multi-edge check */
  int*mark=malloc(sizeof(int)*n); for(int i=0;i<n;i++)mark[i]=-1; long dup=0;
  for(int v=0;v<n;v++) for(int k=off[v];k<off[v+1];k++){ if(mark[adj[k]]==v) dup++; mark[adj[k]]=v; }
  int diam=0; long far=0; int bip=1, disc=0;
  #pragma omp parallel for schedule(dynamic,64) reduction(max:diam) reduction(+:far) reduction(&:bip) reduction(|:disc)
  for(int s=0;s<n;s++){
    static __thread int *dist=0,*qu=0; if(!dist){dist=malloc(sizeof(int)*n);qu=malloc(sizeof(int)*n);}
    for(int i=0;i<n;i++)dist[i]=-1; int h=0,t=0; dist[s]=0; qu[t++]=s;
    while(h<t){int u=qu[h++]; for(int k=off[u];k<off[u+1];k++){int w=adj[k]; if(dist[w]<0){dist[w]=dist[u]+1;qu[t++]=w;} else if(s==0 && (dist[w]%2)==(dist[u]%2)) bip=0;}}
    if(t<n){disc=1;continue;}
    for(int i=0;i<n;i++){ if(dist[i]>diam)diam=dist[i]; if(dist[i]>7)far++; }
  }
  if(disc){printf("disconnected\n");return 1;}
  printf("n=%d m=%d dup=%ld degree min=%d max=%d bipartite=%d diameter=%d pairs>7=%ld\n",n,m,dup,mind,maxd,bip,diam,far);
  return 0;
}
