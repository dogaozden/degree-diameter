/* farpair EDGES LO HI: BFS from every vertex in [LO,HI); report pairs at distance > 5 (first 10) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){ FILE*f=fopen(argv[1],"r"); int n; fscanf(f,"%d",&n); int lo=atoi(argv[2]),hi=atoi(argv[3]);
 int *eu=malloc(sizeof(int)*n*20), *ev=malloc(sizeof(int)*n*20); int m=0,u,v; int *deg=calloc(n,4);
 while(fscanf(f,"%d %d",&u,&v)==2){eu[m]=u;ev[m]=v;m++;deg[u]++;deg[v]++;} fclose(f);
 int *off=calloc(n+1,4); for(int i=0;i<n;i++) off[i+1]=off[i]+deg[i]; int *fill=calloc(n,4); int *adj=malloc(sizeof(int)*2*m);
 for(int i=0;i<m;i++){ adj[off[eu[i]]+fill[eu[i]]++]=ev[i]; adj[off[ev[i]]+fill[ev[i]]++]=eu[i]; }
 int *dist=malloc(4*n), *q=malloc(4*n); int shown=0; long bad=0;
 for(int s=lo;s<hi;s++){ for(int i=0;i<n;i++) dist[i]=-1; dist[s]=0; int h=0,t=0; q[t++]=s;
   while(h<t){int x=q[h++]; for(int k=off[x];k<off[x+1];k++){int y=adj[k]; if(dist[y]<0){dist[y]=dist[x]+1; q[t++]=y;}}}
   for(int i=0;i<n;i++) if(dist[i]<0||dist[i]>5){ bad++; if(shown<10){ printf("src %d tgt %d dist %d\n",s,i,dist[i]); shown++; } } }
 printf("total bad pairs from range: %ld\n",bad); return 0; }
