// read: n m, then m edges (u v); print n, m, maxdeg, mindeg, bipartite?, diameter (-1 if disconnected)
#include <stdio.h>
#include <stdlib.h>
int main(){int n,m; if(scanf("%d %d",&n,&m)!=2)return 1;
 int *eu=malloc(sizeof(int)*m),*ev=malloc(sizeof(int)*m),*deg=calloc(n,sizeof(int));
 for(int i=0;i<m;i++){scanf("%d %d",&eu[i],&ev[i]);deg[eu[i]]++;deg[ev[i]]++;}
 int *off=malloc(sizeof(int)*(n+1));off[0]=0;for(int i=0;i<n;i++)off[i+1]=off[i]+deg[i];
 int *adj=malloc(sizeof(int)*2*m),*pos=calloc(n,sizeof(int));
 for(int i=0;i<m;i++){adj[off[eu[i]]+pos[eu[i]]++]=ev[i];adj[off[ev[i]]+pos[ev[i]]++]=eu[i];}
 int mx=0,mn=1<<30;for(int i=0;i<n;i++){if(deg[i]>mx)mx=deg[i];if(deg[i]<mn)mn=deg[i];}
 int *dist=malloc(sizeof(int)*n),*q=malloc(sizeof(int)*n);int diam=0,bip=1;
 for(int s=0;s<n;s++){for(int i=0;i<n;i++)dist[i]=-1;dist[s]=0;int h=0,t=0;q[t++]=s;
  while(h<t){int u=q[h++];for(int k=off[u];k<off[u+1];k++){int w=adj[k];if(dist[w]<0){dist[w]=dist[u]+1;q[t++]=w;}else if(dist[w]==dist[u])bip=0;}}
  if(t<n){diam=-1;break;} if(dist[q[t-1]]>diam)diam=dist[q[t-1]];}
 // check multi-edges
 printf("n=%d m=%d maxdeg=%d mindeg=%d bipartite=%d diameter=%d\n",n,m,mx,mn,bip,diam);return 0;}
