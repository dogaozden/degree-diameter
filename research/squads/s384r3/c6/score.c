/* score: number of unordered pairs at distance > 5 (or unreachable) in an edge list (first line N). Usage: score EDGES */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v){
    FILE *f=fopen(v[1],"r"); int n; if(!f||fscanf(f,"%d",&n)!=1) return 2;
    int *U=malloc(sizeof(int)*100000), *W=malloc(sizeof(int)*100000); int m=0,a,b;
    while(fscanf(f,"%d %d",&a,&b)==2){U[m]=a;W[m]=b;m++;}
    int *deg=calloc(n,sizeof(int)); for(int i=0;i<m;i++){deg[U[i]]++;deg[W[i]]++;}
    int maxd=0; for(int i=0;i<n;i++) if(deg[i]>maxd) maxd=deg[i];
    int *st=calloc(n+1,sizeof(int)); for(int i=0;i<n;i++) st[i+1]=st[i]+deg[i];
    int *adj=malloc(sizeof(int)*2*m), *pos=calloc(n,sizeof(int));
    for(int i=0;i<m;i++){adj[st[U[i]]+pos[U[i]]++]=W[i]; adj[st[W[i]]+pos[W[i]]++]=U[i];}
    int *dist=malloc(sizeof(int)*n), *q=malloc(sizeof(int)*n);
    long bad=0;
    for(int s=0;s<n;s++){
        for(int i=0;i<n;i++) dist[i]=-1;
        int h=0,t=0; q[t++]=s; dist[s]=0;
        while(h<t){int x=q[h++]; for(int j=st[x];j<st[x+1];j++){int y=adj[j]; if(dist[y]<0){dist[y]=dist[x]+1; q[t++]=y;}}}
        for(int i=0;i<n;i++) if(i>s && (dist[i]<0 || dist[i]>5)) bad++;
    }
    printf("n=%d edges=%d maxdeg=%d bad_pairs(dist>5 or unreachable)=%ld\n", n, m, maxd, bad);
    return 0;
}
