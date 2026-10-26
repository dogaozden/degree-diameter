// Anneal S (|S|=4, e in S WLOG) for Haar graph H(G,S): (0,x)~(1,s x). G given by mul/inv tables.
// cost = #vertices at distance > D from (0,e) plus from (1,e). 0 = diameter <= D (distance-transitive per side).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXN 2520
#define DEG 4
static unsigned short mul[MAXN][MAXN];
static unsigned short inv_[MAXN];
static int N, D;
static unsigned long long rs;
static inline unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
// BFS from side-s source at identity, returns number of vertices with dist > D (incl unreached)
static int bfs_cost(const int *S, int side){
    static int dist[2*MAXN]; static int q[2*MAXN];
    for(int i=0;i<2*N;i++) dist[i]=-1;
    int src = side*N + 0;
    int h=0,t=0; q[t++]=src; dist[src]=0;
    while(h<t){
        int v=q[h++]; int dv=dist[v];
        if(v<N){ // side0 x=v: neighbours (1, s*x)
            for(int k=0;k<DEG;k++){ int w = N + mul[S[k]][v]; if(dist[w]<0){dist[w]=dv+1; q[t++]=w;} }
        } else { int y=v-N;
            for(int k=0;k<DEG;k++){ int w = mul[inv_[S[k]]][y]; if(dist[w]<0){dist[w]=dv+1; q[t++]=w;} }
        }
    }
    int far=0;
    for(int i=0;i<2*N;i++){ if(dist[i]<0 || dist[i]>D) far++; }
    return far;
}
static int cost(const int *S){ return bfs_cost(S,0)+bfs_cost(S,1); }
int main(int argc,char**argv){
    D=atoi(argv[1]); double secs=atof(argv[2]); rs=strtoull(argv[3],0,10)*2654435761ULL+88172645463325252ULL;
    N=2520;
    FILE*f=fopen("mul.bin","rb"); fread(mul,2,(size_t)MAXN*MAXN,f); fclose(f);
    f=fopen("inv.bin","rb"); fread(inv_,2,MAXN,f); fclose(f);
    int S[DEG], best[DEG]; int bestc=1<<30;
    clock_t t0=clock();
    long it=0;
    while(1){
        // random start: e plus 3 distinct random non-identity elements
        S[0]=0;
        for(int k=1;k<DEG;k++){ int ok; do{ S[k]=rnd()%N; ok=1; for(int j=0;j<k;j++) if(S[j]==S[k]) ok=0; }while(!ok); }
        int c=cost(S); double T0=3.0, T1=0.05; long steps=20000;
        for(long st=0; st<steps; st++){
            double T = T0*pow(T1/T0,(double)st/steps);
            int k = 1 + rnd()%(DEG-1);
            int old=S[k]; int nv; int ok;
            do{ nv=rnd()%N; ok=(nv!=0); for(int j=0;j<DEG;j++) if(S[j]==nv) ok=0; }while(!ok);
            S[k]=nv; int c2=cost(S);
            if(c2<=c || exp((c-c2)/T) > (double)(rnd()%1000000)/1e6){ c=c2; }
            else S[k]=old;
            if(c<bestc){ bestc=c; memcpy(best,S,sizeof S); printf("best %d S %d %d %d %d it=%ld t=%.1f\n",bestc,S[0],S[1],S[2],S[3],it,(double)(clock()-t0)/CLOCKS_PER_SEC); fflush(stdout); if(bestc==0) goto done; }
            it++;
        }
        if((double)(clock()-t0)/CLOCKS_PER_SEC > secs) break;
    }
done:
    printf("FINAL cost %d S %d %d %d %d\n",bestc,best[0],best[1],best[2],best[3]);
    return 0;
}
