/* aut FILE.bin g1 g2 OUTORB : all automorphisms of a 2-generated group given by a table (generators g1, g2).
 * BFS tree from identity by right multiplication; candidate images (x1,x2) with equal orders; phi defined on the tree,
 * consistency checked on all right-multiplication edges, injectivity checked.  Prints |Aut| and orbit reps on G\{e}
 * (orbits by union-find over all automorphisms), writes OUTORB: one rep per line. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N; static uint16_t *T;
static int *par, *pj, *order_bfs; static int gen[2];
static int ordr(int g){ int k=1,x=g; while(x!=0){ x=T[(size_t)x*N+g]; k++; } return k; }
static int *uf;
static int find(int x){ while(uf[x]!=x){ uf[x]=uf[uf[x]]; x=uf[x]; } return x; }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb"); int32_t n32; fread(&n32,4,1,f); N=n32;
  T=malloc((size_t)N*N*2); fread(T,2,(size_t)N*N,f); fclose(f);
  gen[0]=atoi(argv[2]); gen[1]=atoi(argv[3]);
  par=malloc(N*sizeof(int)); pj=malloc(N*sizeof(int)); order_bfs=malloc(N*sizeof(int));
  int *seen=calloc(N,sizeof(int)); int head=0,tail=0; order_bfs[tail++]=0; seen[0]=1; par[0]=-1;
  while(head<tail){ int x=order_bfs[head++]; for(int j=0;j<2;j++){ int y=T[(size_t)x*N+gen[j]]; if(!seen[y]){ seen[y]=1; par[y]=x; pj[y]=j; order_bfs[tail++]=y; } } }
  if(tail!=N){ printf("not generated: %d of %d\n",tail,N); return 1; }
  int *ord=malloc(N*sizeof(int)); for(int g=0;g<N;g++) ord[g]=ordr(g);
  int *phi=malloc(N*sizeof(int)); char *hit=malloc(N);
  uf=malloc(N*sizeof(int)); for(int i=0;i<N;i++) uf[i]=i;
  long naut=0;
  for(int x1=0;x1<N;x1++){ if(ord[x1]!=ord[gen[0]]) continue;
   for(int x2=0;x2<N;x2++){ if(ord[x2]!=ord[gen[1]]) continue;
    int xs[2]={x1,x2};
    phi[0]=0;
    for(int k=1;k<N;k++){ int y=order_bfs[k]; phi[y]=T[(size_t)phi[par[y]]*N+xs[pj[y]]]; }
    int ok=1;
    for(int x=0;x<N && ok;x++) for(int j=0;j<2;j++){ if(phi[T[(size_t)x*N+gen[j]]]!=T[(size_t)phi[x]*N+xs[j]]){ ok=0; break; } }
    if(!ok) continue;
    memset(hit,0,N); int inj=1; for(int x=0;x<N;x++){ if(hit[phi[x]]){ inj=0; break; } hit[phi[x]]=1; }
    if(!inj) continue;
    naut++;
    for(int x=0;x<N;x++){ int a=find(x), b=find(phi[x]); if(a!=b) uf[a]=b; }
  }}
  printf("Aut order %ld\n", naut);
  FILE*o=fopen(argv[4],"w"); int norb=0; int *cnt=calloc(N,sizeof(int));
  for(int x=1;x<N;x++){ cnt[find(x)]++; }
  for(int x=1;x<N;x++) if(find(x)==x){ fprintf(o,"%d %d\n",x,cnt[x]); norb++; }
  fclose(o); printf("orbits on G minus e: %d\n", norb);
  return 0;
}
