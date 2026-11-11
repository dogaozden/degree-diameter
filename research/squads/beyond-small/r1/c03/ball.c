/* For every B-vertex b (ids 16896..33791) compute the set of A-vertices at distance <=3 from b
   (bipartite: that is distance 1 or 3), as a 16896-bit bitset. Output: ball3.bin (16896 x 264 uint64). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NV 33792
#define HALF 16896
#define DEG 16
#define W 264
static int adj[NV][DEG];
int main(void){
  FILE *f = fopen("/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges","r");
  if(!f){perror("open");return 1;}
  int n; if(fscanf(f,"%d",&n)!=1) return 1;
  int deg[NV]; memset(deg,0,sizeof deg);
  for(long e=0;e<(long)NV*DEG/2;e++){
    int u,v; if(fscanf(f,"%d %d",&u,&v)!=2){fprintf(stderr,"short\n");return 1;}
    if(deg[u]>=DEG||deg[v]>=DEG){fprintf(stderr,"deg overflow\n");return 1;}
    adj[u][deg[u]++]=v; adj[v][deg[v]++]=u;
  }
  fclose(f);
  for(int v=0;v<NV;v++) if(deg[v]!=DEG){fprintf(stderr,"not regular at %d\n",v);return 1;}
  uint64_t *out = calloc((size_t)HALF*W, sizeof(uint64_t));
  static int mark[NV]; int stamp=0;
  for(int b=HALF;b<NV;b++){
    stamp++;
    mark[b]=stamp;
    int l1[DEG], n1=0, l2[DEG*DEG], n2=0;
    for(int i=0;i<DEG;i++){ int a=adj[b][i]; mark[a]=stamp; l1[n1++]=a; }
    for(int i=0;i<n1;i++) for(int j=0;j<DEG;j++){ int bb=adj[l1[i]][j]; if(mark[bb]!=stamp){ mark[bb]=stamp; l2[n2++]=bb; } }
    uint64_t *row = out + (size_t)(b-HALF)*W;
    for(int i=0;i<n1;i++) row[l1[i]/64] |= 1ULL<<(l1[i]%64);
    for(int i=0;i<n2;i++) for(int j=0;j<DEG;j++){ int a=adj[l2[i]][j]; row[a/64] |= 1ULL<<(a%64); }
  }
  FILE *o = fopen("/home/user/degree-diameter/research/squads/beyond-small/r1/c03/ball3.bin","wb");
  fwrite(out,sizeof(uint64_t),(size_t)HALF*W,o); fclose(o);
  /* sizes */
  long tot=0; int mn=1<<30, mx=0;
  for(int k=0;k<HALF;k++){ int c=0; for(int w=0;w<W;w++) c+=__builtin_popcountll(out[(size_t)k*W+w]); tot+=c; if(c<mn)mn=c; if(c>mx)mx=c; }
  printf("ball3 sizes: min %d max %d avg %.1f\n", mn, mx, (double)tot/HALF);
  return 0;
}
