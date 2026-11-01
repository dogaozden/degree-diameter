/* exh TAB.bin ORBFILE CAP MODE [args]
 * Exhaustive minimum of the Haar cost over S = {e,a,b,c} (a = one rep per Aut-orbit on G\{e} from ORBFILE, b<c all).
 * Cost (haar_tab convention, zero iff valid):  |G \ T^{<=4}| + |G \ T'^{<=4}|,  T = S^-1 S, T' = S S^-1.
 * MODE "check" : compares the fast cost with a BFS on the Haar graph for random S (argv[5] samples).
 * MODE "run"   : searches; argv[5] = first orbit index, argv[6] = last orbit index (exclusive).  Prints histogram of
 *                costs < CAP and writes every S with cost <= argv[7] to stdout as "COST a b c". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N; static uint16_t *T; static int *inv;
static uint32_t *mk1,*mk2,*mk3; static uint32_t st1=0,st2=0,st3=0; /* mk1 unused */
static int tl[32]; static int ntl;
static int X2[400], n2; static int X3list[2600]; 
/* uncovered count of G \ (T^{<=4}) for the T-set in tl[0..ntl-1] (tl contains 0 and is inverse-closed), capped at cap */
static int side_cost(int cap){
  st2++; st3++;
  /* X2 = T^{<=2}: T itself (contains e) and products */
  n2=0;
  for(int i=0;i<ntl;i++){ int x=tl[i]; for(int j=0;j<ntl;j++){ int y=T[(size_t)x*N+tl[j]]; if(mk2[y]!=st2){ mk2[y]=st2; X2[n2++]=y; } } }
  /* X3 = X2 . T  (T^{<=3}; e in T so it contains T^{<=2}) */
  int n3=0;
  for(int i=0;i<n2;i++){ int x=X2[i]; for(int j=0;j<ntl;j++){ int y=T[(size_t)x*N+tl[j]]; if(mk3[y]!=st3){ mk3[y]=st3; X3list[n3++]=y; } } }
  /* uncovered of X3 . T : g covered iff some t in T with g*t in X3 (T inverse-closed) */
  int unc=0;
  for(int g=0;g<N;g++){
    int cov=0;
    for(int j=0;j<ntl;j++){ if(mk3[T[(size_t)g*N+tl[j]]]==st3){ cov=1; break; } }
    if(!cov){ if(++unc>=cap) return cap; }
  }
  return unc;
}
/* Set T = S^-1 S for S = {0,a,b,c} (or T' = S S^-1 when prime=1); returns ntl */
static void build_T(const int *S, int prime){
  static uint32_t *mkd=NULL; static uint32_t dst=0; if(!mkd){ mkd=calloc(N,4); }
  ntl=0; dst++;
  for(int i=0;i<4;i++) for(int j=0;j<4;j++){
    int y = prime ? T[(size_t)S[i]*N+inv[S[j]]] : T[(size_t)inv[S[i]]*N+S[j]];
    if(mkd[y]!=dst){ mkd[y]=dst; tl[ntl++]=y; }
  }
}
static int cost_S(const int *S, int cap){
  build_T(S,0); int c1=side_cost(cap); if(c1>=cap) return cap;
  build_T(S,1); int c2=side_cost(cap-c1); return c1+c2;
}
/* BFS reference: Haar graph vertices (g,A)=g, (g,B)=N+g, edges (g,A)~(s g,B) */
static int cost_bfs(const int *S){
  int V=2*N; int *dA=malloc(V*sizeof(int)), *dB=malloc(V*sizeof(int)); int *q=malloc(V*sizeof(int));
  int cost=0;
  for(int side=0;side<2;side++){
    int *d = side? dB: dA; for(int v=0;v<V;v++) d[v]=-1;
    int src = side? N+0 : 0; int head=0,tail=0; q[tail++]=src; d[src]=0;
    while(head<tail){ int v=q[head++];
      if(v<N){ for(int i=0;i<4;i++){ int u=N+T[(size_t)S[i]*N+v]; if(d[u]<0){ d[u]=d[v]+1; q[tail++]=u; } } }
      else { int g=v-N; for(int i=0;i<4;i++){ int u=T[(size_t)inv[S[i]]*N+g]; if(d[u]<0){ d[u]=d[v]+1; q[tail++]=u; } } }
    }
    for(int v=0;v<V;v++){ /* same-side vertices at distance > 8 */
      if(side==0 && v<N && (d[v]<0 || d[v]>8)) cost++;
      if(side==1 && v>=N && (d[v]<0 || d[v]>8)) cost++;
    }
  }
  free(dA); free(dB); free(q); return cost;
}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb"); int32_t n32; if(fread(&n32,4,1,f)!=1) return 1; N=n32;
  T=malloc((size_t)N*N*2); if(fread(T,2,(size_t)N*N,f)!=(size_t)N*N) return 1; fclose(f);
  inv=malloc(N*sizeof(int)); for(int g=0;g<N;g++) for(int h=0;h<N;h++) if(T[(size_t)g*N+h]==0){ inv[g]=h; break; }
  mk1=calloc(N,4); mk2=calloc(N,4); mk3=calloc(N,4);
  int cap = atoi(argv[3]);
  char *mode=argv[4];
  if(!strcmp(mode,"check")){
    int ns=atoi(argv[5]); srand(12345); int bad=0; int hist[64]={0};
    for(int it=0;it<ns;it++){
      int S[4]={0,0,0,0}; for(int i=1;i<4;i++) S[i]=1+rand()%(N-1);
      if(S[1]==S[2]||S[1]==S[3]||S[2]==S[3]) { it--; continue; }
      int c1=cost_S(S,1<<20), c2=cost_bfs(S);
      if(c1!=c2){ bad++; if(bad<5) printf("mismatch S=%d %d %d %d fast=%d bfs=%d\n",S[0],S[1],S[2],S[3],c1,c2); }
      if(c2<64) hist[c2]++;
    }
    printf("check: samples %d mismatches %d\n", ns, bad);
    for(int i=0;i<12;i++) printf("cost %d: %d\n", i, hist[i]);
    return 0;
  }
  /* run */
  int lo=atoi(argv[5]), hi=atoi(argv[6]), keep=atoi(argv[7]);
  FILE*o=fopen(argv[2],"r"); int *reps=malloc(64*sizeof(int)); int nr=0; int r,sz; while(fscanf(o,"%d %d",&r,&sz)==2) reps[nr++]=r; fclose(o);
  long hist[64]={0}; (void)0;
  for(int ri=lo; ri<hi && ri<nr; ri++){
    int a=reps[ri]; long cnt=0;
    for(int b=1;b<N;b++){ if(b==a) continue;
      for(int c=b+1;c<N;c++){ if(c==a) continue;
        int S[4]={0,a,b,c};
        int cost=cost_S(S,cap);
        hist[cost<cap?cost:cap]++; cnt++;
        if(cost<=keep) printf("COST %d %d %d %d %d\n", cost, a,b,c, ri);
      }
    }
    fprintf(stderr,"rep %d a=%d done (%ld sets)\n", ri, a, cnt);
    fflush(stdout);
  }
  printf("HIST");
  for(int i=0;i<=cap;i++) printf(" %d:%ld", i, hist[i]);
  printf("\n");
  return 0;
}
