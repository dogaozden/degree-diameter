/* Symmetric voltage lifts of 3+3 circulant bases (rotation sigma: a_i->a_{i+1}, b_i->b_{i+1}).
   Base: a_i ~ b_{i+j} with multiplicity m_j (j=0,1,2), sum m_j = 6.
   Free voltages: one per (j,k), k<m_j; voltage on edge (a_i, b_{i+j}, k) is alpha^i(g_{j,k}).
   Lift vertices A(i,g)=i*n+g, B(t,g)=3n+t*n+g; edges A(i,x) ~ B(i+j, v*x).
   Right multiplication is an automorphism and (sigma,alpha) is one too, so BFS from A(0,e) and B(0,e)
   gives the exact diameter. cost = number of vertices not within distance 5 of the two sources.
   usage: sym3 GROUPFILE m0 m1 m2 SECONDS SEED OUTPREFIX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int n, idx, *mt, *inv_, *alph;
static int apow[3][512];
static int mj[3], pj[6];
static int V;
static int *adj, *deg, *dist, *q;
static int curpar[6];

static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }

static void build(const int *par){
  int p,i,g,j,t,v;
  memset(deg,0,sizeof(int)*V);
  for(p=0;p<6;p++){
    j=pj[p];
    for(i=0;i<3;i++){
      v=apow[i][par[p]]; t=(i+j)%3;
      for(g=0;g<n;g++){
        int u=i*n+g, w=3*n+t*n+mt[v*n+g];
        adj[u*6+deg[u]++]=w; adj[w*6+deg[w]++]=u;
      }
    }
  }
}

static int bfs(int src){
  int head=0,tail=0,reached=0,k;
  static int stamp=0; /* use dist as visited via generation */
  stamp++;
  /* dist stores generation*16+depth for visited */
  dist[src]=stamp*16+0; q[tail++]=src; reached=1;
  while(head<tail){
    int u=q[head++]; int du=dist[u]-stamp*16;
    if(du>=5) continue;
    for(k=0;k<6;k++){
      int w=adj[u*6+k];
      if(dist[w]<stamp*16){ dist[w]=stamp*16+du+1; q[tail++]=w; reached++; }
    }
  }
  return V-reached;
}

static int evalp(const int *par){
  int p,q2,pen=0;
  for(p=0;p<6;p++) for(q2=0;q2<p;q2++) if(pj[p]==pj[q2] && par[p]==par[q2]) pen++;
  if(pen) return 100000*pen;
  build(par);
  for(p=0;p<V;p++) ; /* nothing */
  return bfs(idx) + bfs(3*n+idx);
}

static void write_edges(const char *fn, const int *par){
  FILE *f=fopen(fn,"w"); int u,k;
  build(par);
  fprintf(f,"%d\n",V);
  for(u=0;u<V;u++) for(k=0;k<6;k++) if(adj[u*6+k]>u) fprintf(f,"%d %d\n",u,adj[u*6+k]);
  fclose(f);
}

int main(int argc,char**argv){
  if(argc<8){fprintf(stderr,"usage: sym3 GROUPFILE m0 m1 m2 SECONDS SEED OUTPREFIX\n");return 1;}
  FILE *f=fopen(argv[1],"r"); int i,j,k,t,x;
  if(!f){fprintf(stderr,"no file\n");return 1;}
  fscanf(f,"%d %d",&n,&idx);
  mt=malloc(sizeof(int)*n*n); inv_=malloc(sizeof(int)*n); alph=malloc(sizeof(int)*n);
  for(i=0;i<n*n;i++) fscanf(f,"%d",&mt[i]);
  for(i=0;i<n;i++) fscanf(f,"%d",&alph[i]);
  fclose(f);
  for(i=0;i<n;i++) for(j=0;j<n;j++) if(mt[i*n+j]==idx) inv_[i]=j;
  for(i=0;i<n;i++){ apow[0][i]=i; apow[1][i]=alph[i]; apow[2][i]=alph[alph[i]]; }
  mj[0]=atoi(argv[2]); mj[1]=atoi(argv[3]); mj[2]=atoi(argv[4]);
  double secs=atof(argv[5]); rs ^= (unsigned long long)atoll(argv[6])*2654435761ULL+12345; for(i=0;i<10;i++) rnd();
  const char *outp=argv[7];
  k=0; for(j=0;j<3;j++) for(x=0;x<mj[j];x++) pj[k++]=j;
  if(k!=6){fprintf(stderr,"need sum m = 6\n");return 1;}
  V=6*n;
  adj=malloc(sizeof(int)*V*6); deg=malloc(sizeof(int)*V); dist=calloc(V,sizeof(int)); q=malloc(sizeof(int)*V);
  int best=1<<30, bestpar[6]; int bestAll[6];
  clock_t t0=clock(); long iters=0; int restarts=0;
  while((double)(clock()-t0)/CLOCKS_PER_SEC < secs){
    int par[6], cur, p, c, pr;
    restarts++;
    for(p=0;p<6;p++) par[p]=rnd()%n;
    cur=evalp(par);
    long L=20000; double T0=3.0, T1=0.05;
    for(long s=0;s<L;s++){
      double T=T0*pow(T1/T0,(double)s/L);
      p=rnd()%6; pr=par[p]; par[p]=rnd()%n;
      c=evalp(par); iters++;
      if(c<=cur || urand()<exp(-(c-cur)/T)){ cur=c; if(cur<best){best=cur; memcpy(bestpar,par,sizeof par);} if(best==0) break; }
      else par[p]=pr;
      if(best==0) break;
    }
    if(best==0) break;
  }
  printf("RESULT group=%s m=%s%s%s best=%d restarts=%d iters=%ld pars=",argv[1],argv[2],argv[3],argv[4],best,restarts,iters);
  for(i=0;i<6;i++) printf("%d ",bestpar[i]);
  printf("\n");
  {
    char fn[512];
    sprintf(fn,"%s_m%s%s%s_c%d.edges",outp,argv[2],argv[3],argv[4],best);
    if(best<=2){ write_edges(fn,bestpar); }
  }
  return 0;
}
