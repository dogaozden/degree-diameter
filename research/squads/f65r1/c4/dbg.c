#define main main_orig
#include "sym3.c"
#undef main
int main(int argc,char**argv){
  /* usage: dbg GROUP p0..p5 : prints distance histogram from A(0,id) and B(0,id) */
  FILE *f=fopen(argv[1],"r"); int i; fscanf(f,"%d %d",&n,&idx);
  mt=malloc(sizeof(int)*n*n); inv_=malloc(sizeof(int)*n); alph=malloc(sizeof(int)*n);
  for(i=0;i<n*n;i++) fscanf(f,"%d",&mt[i]); for(i=0;i<n;i++) fscanf(f,"%d",&alph[i]); fclose(f);
  for(i=0;i<n;i++){ apow[0][i]=i; apow[1][i]=alph[i]; apow[2][i]=alph[alph[i]]; }
  mj[0]=2;mj[1]=2;mj[2]=2; int k=0,j,x; for(j=0;j<3;j++) for(x=0;x<mj[j];x++) pj[k++]=j;
  V=6*n; adj=malloc(sizeof(int)*V*6); deg=malloc(sizeof(int)*V); dist=calloc(V,sizeof(int)); q=malloc(sizeof(int)*V);
  int par[6]; for(i=0;i<6;i++) par[i]=atoi(argv[2+i]);
  build(par);
  printf("n=%d V=%d\n",n,V);
  int dd[20]={0}; int u;
  /* BFS from 0 manually */
  int *dl=malloc(sizeof(int)*V); for(u=0;u<V;u++) dl[u]=-1;
  int *qq=malloc(sizeof(int)*V); int h=0,t=0; dl[0]=0; qq[t++]=0;
  while(h<t){int a=qq[h++]; for(k=0;k<6;k++){int w=adj[a*6+k]; if(dl[w]<0){dl[w]=dl[a]+1; qq[t++]=w;}}}
  for(u=0;u<V;u++) dd[dl[u]<0?19:dl[u]]++;
  for(i=0;i<20;i++) if(dd[i]) printf("d=%d: %d\n",i,dd[i]);
  printf("bfs cost A=%d B=%d\n", bfs(idx), bfs(3*n+idx));
  return 0;
}
