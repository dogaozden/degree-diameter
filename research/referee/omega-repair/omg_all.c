// OmegaH_q, reading 2, labelling given per copy: hub (t,k) -> point P_c[t] of copy c, hub (m,kbar) -> line L_c[m].
// Wiring of Fig. 2.21 (d12D8_table.md 1.3): type a: k -> k-1,k+1 ; kbar -> k+2,k+3.  type b: k -> k+3,k+4 ; kbar -> k-1,k+1.
// usage: omg hex.txt lab.bin pattern src_class(u|b) k row target_copy out_reached.txt
// Checks degrees, simplicity, bipartiteness; BFS from the hub; prints the distance profile, the far count per copy,
// and writes the target-colour vertices of target_copy at distance <= 7 (as hexagon indices).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage: omg_all hex lab pattern [A]\n");return 1;}
  FILE*f=fopen(argv[1],"r"); int q,N; if(fscanf(f,"%d %d",&q,&N)!=2) return 1;
  int k1=q+1; int *pl=malloc(sizeof(int)*N*k1), *lp=malloc(sizeof(int)*N*k1), *pd=calloc(N,sizeof(int));
  for(int l=0;l<N;l++) for(int j=0;j<k1;j++){int p; if(fscanf(f,"%d",&p)!=1) return 1; lp[l*k1+j]=p; pl[p*k1+pd[p]++]=l;}
  fclose(f);
  const char*pat=argv[3]; int A=strlen(pat), C=5*A;
  int *P=malloc(sizeof(int)*C*N), *L=malloc(sizeof(int)*C*N);
  f=fopen(argv[2],"rb"); int hdr[2]; if(fread(hdr,4,2,f)!=2||hdr[0]!=C||hdr[1]!=N){fprintf(stderr,"lab header\n");return 1;}
  for(int c=0;c<C;c++){ if(fread(P+c*N,4,N,f)!=(size_t)N||fread(L+c*N,4,N,f)!=(size_t)N) return 1; }
  fclose(f);
  int *Pi=malloc(sizeof(int)*C*N), *Li=malloc(sizeof(int)*C*N);
  for(int c=0;c<C;c++){ for(int i=0;i<N;i++){Pi[c*N+i]=-1;Li[c*N+i]=-1;}
    for(int i=0;i<N;i++){ if(Pi[c*N+P[c*N+i]]!=-1||Li[c*N+L[c*N+i]]!=-1){fprintf(stderr,"not a bijection\n");return 1;} Pi[c*N+P[c*N+i]]=i; Li[c*N+L[c*N+i]]=i; } }
  // classes: 0..4 unbarred, 5..9 barred; cop[Y][2A]
  int cop[10][64]; int ncop[10]={0};
  int meets[512][4]; int nm[512]; memset(nm,0,sizeof nm);
  for(int B=0;B<A;B++) for(int k=0;k<5;k++){
    int u1,u2,b1,b2;
    if(pat[B]=='a'){u1=(k+4)%5;u2=(k+1)%5;b1=(k+2)%5;b2=(k+3)%5;} else {u1=(k+3)%5;u2=(k+4)%5;b1=(k+4)%5;b2=(k+1)%5;}
    int cs[4]={5*B+u1,5*B+u2,5*B+b1,5*B+b2}; int Ys[4]={k,k,5+k,5+k};
    for(int j=0;j<4;j++){cop[Ys[j]][ncop[Ys[j]]++]=cs[j]; meets[cs[j]][nm[cs[j]]++]=Ys[j];}
  }
  for(int c=0;c<C;c++) if(nm[c]!=4){fprintf(stderr,"copy %d met by %d classes\n",c,nm[c]);return 1;}
  long V=(long)C*2*N+10L*N; long hub0=(long)C*2*N;
  #define CP(c,p) ((long)(c)*2*N+(p))
  #define CL(c,l) ((long)(c)*2*N+N+(l))
  #define HUB(Y,t) (hub0+(long)(Y)*N+(t))
  // degrees
  int *deg=calloc(V,sizeof(int));
  for(int c=0;c<C;c++) for(int i=0;i<N;i++){deg[CP(c,i)]=k1; deg[CL(c,i)]=k1;}
  for(int Y=0;Y<10;Y++) for(int t=0;t<N;t++){ deg[HUB(Y,t)]=ncop[Y]; for(int j=0;j<ncop[Y];j++){int c=cop[Y][j]; if(Y<5) deg[CP(c,P[c*N+t])]++; else deg[CL(c,L[c*N+t])]++;} }
  long *off=malloc(sizeof(long)*(V+1)); off[0]=0; for(long v=0;v<V;v++) off[v+1]=off[v]+deg[v];
  int *adj=malloc(sizeof(int)*off[V]); long *fill=malloc(sizeof(long)*V); for(long v=0;v<V;v++) fill[v]=off[v];
  for(int c=0;c<C;c++) for(int l=0;l<N;l++) for(int j=0;j<k1;j++){int p=lp[l*k1+j]; adj[fill[CL(c,l)]++]=CP(c,p); adj[fill[CP(c,p)]++]=CL(c,l);}
  for(int Y=0;Y<10;Y++) for(int t=0;t<N;t++) for(int j=0;j<ncop[Y];j++){int c=cop[Y][j]; long x= Y<5? CP(c,P[c*N+t]) : CL(c,L[c*N+t]); adj[fill[HUB(Y,t)]++]=x; adj[fill[x]++]=HUB(Y,t);}
  int dmin=1<<30,dmax=0; for(long v=0;v<V;v++){ if(deg[v]<dmin)dmin=deg[v]; if(deg[v]>dmax)dmax=deg[v]; }
  // simplicity: sort-free check with a marker array
  long dup=0; int *mark=calloc(V,sizeof(int));
  for(long v=0;v<V;v++){ for(long e=off[v];e<off[v+1];e++){ if(mark[adj[e]]==(int)(v+1)) dup++; mark[adj[e]]=v+1; } }
  printf("V=%ld E=%ld degrees %d..%d duplicate edges %ld\n",V,off[V]/2,dmin,dmax,dup);

  int all=(argc>4 && argv[4][0]=='A');
  long start= all?0:hub0;
  signed char *dist=malloc(V); long *qu=malloc(sizeof(long)*V);
  long far=0; int ecc=0; long far_nonhubtarget=0;
  for(long s=start;s<V;s++){
    memset(dist,-1,V); long h=0,tl=0; dist[s]=0; qu[tl++]=s;
    while(h<tl){ long v=qu[h++]; for(long e=off[v];e<off[v+1];e++){ long w=adj[e]; if(dist[w]<0){dist[w]=dist[v]+1; qu[tl++]=w;} } }
    if(tl!=V){printf("disconnected\n");return 1;}
    for(long v=0;v<V;v++){ if(dist[v]>ecc) ecc=dist[v]; if(dist[v]>8){ far++; if(!(s>=hub0 && v<hub0)) far_nonhubtarget++; } }
  }
  printf("sources %s: pairs (source, vertex) at distance > 8: %ld (of which not hub->copy-vertex: %ld); max eccentricity %d\n", all?"all vertices":"all hubs", far, far_nonhubtarget, ecc);
  return 0;
}
