// OmegaH_q, reading 2, labelling given per copy: hub (t,k) -> point P_c[t] of copy c, hub (m,kbar) -> line L_c[m].
// Wiring of Fig. 2.21 (d12D8_table.md 1.3): type a: k -> k-1,k+1 ; kbar -> k+2,k+3.  type b: k -> k+3,k+4 ; kbar -> k-1,k+1.
// usage: omg hex.txt lab.bin pattern src_class(u|b) k row target_copy out_reached.txt
// Checks degrees, simplicity, bipartiteness; BFS from the hub; prints the distance profile, the far count per copy,
// and writes the target-colour vertices of target_copy at distance <= 7 (as hexagon indices).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){
  if(argc<9){fprintf(stderr,"usage\n");return 1;}
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
  // BFS
  int Ysrc = (argv[4][0]=='u'?0:5)+atoi(argv[5]); int row=atoi(argv[6]); int cp=atoi(argv[7]);
  long s=HUB(Ysrc,row);
  signed char *dist=malloc(V); memset(dist,-1,V); long *qu=malloc(sizeof(long)*V); long h=0,tl=0; dist[s]=0; qu[tl++]=s;
  long bip=0;
  while(h<tl){ long v=qu[h++]; for(long e=off[v];e<off[v+1];e++){ long w=adj[e]; if(dist[w]<0){dist[w]=dist[v]+1; qu[tl++]=w;} else if(((dist[w]^dist[v])&1)==0) bip++; } }
  long hist[64]={0}; long unr=0; for(long v=0;v<V;v++){ if(dist[v]<0) unr++; else hist[dist[v]]++; }
  printf("source hub class %s%d row %d (vertex %ld); non-bipartite edges seen %ld; unreachable %ld\n",Ysrc<5?"":"bar ",Ysrc%5,row,s,bip,unr);
  printf("distance profile:"); int ecc=0; for(int d=0;d<64;d++) if(hist[d]){printf(" %d:%ld",d,hist[d]); ecc=d;} printf("\neccentricity %d\n",ecc);
  printf("far (>=9) vertices per copy:"); long tot=0;
  for(int c=0;c<C;c++){ long n=0; for(int i=0;i<2*N;i++){ long v=(long)c*2*N+i; if(dist[v]<0||dist[v]>=9) n++; } tot+=n; printf(" %ld",n);} 
  long nh=0; for(long v=hub0;v<V;v++) if(dist[v]<0||dist[v]>=9) nh++;
  printf("\ntotal far copy vertices %ld, far hubs %ld\n",tot,nh);
  // target colour in target copy: points if source unbarred, lines if barred
  FILE*o=fopen(argv[8],"w"); long nr=0,nfar=0;
  for(int i=0;i<N;i++){ long v= Ysrc<5? CP(cp,i):CL(cp,i); if(dist[v]>=0 && dist[v]<=7){fprintf(o,"%d\n",i); nr++;} else nfar++; }
  fclose(o);
  printf("target copy %d, %s: reached within 7: %ld, at distance >= 9: %ld\n",cp,Ysrc<5?"points":"lines",nr,nfar);
  return 0;
}
