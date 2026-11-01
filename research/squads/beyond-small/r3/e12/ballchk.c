#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define H 16896
static int adjA[H][16], adjB[H][16];
int main(int argc,char**argv){ FILE*f=fopen(argv[1],"r"); long n,u,v; fscanf(f,"%ld",&n); int da[H]={0},db[H]={0};
 while(fscanf(f,"%ld %ld",&u,&v)==2){ if(u>v){long t=u;u=v;v=t;} v-=H; adjA[u][da[u]++]=v; adjB[v][db[v]++]=u; }
 int ok=1; for(int i=0;i<H;i++) if(da[i]!=16||db[i]!=16) ok=0; printf("regular %d\n",ok);
 /* coverage of B-vertices within distance 3 of the 16 A-vertices in line file argv[2] line argv[3] */
 FILE*g=fopen(argv[2],"r"); char buf[512]; int L=atoi(argv[3]); for(int i=0;i<L;i++) fgets(buf,512,g); fgets(buf,512,g);
 int N[16],m=0,x,off; char*q=buf; while(sscanf(q,"%d%n",&x,&off)==1&&m<16){q+=off;N[m++]=x;}
 static char covB[H], d2A[H]; memset(covB,0,H); memset(d2A,0,H);
 int dist1B[H]; memset(dist1B,0,sizeof dist1B);
 for(int k=0;k<m;k++){ int a=N[k]; for(int i=0;i<16;i++){ int b=adjA[a][i]; covB[b]=1; for(int j=0;j<16;j++){ d2A[adjB[b][j]]=1; } } }
 /* distance 3 B-vertices: via A-vertices at distance 2 (d2A) */
 for(int a=0;a<H;a++) if(d2A[a]) for(int i=0;i<16;i++) covB[adjA[a][i]]=1;
 int cnt=0; for(int b=0;b<H;b++) if(!covB[b]) cnt++; printf("uncovered B (python-equivalent) %d\n",cnt);
 return 0; }
