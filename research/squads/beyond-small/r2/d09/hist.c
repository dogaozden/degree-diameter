#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#define H 16896
#define W 264
static int adjA[H][16], adjB[H][16];
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); long n,u,v; fscanf(f,"%ld",&n); static int da[H],db[H];
  while(fscanf(f,"%ld %ld",&u,&v)==2){ if(u>v){long t=u;u=v;v=t;} v-=H; adjA[u][da[u]++]=v; adjB[v][db[v]++]=u; }
  /* ball sizes for B-vertices (side 0 hubs): S=A within distance 3 */
  static int hist[20000]; int *bs=malloc(4*H);
  for(int t=0;t<H;t++){ static uint8_t mark[H]; memset(mark,0,H); int c=0;
    int d2[256]; int nd=0; static uint8_t m2[H]; memset(m2,0,H);
    for(int i=0;i<16;i++){ int s=adjB[t][i]; for(int j=0;j<16;j++){ int t2=adjA[s][j]; if(!m2[t2]){m2[t2]=1; d2[nd++]=t2;} } }
    for(int i=0;i<nd;i++){ int t2=d2[i]; for(int k=0;k<16;k++){ int s=adjB[t2][k]; if(!mark[s]){mark[s]=1;c++;} } }
    for(int k=0;k<16;k++){ int s=adjB[t][k]; if(!mark[s]){mark[s]=1;c++;} }
    bs[t]=c; hist[c]++; }
  for(int c=0;c<20000;c++) if(hist[c]) printf("ball %d : %d\n",c,hist[c]);
  return 0; }
