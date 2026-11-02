#define main main_orig
#include "haar_sl8d.c"
#undef main
int main(void){
    P=37; U=10; MODE=0; M2=2*P; init_gf(); init_sl(); N=NSL*M2; NV=2*N; EID=IDSL*M2;
    dist=malloc(NV); qu=malloc(NV*sizeof(int32_t));
    srand(5);
    for(int t=0;t<12;t++){
        int g=rand()%N; int a1=alphaG(g), a2=alphaG(a1);
        if(a1==g) continue;
        int Sg[4]={EID,g,a1,a2}; setS(Sg,4);
        int c=bfs(EID); int vis=0; for(int v=0;v<NV;v++) if(dist[v]!=255) vis++;
        /* per-depth counts */
        int dep[13]={0}; for(int v=0;v<NV;v++) if(dist[v]!=255) dep[dist[v]]++;
        printf("g=%d (i=%d x=%d) cost=%d visited=%d depths:",g,g/M2,g%M2,c,vis);
        for(int d=0;d<=12;d++) printf(" %d",dep[d]); printf("\n");
    }
    return 0;
}
