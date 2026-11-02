#define main main_orig
#include "haar_sl8d.c"
#undef main
int main(void){
    P=37; U=10; MODE=0; D=4; M2=2*P; init_gf(); init_sl(); N=NSL*M2; NV=2*N; EID=IDSL*M2;
    dist=malloc(NV); qu=malloc(NV*sizeof(int32_t));
    /* group check: associativity on random triples and inverse */
    for(int t=0;t<100000;t++){ int a=rand()%N,b=rand()%N,c=rand()%N;
        if(mulG(mulG(a,b),c)!=mulG(a,mulG(b,c))){printf("assoc fail\n");return 1;}
        if(mulG(a,invG(a))!=EID){printf("inv fail %d\n",a);return 1;} }
    printf("group ok\n");
    int g=77; int a1=alphaG(g), a2=alphaG(a1);
    int Sg[4]={EID,g,a1,a2}; setS(Sg,4);
    printf("g=%d a1=%d a2=%d EID=%d\n",g,a1,a2,EID);
    printf("reached cost A %d\n", bfs(EID));
    /* count reached by depth */
    /* compute closure size of <S^-1 S> in C by BFS on group */
    int cnt=0; for(int v=0;v<NV;v++) if(dist[v]!=255) cnt++;
    printf("visited after bfs(A): %d\n",cnt);
    return 0;
}
