#define main main_orig
#include "sym3.c"
#undef main
int main(){
  FILE *f=fopen("groups/G120_5_id.txt","r"); int i,j,k;
  fscanf(f,"%d %d",&n,&idx); mt=malloc(sizeof(int)*n*n); alph=malloc(sizeof(int)*n);
  for(i=0;i<n*n;i++) fscanf(f,"%d",&mt[i]); for(i=0;i<n;i++) fscanf(f,"%d",&alph[i]);
  printf("row0: "); for(j=0;j<10;j++) printf("%d ",mt[j]); printf("\n");
  printf("row1: "); for(j=0;j<10;j++) printf("%d ",mt[n+j]); printf("\n");
  printf("alpha: "); for(j=0;j<10;j++) printf("%d ",alph[j]); printf("\n");
  /* check associativity sample and that identity row = identity */
  int bad=0; for(i=0;i<n;i++) for(j=0;j<n;j++) if(mt[idx*n+j]!=j) bad++; printf("id bad=%d\n",bad);
  return 0;
}
