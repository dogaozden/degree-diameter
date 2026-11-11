/* routes_dump.c: per hub class X and missed copy c', the numbers of radius-4 and radius-2 route centres of twist.c (reading 2)
   and the radius-4 words (a,b) = lam_a lam_b^-1.  usage: routes_dump hex.txt TYPES  */
#define TWIST_NO_MAIN
#include "twist.c"
int main(int argc,char**argv){ load_hex(argv[1]); strcpy(types,argv[2]); A=strlen(types); C=5*A; wiring(); routes();
 for(int X=0;X<10;X++){ for(int cp=0;cp<C;cp++) if(!att[cp][X]){ int r4=0,r2=0,r0=0,id4=0; for(int i=0;i<ncen[X][cp];i++){Cen e=cen[X][cp][i]; if(e.a<0&&e.R>=4) id4=1; if(e.R>=4) r4++; else if(e.R>=2) r2++; else r0++;}
   printf("X=%d c'=%2d: R4 %2d (id:%d) R2 %3d R0 %d |", X, cp, r4, id4, r2, r0);
   for(int i=0;i<ncen[X][cp];i++){Cen e=cen[X][cp][i]; if(e.R>=4) printf(" (%d,%d)",e.a,e.b);} printf("\n"); } } }
