#define main main_orig
#include "inv.c"
#undef main
int main(void) {
    n = 150; m = 75; f = 1; init_sigma(); rng_s[0] = 1; rng_s[1] = 2; for (int i=0;i<10;i++) rnd64();
    int tries=0; while(!gen_init()) tries++;
    printf("init tries %d far=%lld\n", tries, far_cost());
    int nv=0, nz=0; long long c0=far_cost();
    for (int it=0; it<2000; it++) { Move M; if (!rand_move(&M)) { nz++; continue; } nv++;
        apply_move(&M,+1); long long c1=far_cost(); apply_move(&M,-1); if (c1!=c0) nz++; }
    printf("valid %d, fails %d, far now %lld\n", nv, nz, far_cost());
    for (int x=0;x<n;x++) if (deg[x]!=3) printf("deg bad %d\n", x);
    return 0;
}
