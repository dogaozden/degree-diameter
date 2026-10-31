/* ---- walk-directed repair: pick a missing (root r, target w, element x), enumerate the non-backtracking walks
   r -> w of length <= D, solve for the voltage of one edge on each walk that would make the walk produce x, and
   evaluate a random sample of these candidate moves (full cost). Accept the best sampled move by an SA rule. ---- */
static int rp_e[16], rp_f[16];          /* walk darts */
static uint64_t rp_pre[16];             /* pre[k] = a_{k-1}...a_0 (pre[0] = identity) */
static uint64_t rp_dart[16];            /* dart voltage at step k */
static int rp_target, rp_root;
static uint64_t rp_x;                   /* element being sought */
static int cand_e[200000], cand_g[200000], ncand;
static int rp_maxcand = 200000;
static int idN;                          /* identity index is 0 */

static void rp_walks(int x, int depth, int *lastE, int r_here, uint64_t pre) {
    /* x: current vertex; depth: number of darts taken; pre: product so far */
    if (depth > 0 && x == rp_target) {
        /* walk from root to target with product pre = V; suffix products */
        uint64_t Q = 0;  /* identity index is 0 */
        for (int p = depth - 1; p >= 0; p--) {
            /* Q = Q_p = a_{depth-1} ... a_{p+1}; pre_p = pre[p] */
            uint64_t prep = rp_pre[p];
            /* a_p* = Q^{-1} x prep^{-1} */
            int t = MT[INV[Q]][rp_x];
            int ap = MT[t][INV[prep]];
            int g = rp_f[p] ? ap : INV[ap];
            if (ncand < rp_maxcand) { cand_e[ncand] = rp_e[p]; cand_g[ncand] = g; ncand++; }
            /* Q_{p-1} = Q_p * a_p */
            Q = MT[Q][rp_dart[p]];
        }
    }
    if (depth == 9) return;
    for (int k = 0; k < nin[x]; k++) {
        /* darts out of x: the same incidence list (edge e, forward flag reversed) */
        int e = inE[x][k], fwd = inFwd[x][k];
        if (e == *lastE) continue;     /* non-backtracking: do not reuse the edge just taken */
        int nxtv = fwd ? ev[e] : eu[e];     /* dart from x to the other end */
        int dartf = fwd ? 0 : 1;            /* dart x->nxtv is forward (eu->ev) iff x == eu[e] */
        /* incoming dart at x from nxtv uses voltage: for target x, forward flag fwd means source eu->ev */
        (void)dartf;
        /* outgoing dart from x along e: exists iff x == eu[e] (forward) or x == ev[e] (backward) */
        int fwd_out = (x == eu[e]) ? 1 : 0;
        int a = fwd_out ? volt[e] : INV[volt[e]];
        rp_e[depth] = e; rp_f[depth] = fwd_out; rp_dart[depth] = a;
        rp_pre[depth + 1] = MT[a][pre];
        int savedE = e;
        rp_walks(nxtv, depth + 1, &savedE, r_here, rp_pre[depth + 1]);
    }
}
