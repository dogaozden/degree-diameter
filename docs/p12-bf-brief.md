# Cloud brief: brute-force cross-check of |LBM(3,8)| (Problems 1–2 of Araujo-Pardo & López)

Repo: research/p12 (lbm.c = filter, run38.sh = pipeline; read both). A different method (tree completion) found
|LBM(3,8)| = 6951; this run is an independent check by exhaustive generation.

1. Install nauty (`apt-get install -y nauty` or build from source; the tools may be named nauty-genbg / nauty-labelg).
   Compile: `cc -O2 -o research/p12/lbm research/p12/lbm.c`.
2. Validate: `genbg -q -c 7 7 -d3:3 -D3:3 | labelg -q | sort -u | ./lbm 3 6` must report 5 LBM graphs (paper, (3,6)).
3. Your chunks: RES = SHARD*8 … SHARD*8+7 of MOD = 32 (SHARD given in your prompt). Run them in parallel on all cores:
   `genbg -q -c 15 15 -d3:3 -D3:3 RES/32 | labelg -q | ./lbm 3 8 > hits_RES.txt` (keep only the hits; do not store
   the full canonical stream). Also record per chunk the number of graphs genbg produced (genbg prints a count on
   stderr without -q, or count lines with `wc -l` on a tee to /dev/null).
4. Rules: `scripts/stop_check.sh` before starting; run the whole batch under `scripts/guarded.sh 5 ...`.
5. Commit research/p12/bf/SHARD/hits_*.txt and a summary research/p12/bf/SHARD/summary.md (per chunk: graphs
   generated, LBM hits, runtime) and push to branch `p12-bf-SHARD` every hour and at the end.
