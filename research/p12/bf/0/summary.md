# SHARD 0 — brute-force check of |LBM(3,8)|

Status: in progress (chunks RES 0–7 of MOD 32 running in parallel under scripts/guarded.sh 5).
Per-chunk table (graphs generated, LBM hits, runtime) will be filled in at completion.

Validation: `genbg -q -c 7 7 -d3:3 -D3:3 | labelg -q | sort -u | lbm 3 6` → 5 LBM graphs (matches paper).
