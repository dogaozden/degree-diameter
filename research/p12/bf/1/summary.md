# Brute-force LBM(3,8) cross-check, shard 1 (chunks 8-15 of 32)

Status at 2026-10-20 08:45 UTC: all 8 chunks running (4 at a time, one per core), no chunk finished yet.
The first four chunks had each used about 1 h of CPU at this point.

Validation: `genbg -q -c 7 7 -d3:3 -D3:3 | labelg -q | sort -u | ./lbm 3 6` reports 5 LBM graphs (matches the paper).

Pipeline per chunk: `genbg -c 15 15 -d3:3 -D3:3 RES/32 | labelg -q | lbm 3 8`. Only hits are stored.
Per-chunk counts are in `logs/chunk_RES.tsv` (written when the chunk finishes).
