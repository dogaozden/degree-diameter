# Cloud brief: diameter-5 fine ladder (autopilot, overnight)

Repo tools (research/d5): groups.py (tables, `--check`), haar_search3.c (compile: `cc -O2 -o haar_search3 haar_search3.c -lm`),
build_haar3.py, h4_plan.py (candidate lists by family), run_h4.sh. Read research/d5/REPORT.md rounds 3–4 first.

Current bests (group order must EXCEED): Δ5 177, Δ6 342, Δ7 576, Δ8 882, Δ9 1331, Δ10 2000.
Goal: groups with orders just above each threshold (up to +8%), all families in groups.py (sl, psl, pgl, gl, heis, agl,
affine, meta, z2 semidirect, and direct products with cyclic groups), non-abelian only, skip duplicates (h4_plan.py has a
fingerprint dedupe). Your half: SHARD (given in your prompt) — take every second candidate in order of (Δ, order).

Rules: run `scripts/stop_check.sh` before each batch; run the batch under `scripts/guarded.sh 5 ...`; use all cores of
this machine; each job 20–30 min, K=20, seeds 1–2. On cost 0: build the graph with build_haar3.py and check it with
`python3 scripts/verify_record.py <json> Δ 5`; commit the solution file and graph JSON. Push to branch `d5-fine-SHARD`
every hour (solutions, a summary file research/d5/fine_SHARD.md with best cost per job).
