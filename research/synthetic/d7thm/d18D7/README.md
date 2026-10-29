# (18,7): 7,318,644 with the hub graph H(7)+H(7) (D7_THEOREMS.md §5.1)

- Solution: research/frontier/sols/d18D7_hex13_typedwhisk_h7h7_n7318644.sol (inputs: research/p4/d6/hex/hex_q13.bin,
  research/frontier/sols/d16D7_hex13_R792_n4025508.sol, named by sha256 in the solution file).
- Build: `python3 research/synthetic/conics2/typed_build.py build research/p4/d6/hex/hex_q13.bin <sol> d18.edges`
  (typed_build.py is on branch claude/conics-2-diameter-7-ic0oat); edge-list sha256
  c80d9c0e6a569508b2314c3c3cd6c53babce0ecb844017fdf7f86f297426ed1a (make and build give the same file).
- make.log: the builder's checks (segment / dual segment sets, local duality at all 792 points, hub graph
  same-side distances <= 6, degrees 15..18).
- level_compare.txt: the 64,554,086 level edges equal those of the lab's 7,309,092 graph.
- check_hubs.txt: apsp_fast from all 78,432 hubs, RESULT VALID.
- check_level_*.txt: apsp_fast on ranges of level vertices (partial).
The full all-pairs check (all 7,318,644 sources) was not run in this job.
