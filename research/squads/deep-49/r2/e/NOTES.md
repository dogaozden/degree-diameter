# r2e: split metacyclic certificate for orders 2,531..2,600 without SmallGroups data

Result: all 245 candidate groups certified exhaustively with no Haar set of cost 0 (MIN >0 each). No cost-0 set found.
Scoreboard: 245 lines with "card": "r2e" appended to research/squads/deep-49/r2/scoreboard.jsonl (score ">0", exact, valid).

Orders (GAP SmallGroupsAvailable false, 24 of them): 2532, 2535, 2536, 2538, 2540, 2541, 2544, 2548, 2550, 2552, 2556,
2560, 2562, 2565, 2568, 2574, 2576, 2580, 2583, 2584, 2590, 2592, 2596, 2600. Orders 2541, 2550, 2556, 2568, 2576, 2583,
2590, 2596 have no kept candidate (no split metacyclic group with d >= 3 and |G/G'| <= 309).
Groups per order (kept): 2532:5, 2535:4, 2536:2, 2538:4, 2540:1, 2544:12, 2548:5, 2552:6, 2560:62, 2562:20, 2565:14,
2574:22, 2580:21, 2584:9, 2592:32, 2600:26 (total 245; candidates before the |G/G'| filter: 316).

Files:
- avail.g: GAP list of orders with/without SmallGroups data (run: gap -q --quitonbreak avail.g < /dev/null).
- mkcand.py: enumerates split metacyclic Z_m x|_r Z_k (r ~ r^t, gcd(t,k)=1 dedup; d = ord(r mod m) >= 3; q = k*gcd(r-1,m) <= 309),
  writes candidates.json (sorted by d descending, then N).
- driver.py: copy of r1/c2/driver.py with paths repointed to r2/e and card "r2e". Resumable, BUDGET seconds per call
  (default 85). Builds each group by GAP (presentation a^m, b^k, b a b^-1 a^-r, Size check, ExportGroup with full Aut,
  build_tab.py), falls back to mkmeta.py when GAP times out or fails (10 groups: 5 GAP timeouts, 4 earlier timeouts
  without a recorded reason, 1 coset-enumeration overflow; listed in state.json as build "mkmeta"). The fallback only
  reduces by the automorphisms that mkmeta.py gives (still exact). Automorphism generators verified; hx LIMIT 0 in resumable
  chunks; any HIT0 is verified with haar_edges.py + apsp 4 9 (VALID) and apsp 4 8 (INVALID). None occurred.
- state.json: per group status, x-orbit count K, next rep, MIN text. All 245 done with next = K+1 (exhaustive), hits 0.
- hx, hx.c, mkmeta.py: copies of r1/c2 (hx.c identical to tools/hx.c).
- runs/: per-group .g, .exp, .aut, .hx.out/.err, .hits. The .tab tables (12 MB each, 3 GB total) were deleted after the run;
  rebuild with `python3 mkmeta.py m k r key` or the GAP step in driver.py.

Rerun: `cd r2/e && BUDGET=85 timeout 100 nice -n 10 python3 driver.py < /dev/null` until it prints "done 245/245".

Calibration: the same path (mkmeta.py 71 35 49 cal; hx cal.tab cal.aut 0 9 1 999999 cal.hits) finds the record group's
cost-0 sets: MIN 0 with 24 hits in about 10 s (runs/cal.out, runs/cal.err). So the pipeline does detect cost 0.

Caveats: dedup is only r ~ r^t (gcd(t,k)=1) within the same (m,k), so some groups may be isomorphic duplicates across
different (m,k) presentations; that costs time, not correctness. The |G/G'| <= 309 and d >= 3 filters are the card's
(d <= 2 is ruled out by tools/capacity), so the certificate covers exactly the filtered list, not every group of these
orders. Non-split (non-metacyclic) groups of these orders were not checked.
