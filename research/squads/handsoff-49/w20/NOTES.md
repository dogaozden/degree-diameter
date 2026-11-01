# w20 NOTES: certificate for metacyclic Haar graphs, order N = 2,486..2,520

Start: 01:23 UTC. Hard stop: 02:55 UTC. Card: cards.md, "## w20". Question: is there any metacyclic G of order
N in 2,486..2,520 (split or non-split) and S, |S| = 4, with H(G,S) of diameter 9 (cost 0, so n = 2N > 4,970)?

## 1. Abelian-quotient bound (D = 9): done, checked by brute force
- Haar graph H(G,S), S = {e,s1,s2,s3}. The A-side vertices within 8 steps of (e,A) are the products of 4 elements of
  D = S^-1 S. Projecting onto an abelian quotient Q = G/G' (a homomorphism of graphs) gives |Q| <= |4D_Q|.
- The largest value is over the free abelian group on s1,s2,s3: |4D| = 309 (bound.py, computed by brute force:
  |D| = 13, reach sizes 13, 55, 147, 309 at 2, 4, 6, 8 steps). So a group with |G/G'| > 309 cannot have cost 0.
- For metacyclic G = <a,b | a^m, b^k = a^s, b a b^-1 = a^r>: G' = <a^d>, d = gcd(r-1,m), so |G/G'| = d*k.
  Exclude every group with d*k > 309.
- Calibration: meta 71 35 49 (the valid 4,970 graph) has d*k = 35 <= 309, so it is not excluded.

## 2. Candidate list (enum2.py -> cand_sorted.tsv, reorder.py -> cand_ordered.tsv)
- Parameters: m | N, k = N/m, r a unit with r^k = 1 mod m, one r per cyclic subgroup <r>; s with s(r-1) = 0 mod m.
  s classes under s -> u*s (u unit) and s -> s + sigma (sigma = sum_{j<k} r^j): the shift is b -> b a^i, the unit
  is a -> a^u. Split groups are the class of s = 0.
- Result: 901 candidate classes (509 split, 392 non-split) survive the bound out of all metacyclic groups in range.
  Excluded by the bound: every (m,k,r,s) with d*k > 309.
- Coverage by earlier work: w11 certified.tsv already has exact rows for 26 of them (covered_by_w11 in certificate.tsv).

## 3. Exhaustive pass (exh3 = w11's orbit-marking search, copied here; run20.sh)
- exh3 with LIMIT 1: it records only sets of cost <= 1. "IMPROVED" = cost 0 (a record); "WROTE cost=1" = min 1;
  no line = no set of cost 0 or 1 exists. Certificate row "no_cost0 yes, min_seen >=2" means the group has no cost-0 set.
- Split groups use the exact automorphisms of exh3 (meta mode). Non-split groups use tab mode (inner automorphisms
  only), which is much slower (100-170 s per group so far).
- Speed: about 50-160 s per group on one core. The 901 candidates would take about 25 hours; this worker can finish
  only the first few dozen. The rest are a clear list for the coordinator: rows of cand_ordered.tsv not in certificate.tsv.
- Order: w2 screen cost first (low cost = most dangerous), then dk.

## 4. Results so far (02:46)
- certificate.tsv: 62 candidate groups certified, no cost-0 set in any of them: 39 by my exhaustive pass
  (DONE, no_cost0 = yes), 23 already exact in w11's certified.tsv (covered_by_w11). Hits (cost 0): none.
- Calibration: exh4 (exh3 + explicit automorphism list) reproduces cost 0 on meta 71 35 49 (the valid 4,970 graph,
  same 1,560,685 evaluations as w11) and min 4 on 104 24 7.
- Non-split groups now use the full Aut(G) list (aut_gen.py, capped at 3,000 automorphisms; any subset is a valid
  symmetry reduction). About 15-80 s per group instead of 100-250 s.
- Remaining: about 840 of the 901 candidate classes are not certified yet (rows of cand_run.tsv not in certificate.tsv).
  The next one is found by the first row of cand_run.tsv that has no certificate.tsv row.

## 4b. Notes on the tools
- run21.sh LIST BUDGET: resumable driver (split = exh3 meta, non-split = exh4 with aut_gen lists). Call it as
  `timeout 100 nice -n 10 ./run21.sh cand_run.tsv 60`. A group is saved after every rep (state/), so a cut-off call
  loses at most one rep.
- Earlier w20 runs of non-split groups (before the aut lists) are valid DONE rows; their state files were moved to
  state/old_*.

## 5. What I would try next
- Give the remaining rows of cand_run.tsv to other workers (any split of the list works; the state files are per tag).
- Full Aut(G) with no cap for the big-Aut non-split groups (|Aut| up to 80,000), generated in chunks.
- The bound may be sharpened by checking, for each abelian quotient Q = G/G' (order dk), whether some 4-set of Q covers Q;
  this excludes large dk groups that the bare count 309 does not.
