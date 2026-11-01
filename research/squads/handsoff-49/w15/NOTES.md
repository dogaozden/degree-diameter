# w15 NOTES: P x| Z_4 with |P| = 625 (order 2,500, n = 5,000)

Start: 2026-10-31 23:53 UTC. Planned end: about 01:55 UTC. Last update: about 01:08 UTC.

## Result (no record; n = 5,000 is not valid at diameter 9 in any run)
- Best: cost 4 (haar_tab, 10 s, 60 s, 120 s x2 with seeds 1, 2, 3 all give 4). Group: u4m_7 = P x|_phi Z_4 with
  P = tabs/u4_1.bin (exponent-5 maximal-class group of order 625, a subgroup of U_4(F_5)), phi = automorphism with
  generator images (589, 157) (phi^2 = id, so the Z_4 acts through Z_2). Invariants: centre 10, |G/G'| = 20, one involution.
  Table: `tabs/u4m_7.bin`. Rebuild: `python3 u4sub.py 4000` (SEED 5, writes tabs/u4_1.bin, the first class),
  then `python3 auto15.py tabs/u4_1.bin 138,583 30000 u4m 40` (writes u4m_1..u4m_8; u4m_7 is the cost-4 one).
  Search: `haar_tab 4 9 60 1 8 OUT tab tabs/u4m_7.bin 1`. Not VALID (cost 4), so no edge list is written.
- Next best: 7 (u4m_1), 8 (u4m_3), 10 (hb_1, mz5_6, hd_221: Heis(5) x Z_5 and M_125 x Z_5 families).

## Families screened (10 s / 60 s haar_tab; floors stable across seeds)
- Abelian P (Z_5^4 with scalar and (3,1) actions, Z_125 x Z_5, Z_25^2, Z_625 x|182 Z_4): 2,300 to 4,700. For Z_5^4
  with the scalar and (3,1) actions G is not 3-generated: random S leaves 2,400 vertices per side unreached (only 3
  nontrivial elements in S, so G must be 3-generated). Abelian P is bad.
- Heis(5) x Z_5 (heisfull.py, all diagonal automorphisms plus auto15 samples; 11 classes): best 10 (hb_1 = hd_221,
  G = (Heis(5) x| Z_4) x Z_5). Others 14 to 155.
- Z_25 x| Z_25 (meta 25 25 6): 13 (10 s), 19 (60 s).
- Z_125 x| Z_5 (meta 125 5 26): 116 and up (3 classes). Z_5^2 x| Z_25 (semi 5 25 1 1 0 1): 25 to 68.
- M_125 x Z_5 (meta 25 5 6 x cyc 5): 10 (mz5_6), 12 (mz5_3), 14, 15, 42, 46.
- Maximal-class P of exponent 5 (u4_1, from random subgroups of U_4(F_5)): 4 (u4m_7), 7 (u4m_1), 8 (u4m_3), 30 to 102 others.
- New exponent-25 P (wr5_1 = random subgroup of order 625 of Z_5 wr Z_5 = Sylow-5 of S_25, centre 5, |G/G'| 25): 22, 44.
- P x| (Z_2 x Z_2) over u4_1 (v4u4 family, commuting involutory automorphisms, only 18 involutory automorphisms found
  in 30,000 samples): 80.

## Structural facts (for the coordinator)
- Every group of order 2,500 has a normal Sylow 5-subgroup P (n_5 divides 4 and is 1 mod 5), so G = P x| Q with
  |Q| = 4. The search covers Q = Z_4 for the nonabelian P listed above (6 of the 10 nonabelian groups of order 625;
  the other 4 are not built), and Q = Z_2 x Z_2 for one P only.
- Groups of order 2,500 have a 3-generated requirement: S has 3 nontrivial elements, so G must be 3-generated.

## Next idea
- Build the remaining nonabelian groups of order 625 (exponent 25 class 2 and class 3 types) as subgroups of Z_5 wr Z_5
  or of U_3(Z/25), run the same automorphism sampler (auto15.py), and screen. The exponent-5 maximal-class group gave
  the best floor (4), so other P with small |G/G'| and an involutory phi are the likely next winners.

## Final checks (01:13 UTC)
- u4m_7 with haar_tab K = 16, 150 s, seed 21: still 4. Floor 4 holds across seeds and run lengths.
- Z_5 wr Z_5 subgroups of order 625 (wr5.py, 2 and 3 generators, about 45,000 samples): only the two classes wr5_1 (new,
  exponent 25) and wr5_2 (exponent 5, equal to u4_1 by invariants). Automorphisms of wr5_1 with phi^4 = id: 22 and 44 floors.
- Disk: tabs/ now keeps only u4m_7.bin, u4_1.bin, hb_1.bin, mz5_6.bin, wr5_1.bin (the rest are rebuildable with the
  commands above and screen.tsv records every result).
- U_3(Z/25) subgroups of order 625 (u3z25.py, 3,000 samples): classes u3z_1 (centre 25, |G/G'| 125, exponent 25),
  u3z_3 (same invariants as M_125 x Z_5 and Z_5^2 x| Z_25), u3z_2 (abelian Z_25^2). Invariants match known groups, so
  these are probably not new. Not screened.
- Finer dedupe (cycle type of phi on P, auto15.py now keys on it too): the same class lists come back for u4_1 (8
  classes, u4f_7 = u4m_7) and Heis(5) x Z_5 (11 classes, hf_k = hb_k). So the automorphism classes sampled are
  complete for these two P, and the cost floors above are the floors of all Z_4 actions on them.
- U_4(Z/25) subgroups of order 625 (u4z25.py, 3,000 samples, sparse generators): three invariant classes, all
  matching known groups (Z_25^2; centre 25 / ab 125 / exponent 25 twice). No new invariant type, so no new P was added.
- Final state (01:26 UTC): best cost 4 (u4m_7), no record. Stopped because every new P class and every Z_4 automorphism
  class from the sampling gave a floor of 4 or more.
