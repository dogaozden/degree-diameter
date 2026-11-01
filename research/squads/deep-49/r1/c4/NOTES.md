# c4: constrained exact searches at the cost-2 / cost-4 walls

## Files
- `hx.c` (copy of tools/hx.c) with two options added (exact for D = 9):
  - `HX_MUST=g1,g2,...` (env): each listed element must lie in (SS^-1)^4 and (S^-1S)^4 before the cost is computed.
    The run aborts unless every automorphism generator fixes each must element (then the Aut reduction stays exact;
    a central element is fixed by the central-character automorphisms used here).
  - `HX_MUSTSIDE=A|B|AB` (env, default AB): restrict the must condition to side A ((SS^-1)^4) and/or side B ((S^-1S)^4).
  Binary: `hxm` (`gcc -O3 -march=native -o hxm hx.c`).
- `g104.tab/.aut` (Z_104 x|_7 Z_24), `g208.tab/.aut` (Z_208 x|_3 Z_12), `g101.tab/.aut` (Z_101 x|_5 Z_25): `python3 ../../tools/mkmeta.py m k r gXXX`.
- `check_sets.py TABLE SETS [MUST] [N]`: independent python recomputation of cost and must-coverage of sets `x y z` (S = {0,x,y,z}).
- `analyse101.py` (+ `cost2_101_25_5_analysis.txt`): all cost-2 sets of Z_101 x|_5 Z_25, missed (a,j), fibres.
- `structure.py TABLE HITS M K Z`: where the misses sit relative to a central involution z.
- `invcheck.py TABLE HITS`: checks inverse-closure of the miss sets.
- Hit files: `hits104_unc4.txt`, `hits104_z52_L8.txt`, `hits104_z52A_L8.txt`, `hits104_z52B_L8.txt`, `hits208_unc4.txt`,
  `hits208_z104_L12a/b.txt`, `hits208_z104A_L12a/b/c.txt`, `hits208_z104B_L12a/b/c.txt`, `hits101_L2.txt`.

## Results (all exact; witnesses re-checked by check_sets.py)
- Unconstrained calibration: 104 24 7 gives MIN 4 (184 sets); 208 12 3 gives MIN 4 (96 sets).
- (i) 104 24 7, z = 52 required on both sides: MIN 8 (none <= 8 missed; run `HX_MUST=52 ./hxm g104.tab g104.aut 8 9 1 61`).
  One-sided: z covered on side A only -> MIN 8; on side B only -> MIN 8.
- (ii) 208 12 3, z = 104 required on both sides: MIN 12 (`... 8 9 1 51` gives MIN >8; `... 12 9 1 25` and `26 51` give MIN 12).
  One-sided: side A -> MIN 12 (chunks 1..17, 18..34, 35..51); side B -> MIN 12 (same chunks).
- (iii) 101 25 5: `./hxm g101.tab g101.aut 2 9 1 99999 hits101_L2.txt` gives 48 cost-2 representatives (MIN 2).
  Each misses exactly one inverse pair {(a,j),(a',-j)} on ONE side (24 on A, 24 on B). Missed fibres are only j in {6,19} or
  {9,16} (= +-6, +-9 mod 25). The kernel j = 0 is never missed. The j-parts of S use the e-in-S normalisation
  (x always (0,j) with j in {3,4,5,7,8,10,12,13,15,17,18,20,21,22}); the missed fibres are invariant, the raw S-j-values are not.
- Structure of the walls (independent recomputation):
  - 104 24 7: in all 184 cost-4 sets z = 52 is missed on BOTH sides. The other two misses form an inverse pair on one side,
    in fibres j = 6, 18 (= +-6); kernel never.
  - 208 12 3: in all 96 cost-4 sets z = 104 is missed on BOTH sides; the other two misses form an inverse pair on one side, fibres j = +-2, +-4.

## Lemmas used in the reading
- X = SS^-1 is inverse-closed, so (SS^-1)^4 and (S^-1S)^4 are inverse-closed. Hence each miss set is closed under g -> g^-1.
  So a miss set has size = (number of involutions it contains) mod 2, and the misses are inverse pairs plus involutions.
- Z_101 x|_5 Z_25 has odd order, so it has no involutions and every side-miss set has even size: every cost is even, which is why its minimum is 2 and not 1.
- In these runs the one-sided constrained minimum equals the two-sided one (8 and 8 for 104; 12 and 12 for 208): forcing
  the central involution onto one side already pays the full wall.

## How to rerun
    cd research/squads/deep-49/r1/c4
    HX_MUST=52 ./hxm g104.tab g104.aut 8 9 1 61 out.txt       # about 25 s CPU, split with XFROM XTO if the machine is loaded
    HX_MUST=104 ./hxm g208.tab g208.aut 12 9 1 25 out.txt
    ./hxm g101.tab g101.aut 2 9 1 99999 hits101_L2.txt && python3 analyse101.py
