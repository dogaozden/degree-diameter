# c10 notes: augmented quotient bases of the 684 Haar graph (round 2)

Idea (card c10): the 684 graph H = H(G,S), G = SmallGroup(342,12) = C6 x (C19:C3), S = {113,16,280,65,59,295}, is a regular
N-cover of its quotient by a normal N (bases from c9's normals342.txt; `quot.py`). Add j new vertex pairs to the base,
rewire 6 base edges (a new pair a (side 0), b (side 1): a takes 6-nab freed side-1 ends, b takes 6-nab freed side-0 ends,
nab parallel a-b edges), and lift by N: n = 684 + 2 j |N|. Every move stays N-equivariant.

## Files
- bases/qL.base, bases/nL.tab: quotient bases for normal subgroup line L of normals342.txt (quot.py, NORM=normals342.txt).
  L2 = C2 (342+342 base, n 688 after augmentation), L3 = C3 (228, 690), L4 = C6 (114, 696), L5 = C19 (36, 722),
  L7 = C19:C3 (12, 798), L13 = C57 (12, 798). All six quotient bases lift to the 684 graph (vl EVAL cost 0).
- augment.py IN OUT NAB SEED PAIRS M: the augmentation above (nab = parallel a-b edges; new voltages random in Z_M).
- fam.sh L NAB SEED SECS T0 T1: augment + vl SA (FIXTREE=0), appends to runs/log.tsv.
- evalb.sh SOL TAB: lift a vl solution (lift.py) and print n and far pairs (score65).
- gauge.py: abelian gauge normalisation (tree voltages to 0) for tabu (INIT=sol needs it).
- randvolt.py: random voltages on a base.

## Calibration
- Unaugmented bases: vl cost 0 for all six (the 684 graph). OK.
- Random-start SA on the 36-vertex C19 base (no augmentation): best 266 (SA 60 s, T0=3), 322 (T0=5), 530 (T0=20); tabu
  216 in 60 s. So the 684 structure is NOT found from random starts; the search must start from the quotient solution.
  Tabu (shared/tabu) is slow here: about 1.6 steps/s on 108 edges.
- Bad pairs vs vl cost: bad ~ cost * m / 2 (e.g. C19 cost 364 -> bad 3458; C6 cost 412 -> bad 1236).
