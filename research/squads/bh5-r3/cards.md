# bh5-r3 cards (read COMMON.md first)

c1 (7,5) h=3 sweep: `./sweep.sh ORDER 3 7` for ORDER = 1731, 1734, ..., 1845 (multiples of 3; N = 2|G|/3 = 1154..1230).
   Do the orders with few groups first, skip orders with > 300 groups. Report the best cost per order and overall.
c2 (5,5) h=3 and h=4 sweeps: `./sweep.sh ORDER 3 5` for ORDER = 534, 537, 540, 543, 549, 552, 555, 558 (546 done),
   then `./sweep.sh ORDER 4 5` for ORDER = 712, 716, 724, 728, 732, 736, 740, 744 and, if time is left, 720
   (840 groups: only the non-solvable ones, e.g. IDS from Filtered([1..840], i -> not IsSolvable(SmallGroup(720,i)))).
c3 (7,5) constructed groups (orders above 2000 are not in SmallGroups): pick groups G and h in {4, 5, 6, 8} with
   N = 2|G|/h in 1154..1400 and run `./run_group.sh NAME "GAP expr" h 7` on each. Start with
   DirectProduct(AlternatingGroup(5), AlternatingGroup(5)) h=6 (N 1200), DirectProduct(PGL(2,7), CyclicGroup(7))
   h=4 (1176), DirectProduct(AlternatingGroup(5), DihedralGroup(40)) h=4 (1200), DirectProduct(SymmetricGroup(5),
   DihedralGroup(20)) h=4 (1200), DirectProduct(PSL(2,11), CyclicGroup(4)) and (PSL(2,11) x V4) h=4 (1320),
   DirectProduct(SL(2,5), CyclicGroup(20)) h=4 (1200), DirectProduct(PSL(2,7), DihedralGroup(14)) h=4 (1176),
   then any others you find (almost simple groups and their direct products with small groups). Use
   DirectProduct(...) with permutation groups (e.g. AlternatingGroup, SymmetricGroup, PSL, PGL, DihedralGroup as
   permutation groups: DihedralGroup(IsPermGroup, 40)).
