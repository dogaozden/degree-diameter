# For every SmallGroup(ORDER, i) (IDS optional), export dc2 files for all pairs of classes of subgroups of order
# H_ORDER, as OUTDIR/sg<ORDER>_<i>_<a>_<b>.dc2.  Skips groups with no such subgroup.
if not IsBound(IDS) then IDS := [1..NrSmallGroups(ORDER)]; fi;
Read("/home/user/degree-diameter/research/squads/bh5-r3/c2/dc2_lib_fixed.g");
for id in IDS do
  G := SmallGroup(ORDER, id);
  if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
  ExportPairs(G, H_ORDER, Concatenation(OUTDIR, "/sg", String(ORDER), "_", String(id)));
od;
QUIT;
