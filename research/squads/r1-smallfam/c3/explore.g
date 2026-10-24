show := function(q, lo, hi)
  local G, sub, k, H, irr;
  G := GL(2,q);
  sub := Filtered(List(ConjugacyClassesSubgroups(G), Representative), H -> Size(H) >= lo and Size(H) <= hi);
  for k in [1..Length(sub)] do
    H := sub[k];
    irr := MTX.IsIrreducible(GModuleByMats(GeneratorsOfGroup(H), GF(q)));
    Print("GL(2,", q, ") k=", k, " |H|=", Size(H), " irr=", irr, " ", StructureDescription(H), "\n");
  od;
end;
show(5, 44, 56);
show(7, 23, 28);
show(8, 39, 51);
QUIT;
