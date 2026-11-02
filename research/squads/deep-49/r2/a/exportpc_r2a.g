# Export with Aut(G) computed through a pc copy of G (AutomorphismGroup of the perm group fails for this group).
ExportGroupPc := function(G, fn)
  local L, n, gens, out, g, perm, iota, ginv, pc, Apc, ag, phi, psi, imgs, pos;
  L := ShallowCopy(AsSSortedList(G)); n := Length(L);
  pos := Position(L, One(G)); L[pos] := L[1]; L[1] := One(G);
  gens := SmallGeneratingSet(G);
  out := OutputTextFile(fn, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, n, " ", Length(gens), "\n");
  for g in gens do
    perm := List(L, x -> Position(L, x * g) - 1);
    AppendTo(out, JoinStringsWithSeparator(List(perm, String), " "), "\n");
  od;
  iota := IsomorphismPcGroup(G); ginv := InverseGeneralMapping(iota); pc := Range(iota);
  Apc := AutomorphismGroup(pc); ag := GeneratorsOfGroup(Apc);
  AppendTo(out, Length(ag), "\n");
  for phi in ag do
    psi := CompositionMapping(ginv, phi, iota);
    imgs := List(gens, g -> Position(L, Image(psi, g)) - 1);
    AppendTo(out, JoinStringsWithSeparator(List(imgs, String), " "), "\n");
  od;
  CloseStream(out);
end;
