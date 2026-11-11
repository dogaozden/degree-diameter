# Export a group for hx: right-multiplication permutations of a generating set and Aut(G) generators given by
# the images of that generating set.  Call ExportGroup(G, filename).
ExportGroup := function(G, fn)
  local L, n, gens, out, g, perm, A, ag, phi, imgs, pos, x;
  L := ShallowCopy(AsSSortedList(G)); n := Length(L);
  pos := Position(L, One(G)); L[pos] := L[1]; L[1] := One(G);
  gens := MinimalGeneratingSet(G);
  out := OutputTextFile(fn, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, n, " ", Length(gens), "\n");
  for g in gens do
    perm := List(L, x -> Position(L, x * g) - 1);
    AppendTo(out, JoinStringsWithSeparator(List(perm, String), " "), "\n");
  od;
  A := AutomorphismGroup(G); ag := GeneratorsOfGroup(A);
  AppendTo(out, Length(ag), "\n");
  for phi in ag do
    imgs := List(gens, g -> Position(L, Image(phi, g)) - 1);
    AppendTo(out, JoinStringsWithSeparator(List(imgs, String), " "), "\n");
  od;
  CloseStream(out);
end;
