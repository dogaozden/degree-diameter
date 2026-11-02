ExportNoAut := function(G, fn)
  local L, n, gens, out, g, perm, pos, x;
  L := ShallowCopy(AsSSortedList(G)); n := Length(L);
  pos := Position(L, One(G)); L[pos] := L[1]; L[1] := One(G);
  gens := SmallGeneratingSet(G);
  out := OutputTextFile(fn, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, n, " ", Length(gens), "\n");
  for g in gens do
    perm := List(L, x -> Position(L, x * g) - 1);
    AppendTo(out, JoinStringsWithSeparator(List(perm, String), " "), "\n");
  od;
  AppendTo(out, "0\n");
  CloseStream(out);
end;
