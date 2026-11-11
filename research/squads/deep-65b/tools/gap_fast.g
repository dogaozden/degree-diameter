# Fast table export (binary search instead of Position). Usage (inside the output folder's parent):
#   gapw -c 'ORDER:=192; IDS:=[1,2,3]; OUTDIR:="tabs";' tools/gap_fast.g      (optional AUT:=true adds "ngen k" + Aut generators)
# Writes OUTDIR/sg_<ORDER>_<i>.tab (m, table with identity 0, ["ngen k", gens]) and .name (structure, abelian flag).
if not IsBound(AUT) then AUT := false; fi;
for i in IDS do
  G := SmallGroup(ORDER, i);
  srt := AsSSortedList(G);
  e := PositionSorted(srt, One(G));
  # index: identity -> 0, others in sorted order
  idx := function(x) local p; p := PositionSorted(srt, x); if p = e then return 0; elif p < e then return p; else return p - 1; fi; end;
  el := Concatenation([srt[e]], srt{Difference([1..Size(G)], [e])});
  fn := Concatenation(OUTDIR, "/sg_", String(ORDER), "_", String(i), ".tab");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(ORDER), "\n");
  for g in el do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(idx(g*h))), " "), "\n"); od;
  if AUT then
    A := AutomorphismGroup(G); gens0 := GeneratorsOfGroup(A);
    AppendTo(out, "ngen ", String(Length(gens0)), "\n");
    for a in gens0 do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(idx(Image(a, h)))), " "), "\n"); od;
  fi;
  CloseStream(out);
  PrintTo(Concatenation(OUTDIR, "/sg_", String(ORDER), "_", String(i), ".name"), StructureDescription(G), " abelian=", IsAbelian(G), "\n");
od;
QUIT;
