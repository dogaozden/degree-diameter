# usage: gap -q -c 'ORDER:=294; OUTDIR:="subs";' subs.g   (optional IDS:=[1,2];)
# For each SmallGroup(ORDER,i): writes OUTDIR/sub6_<ORDER>_<i>.txt: first line = number of subgroups of order 6,
# then one line per subgroup: TYPE (C6 or S3) followed by its 6 element indices (same indexing as c18/groups tables:
# index 0 = identity, index of g*h = table entry).
if not IsBound(IDS) then IDS := [1..NrSmallGroups(ORDER)]; fi;
for i in IDS do
  G := SmallGroup(ORDER, i);
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  subs := Filtered(AllSubgroups(G), H -> Size(H) = 6);
  fn := Concatenation(OUTDIR, "/sub6_", String(ORDER), "_", String(i), ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, Length(subs), "\n");
  for H in subs do
    if IsCyclic(H) then AppendTo(out, "C6"); else AppendTo(out, "S3"); fi;
    for x in Elements(H) do AppendTo(out, " ", Position(el, x) - 1); od;
    AppendTo(out, "\n");
  od;
  CloseStream(out);
od;
QUIT;
