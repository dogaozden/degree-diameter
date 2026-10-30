# Usage: gap -q -c 'ORDER:=60; OUTDIR:="groups";' src/gap_tables.g     (optional: IDS:=[1,5];)
# Writes OUTDIR/sg_<ORDER>_<i>.txt for every SmallGroup(ORDER, i): first line m, then m rows of the
# multiplication table (row g, column h: index of g*h), element 0 = identity. Also OUTDIR/sg_<ORDER>_<i>.name.
if not IsBound(IDS) then IDS := [1..NrSmallGroups(ORDER)]; fi;
for i in IDS do
  G := SmallGroup(ORDER, i);
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  fn := Concatenation(OUTDIR, "/sg_", String(ORDER), "_", String(i), ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(ORDER), "\n");
  for g in el do
    AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n");
  od;
  CloseStream(out);
  PrintTo(Concatenation(OUTDIR, "/sg_", String(ORDER), "_", String(i), ".name"),
          StructureDescription(G), " abelian=", IsAbelian(G), " nilpotent=", IsNilpotent(G), "\n");
od;
QUIT;
