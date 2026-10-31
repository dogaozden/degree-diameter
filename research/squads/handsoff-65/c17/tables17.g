# Usage: gap -q -c 'ORDER:=522; OUTDIR:="groups17"; IDS:=[1,2];' tables17.g
# Same output as shared/gap_tables.g (first line m, then m rows of the multiplication table, identity = element 0),
# but positions are looked up in an enumerator (faster for larger orders).
if not IsBound(IDS) then IDS := [1..NrSmallGroups(ORDER)]; fi;
for i in IDS do
  G := SmallGroup(ORDER, i);
  e := Enumerator(G);
  m := Size(G);
  id := Position(e, One(G));
  el := Concatenation([e[id]], e{Difference([1..m], [id])});
  fn := Concatenation(OUTDIR, "/sg_", String(ORDER), "_", String(i), ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(ORDER), "\n");
  for g in el do
    AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(e, g*h) - 1)), " "), "\n");
  od;
  CloseStream(out);
  PrintTo(Concatenation(OUTDIR, "/sg_", String(ORDER), "_", String(i), ".name"),
          StructureDescription(G), " abelian=", IsAbelian(G), "\n");
od;
QUIT;
