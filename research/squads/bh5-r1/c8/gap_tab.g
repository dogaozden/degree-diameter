# Usage: gap -q -c 'ORDER:=356; OUTDIR:="/abs/groups"; IDS:=[1..5];' gap_tab.g
# Writes OUTDIR/s_<ORDER>_<i>.txt : line 1 "N e" (e = index of identity), then N rows; row g col h = index of g*h.
for i in IDS do
  G := SmallGroup(ORDER, i);
  el := ShallowCopy(Elements(G));
  Sort(el);
  N := Length(el);
  e := PositionSorted(el, One(G));
  fn := Concatenation(OUTDIR, "/s_", String(ORDER), "_", String(i), ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(N), " ", String(e-1), "\n");
  for g in el do
    AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(PositionSorted(el, g*h) - 1)), " "), "\n");
  od;
  CloseStream(out);
  PrintTo(Concatenation(OUTDIR, "/s_", String(ORDER), "_", String(i), ".name"),
          StructureDescription(G), "\n");
od;
QUIT;
