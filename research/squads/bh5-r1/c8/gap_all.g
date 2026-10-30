# Driver: exports all SmallGroups of the orders in ORDERS into OUTDIR (format: "N e" then N rows, row g col h = index of g*h).
for n in ORDERS do
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    el := ShallowCopy(Elements(G));
    Sort(el);
    N := Length(el);
    e := PositionSorted(el, One(G));
    fn := Concatenation(OUTDIR, "/s_", String(n), "_", String(i), ".txt");
    out := OutputTextFile(fn, false);
    SetPrintFormattingStatus(out, false);
    AppendTo(out, String(N), " ", String(e-1), "\n");
    for g in el do
      AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(PositionSorted(el, g*h) - 1)), " "), "\n");
    od;
    CloseStream(out);
    PrintTo(Concatenation(OUTDIR, "/s_", String(n), "_", String(i), ".name"), StructureDescription(G), "\n");
  od;
od;
QUIT;
