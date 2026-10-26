# usage: echo 'lo:=58;; hi:=71;; Read("exp.g");' | gap -q
for N in [lo..hi] do
  out := OutputTextFile(Concatenation("groups/t", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  sm := OutputTextFile(Concatenation("groups/p", String(N), ".txt"), false);
  SetPrintFormattingStatus(sm, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    T := MultiplicationTable(el);
    AppendTo(out, "G ", N, " ", id, "\n");
    for a in [1..N] do
      AppendTo(out, JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n");
    od;
    D := DerivedSubgroup(G);
    AppendTo(sm, N, " ", id, " ", StructureDescription(G), " ab=", Size(G/D), " der=", Size(D), " cen=", Size(Centre(G)), " exp=", Exponent(G), " ncc=", NrConjugacyClasses(G), " ", IsAbelian(G), " ngen=", Length(MinimalGeneratingSet(G)), "\n");
  od;
  CloseStream(out); CloseStream(sm);
od;
QUIT;
