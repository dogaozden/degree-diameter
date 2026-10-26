# Export every SmallGroup of order N (lo..hi) as a multiplication table.
# Usage: echo 'lo:=43;; hi:=63;; Read("gap_export.g");' | gap -q
# Output: groups/g<N>.txt, one block per group:
#   G <N> <id> <name>
#   N lines of N integers: row a, column b = index of el[a]*el[b]; index 0 is the identity.
for N in [lo..hi] do
  out := OutputTextFile(Concatenation("groups/g", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    T := MultiplicationTable(el);
    nm := ReplacedString(StructureDescription(G), " ", "");
    AppendTo(out, "G ", N, " ", id, " ", nm, "\n");
    for a in [1..N] do
      AppendTo(out, JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n");
    od;
  od;
  CloseStream(out);
od;
QUIT;
