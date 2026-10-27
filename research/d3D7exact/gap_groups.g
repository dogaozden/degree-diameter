# Export every SmallGroup of the orders in `ords` with multiplication table and Aut(G)-orbit representatives.
# Usage: echo 'ords:=[8,9,10];; Read("gap_groups.g");' | gap -q   ->  groups/g<N>.txt, blocks:
#   G <N> <id> <name>
#   N rows of N integers (row a, column b = index of el[a]*el[b]; index 0 is the identity)
#   A <number of reps> <rep> <rep> ...   (Aut(G)-orbit representatives on elements, smallest index in each orbit)
for N in ords do
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
    A := AutomorphismGroup(G);
    reps := List(Orbits(A, el), o -> Minimum(List(o, x -> Position(el, x))) - 1);
    Sort(reps);
    AppendTo(out, "A ", Length(reps), " ", JoinStringsWithSeparator(List(reps, String), " "), "\n");
  od;
  CloseStream(out);
od;
QUIT;
