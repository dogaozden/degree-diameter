# Orbit representatives of Aut(G) on the elements of each SmallGroup(N, id), in the element order of gap_export.g.
# Usage: echo 'lo:=29;; hi:=42;; Read("gap_aut.g");' | gap -q   ->  groups/a<N>.txt, lines "A N id rep rep ..."
for N in [lo..hi] do
  out := OutputTextFile(Concatenation("groups/a", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    A := AutomorphismGroup(G);
    orbs := Orbits(A, el);
    reps := List(orbs, o -> Minimum(List(o, x -> Position(el, x))) - 1);
    Sort(reps);
    AppendTo(out, "A ", N, " ", id, " ", JoinStringsWithSeparator(List(reps, String), " "), "\n");
  od;
  CloseStream(out);
od;
QUIT;
