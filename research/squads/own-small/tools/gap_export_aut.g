# Export every SmallGroup of order N in [lo..hi] as a multiplication table plus Aut(G)-orbit representatives.
# Usage: echo 'lo:=216;; hi:=216;; dir:="groups";; Read("gap_export_aut.g");' | gap -q -o 4g
# Output dir/t<N>.txt: per group "G N id nAutReps", then the reps (element indices, identity = 0), then N table rows.
for N in [lo..hi] do
  out := OutputTextFile(Concatenation(dir, "/t", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    T := MultiplicationTable(el);
    A := AutomorphismGroup(G);
    orbs := Orbits(A, el);
    reps := List(orbs, o -> Minimum(List(o, x -> Position(el, x))) - 1);
    Sort(reps);
    WriteAll(out, Concatenation("G ", String(N), " ", String(id), " ", String(Length(reps)), "\n"));
    WriteAll(out, Concatenation(JoinStringsWithSeparator(List(reps, String), " "), "\n"));
    for a in [1..N] do
      WriteAll(out, Concatenation(JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n"));
    od;
  od;
  CloseStream(out);
od;
QUIT;
