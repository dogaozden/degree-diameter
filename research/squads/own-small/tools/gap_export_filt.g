# Like gap_export_aut.g, but only groups with |G/G'| <= B (quotient bound); every group gets a line in dir/sum<N>.txt:
# "N id |G/G'| exported(0/1)". Usage: echo 'lo:=401;; hi:=500;; B:=75;; dir:="groups";; Read("gap_export_filt.g");' | gap -q -o 8g
for N in [lo..hi] do
  out := OutputTextFile(Concatenation(dir, "/t", String(N), ".txt"), false);
  sm := OutputTextFile(Concatenation(dir, "/sum", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false); SetPrintFormattingStatus(sm, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    q := Product(AbelianInvariants(G));
    if q <= B then
      el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
      T := MultiplicationTable(el);
      orbs := Orbits(AutomorphismGroup(G), el);
      reps := List(orbs, o -> Minimum(List(o, x -> Position(el, x))) - 1);
      Sort(reps);
      WriteAll(out, Concatenation("G ", String(N), " ", String(id), " ", String(Length(reps)), "\n"));
      WriteAll(out, Concatenation(JoinStringsWithSeparator(List(reps, String), " "), "\n"));
      for a in [1..N] do
        WriteAll(out, Concatenation(JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n"));
      od;
      WriteAll(sm, Concatenation(String(N), " ", String(id), " ", String(q), " 1\n"));
    else
      WriteAll(sm, Concatenation(String(N), " ", String(id), " ", String(q), " 0\n"));
    fi;
  od;
  CloseStream(out); CloseStream(sm);
od;
QUIT;
