# Export groups of order N in [lo..hi] with |G/G'| <= B that contain an involution: table + involution class reps.
# Output dir/t<N>.txt blocks "G N id R" / reps line / N table rows; dir/sum<N>.txt "N id |G/G'| exported".
for N in [lo..hi] do
  out := OutputTextFile(Concatenation(dir, "/t", String(N), ".txt"), false);
  sm := OutputTextFile(Concatenation(dir, "/sum", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false); SetPrintFormattingStatus(sm, false);
  if N mod 2 = 0 then
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    q := Product(AbelianInvariants(G));
    if q <= B then
      el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
      T := MultiplicationTable(el);
      cl := Filtered(ConjugacyClasses(G), c -> Order(Representative(c)) = 2);
      reps := List(cl, c -> Position(el, Representative(c)) - 1);
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
  fi;
  CloseStream(out); CloseStream(sm);
od;
QUIT;
