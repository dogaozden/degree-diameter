# Text tables (gap_export format, name "-") for every group of each order in L with at most MAXG groups.
# Usage: echo 'L:=[219,220];; MAXG:=60;; dir:="out";; Read("gap_export_fast.g");' | gap -q -o 8g
for N in L do
  if NrSmallGroups(N) <= MAXG then
    out := OutputTextFile(Concatenation(dir, "/g", String(N), ".txt"), false);
    SetPrintFormattingStatus(out, false);
    for id in [1..NrSmallGroups(N)] do
      G := SmallGroup(N, id);
      el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
      T := MultiplicationTable(el);
      WriteAll(out, Concatenation("G ", String(N), " ", String(id), " -\n"));
      for a in [1..N] do WriteAll(out, Concatenation(JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n")); od;
    od;
    CloseStream(out);
  fi;
od;
QUIT;
