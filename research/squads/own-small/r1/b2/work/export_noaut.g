# export all groups (no Aut reps) for orders in lst, text format used by split_groups.py (empty reps line)
lst := Concatenation([13..63],[65..71]);;
dir := "/home/user/degree-diameter/research/squads/own-small/r1/b2/groups";;
for N in lst do
  out := OutputTextFile(Concatenation(dir, "/t", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    T := MultiplicationTable(el);
    WriteAll(out, Concatenation("G ", String(N), " ", String(id), " 0\n"));
    WriteAll(out, "\n");
    for a in [1..N] do
      WriteAll(out, Concatenation(JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n"));
    od;
  od;
  CloseStream(out);
od;
QUIT;
