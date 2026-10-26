for N in Concatenation([14..45],[64..80],[85..106]) do
  out := OutputTextFile(Concatenation("/home/user/degree-diameter/research/squads/own-small/r1/e2/groups/t", String(N), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  for id in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    T := MultiplicationTable(el);
    ab := "0";; if IsAbelian(G) then ab := "1";; fi;;
    WriteAll(out, Concatenation("G ", String(N), " ", String(id), " ", ab, "\n"));
    for a in [1..N] do
      WriteAll(out, Concatenation(JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n"));
    od;
  od;
  CloseStream(out);
od;
QUIT;
