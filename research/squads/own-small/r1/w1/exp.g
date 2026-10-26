for line in SplitString(StringFile("sel.txt"), "\n") do
  if Length(line) > 0 then
    f := SplitString(line, " ");
    N := Int(f[1]); id := Int(f[2]);
    G := SmallGroup(N, id);
    el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
    T := MultiplicationTable(el);
    out := OutputTextFile(Concatenation("groups/t", String(N), "_", String(id), ".txt"), false);
    SetPrintFormattingStatus(out, false);
    AppendTo(out, N, "\n");
    for a in [1..N] do
      AppendTo(out, JoinStringsWithSeparator(List(T[a], x -> String(x - 1)), " "), "\n");
    od;
    CloseStream(out);
  fi;
od;
QUIT;
