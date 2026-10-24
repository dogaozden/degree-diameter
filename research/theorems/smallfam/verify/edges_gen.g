WriteHaar := function(n, id, idx, path)
  local G, el, N, S, f, i, s;
  G := SmallGroup(n, id);; el := AsSSortedList(G);; N := Length(el);;
  S := List(idx, i -> el[i + 1]);;
  f := OutputTextFile(path, false);; SetPrintFormattingStatus(f, false);;
  AppendTo(f, 2 * N, "\n");;
  for i in [1..N] do for s in S do AppendTo(f, i - 1, " ", N + Position(el, s * el[i]) - 1, "\n");; od; od;
  CloseStream(f);;
end;;
