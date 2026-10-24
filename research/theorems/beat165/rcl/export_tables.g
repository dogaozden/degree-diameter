# For each group of order n with an index-2 subgroup: write "n id k" then the multiplication table (n*n bytes as
# numbers 0..n-1, row-major, x*y), then k lines each with the 0/1 membership vector of an index-2 subgroup.
ExportOrder := function(n, file)
  local out, i, G, el, tab, subs, S, row, cnt, homs;
  out := OutputTextFile(file, false); SetPrintFormattingStatus(out, false);
  cnt := 0;
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    # index-2 subgroups = kernels of the nontrivial homomorphisms to C2
    subs := Filtered(MaximalNormalSubgroups(G), N -> Index(G, N) = 2);
    if Length(subs) = 0 then continue; fi;
    if not IsSolvable(G) or true then fi;
    el := AsSSortedList(G);
    tab := MultiplicationTable(el);
    AppendTo(out, n, " ", i, " ", Length(subs), "\n");
    for row in tab do AppendTo(out, JoinStringsWithSeparator(List(row, x -> String(x-1)), " "), "\n"); od;
    for S in subs do AppendTo(out, JoinStringsWithSeparator(List(el, x -> String(Number([x], y -> y in S))), " "), "\n"); od;
    cnt := cnt + 1;
  od;
  CloseStream(out);
  return cnt;
end;
n := Int(Filtered(GAPInfo.SystemCommandLine, x -> Length(x) > 2 and x{[1..2]} = "-N")[1]{[3..10]});
