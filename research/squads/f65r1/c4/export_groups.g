dir := "/home/user/degree-diameter/research/squads/f65r1/c4/groups/";
ExportG := function(G, alpha, fn)
  local el, n, i, j, row, id;
  el := AsList(G); n := Length(el);
  id := Position(el, One(G)) - 1;
  PrintTo(fn, n, "\n", id, "\n");
  for i in [1..n] do
    row := List([1..n], j -> Position(el, el[i]*el[j]) - 1);
    AppendTo(fn, JoinStringsWithSeparator(List(row, String), " "), "\n");
  od;
  if alpha = fail then
    row := List([1..n], j -> j - 1);
  else
    row := List([1..n], j -> Position(el, Image(alpha, el[j])) - 1);
  fi;
  AppendTo(fn, JoinStringsWithSeparator(List(row, String), " "), "\n");
end;
for N in [115..130] do
  if N <> 128 then
  for i in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, i);
    base := Concatenation(dir, "G", String(N), "_", String(i));
    ExportG(G, fail, Concatenation(base, "_id.txt"));
    A := AutomorphismGroup(G);
    k := 0;
    for c in ConjugacyClasses(A) do
      r := Representative(c);
      if Order(r) = 3 then
        k := k + 1;
        ExportG(G, r, Concatenation(base, "_a", String(k), ".txt"));
      fi;
    od;
    Print(N, " ", i, " aut3classes=", k, " aut=", Size(A), "\n");
  od; fi;
od;
QUIT;
