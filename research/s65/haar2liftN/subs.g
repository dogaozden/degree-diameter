# subgroups of index IDX of SmallGroup(360,53) as element-index lists in haarex2.g's element order
K := SmallGroup(360,53);; elms := AsSSortedList(K);; e := One(K);; elms := Concatenation([e], Filtered(elms, x -> x <> e));;
for idx in [3, 4, 8] do
  cls := Filtered(ConjugacyClassesSubgroups(K), c -> Index(K, Representative(c)) = idx);
  for k in [1..Length(cls)] do
    N := Representative(cls[k]);
    PrintTo(Concatenation("N_", String(idx), "_", String(k), ".txt"), JoinStringsWithSeparator(List(AsList(N), x -> String(Position(elms, x) - 1)), " "), "\n");
    Print(idx, " ", k, " ", StructureDescription(N), "\n");
  od;
od;
QUIT;
