G := SmallGroup(360, 53);
el := Elements(G); e := Position(el, One(G));
el2 := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
pos := x -> Position(el2, x) - 1;
cl := ConjugacyClassesSubgroups(G);
out := OutputTextFile("subs360.txt", false);
SetPrintFormattingStatus(out, false);
for c in cl do
  H := Representative(c);
  if Size(H) in [180, 120, 90, 72, 60, 36, 30, 40, 45] then
    AppendTo(out, Size(H), " ", Index(G, H), " ", JoinStringsWithSeparator(List(AsList(H), x -> String(pos(x))), ","), "\n");
  fi;
od;
CloseStream(out);
Print("classes: ", Length(cl), "\n");
