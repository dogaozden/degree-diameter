SizeScreen([100000, 40]);
# usage: gap -q -c "mygrp:=SmallGroup(93,1);; OUT:=\"x.txt\";;" export.g   (mygrp must be preset)
mypg := Image(IsomorphismPermGroup(mygrp));
myels := ShallowCopy(AsList(mypg));
Sort(myels);
mynn := Length(myels);
myid := PositionSorted(myels, One(mypg));
PrintTo(OUT, mynn, "\n", myid, "\n");
for mya in [1..mynn] do
  myrow := List([1..mynn], myb -> PositionSorted(myels, myels[mya]*myels[myb]));
  AppendTo(OUT, JoinStringsWithSeparator(myrow, " "), "\n");
od;
mysubs := Filtered(List(ConjugacyClassesSubgroups(mypg), Representative), H -> Size(H) = 3);
AppendTo(OUT, "SUBS ", Length(mysubs), "\n");
for H in mysubs do
  AppendTo(OUT, JoinStringsWithSeparator(Concatenation([Size(H)], List(Elements(H), x -> PositionSorted(myels, x))), " "), "\n");
od;
AppendTo(OUT, "DONE\n");
QUIT;
