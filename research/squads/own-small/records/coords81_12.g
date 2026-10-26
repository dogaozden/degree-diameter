# Express the elements of SmallGroup(81,12) (numbered as in gap_export.g: identity 0, then AsSSortedList order)
# as (z, a, b, c) in C3 x He3, He3 = {[[1,a,c],[0,1,b],[0,0,1]]} over GF(3).
G := SmallGroup(81, 12);
el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
F := GF(3); o := One(F); zr := Zero(F);
mk := function(z, a, b, c) return [[o, a*o, c*o, zr, zr], [zr, o, b*o, zr, zr], [zr, zr, o, zr, zr], [zr, zr, zr, o, z*o], [zr, zr, zr, zr, o]]; end;
M := Group([mk(0,1,0,0), mk(0,0,1,0), mk(1,0,0,0)]);
Print("order ", Size(M), "\n");
iso := IsomorphismGroups(G, M);
for i in [1..81] do
  m := Image(iso, el[i]);
  Print(i - 1, " ", IntFFE(m[4][5]), " ", IntFFE(m[1][2]), " ", IntFFE(m[2][3]), " ", IntFFE(m[1][3]), "\n");
od;
QUIT;
