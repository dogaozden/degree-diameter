# Elements of SmallGroup(165,1) (gap_export numbering) as (z, a, j): C3 x (Z11 x|_3 Z5), product
# (z,a,j)(z',a',j') = (z+z' mod 3, a + 3^j a' mod 11, j+j' mod 5). The affine part is realised as maps x -> 3^j x + a on Z11.
G := SmallGroup(165, 1);
el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
c3 := CyclicGroup(IsPermGroup, 3);
aff := Group(PermList(List([0..10], x -> (x + 1) mod 11 + 1)), PermList(List([0..10], x -> (3 * x) mod 11 + 1)));
T := DirectProduct(c3, aff);
iso := IsomorphismGroups(G, T);
gz := MinimalGeneratingSet(c3)[1];
for i in [1..165] do
  t := Image(iso, el[i]);
  z := First([0..2], k -> Image(Projection(T, 1), t) = gz^k);
  p := Image(Projection(T, 2), t);
  a := (0 + 1)^p - 1; s := ((1 + 1)^p - 1 - a) mod 11;   # p: x -> s x + a, s = 3^j
  j := First([0..4], k -> 3^k mod 11 = s);
  Print(i - 1, " ", z, " ", a, " ", j, "\n");
od;
QUIT;
