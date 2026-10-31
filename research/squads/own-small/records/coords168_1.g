# Elements of SmallGroup(168,1) = C7 : C24 (gap_export numbering) as (i, j) with g = a^i b^j, a of order 7, b of order 24,
# b a b^-1 = a^s; product (i,j)(k,l) = (i + s^j k mod 7, j + l mod 24).
G := SmallGroup(168, 1);
el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
a := First(el, x -> Order(x) = 7);
b := First(el, x -> Order(x) = 24 and not (x in Subgroup(G, [a])));
s := First([1..6], k -> b * a * b^-1 = a^k);
Print("s ", s, "\n");
for g in [1..168] do
  ij := First(Cartesian([0..6], [0..23]), t -> a^t[1] * b^t[2] = el[g]);
  Print(g - 1, " ", ij[1], " ", ij[2], "\n");
od;
QUIT;
