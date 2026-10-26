# Elements of SmallGroup(296,3) = C37 : C8 (gap_export numbering) as (i, j) with g = a^i b^j, a of order 37, b of order 8,
# b a b^-1 = a^s; product (i,j)(k,l) = (i + s^j k mod 37, j + l mod 8).
G := SmallGroup(296, 3);
el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
a := First(el, x -> Order(x) = 37);
b := First(el, x -> Order(x) = 8 and not (x in Subgroup(G, [a])));
s := First([1..36], k -> b * a * b^-1 = a^k);
Print("s ", s, "\n");
for g in [1..296] do
  ij := First(Cartesian([0..36], [0..7]), t -> a^t[1] * b^t[2] = el[g]);
  Print(g - 1, " ", ij[1], " ", ij[2], "\n");
od;
QUIT;
