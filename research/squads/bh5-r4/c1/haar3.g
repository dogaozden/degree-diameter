Read("/home/user/degree-diameter/research/beyond-haar-d5/coset/dc2_lib.g");
for i in [473, 475, 476] do
  G := Image(IsomorphismPermGroup(SmallGroup(1200, i)));
  N := Filtered(NormalSubgroups(G), M -> Index(G, M) = 2)[1];
  Hs := SubsOfOrderFast(G, 2);
  Print("1200/", i, " classes of involution subgroups: ", Length(Hs), " H in N for each: ", List(Hs, H -> Size(Intersection(H, N)) = 2), "\n");
od;
QUIT;
