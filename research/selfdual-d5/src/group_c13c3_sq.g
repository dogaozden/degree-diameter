# (C13 : C3) x (C13 : C3) = F13^2 : <diag(a,1), diag(1,a)>, a = Z(13)^4 of order 3 (squad sd5b-r1 card c4); mkaff from c4/mk.g:
mkaff := function(p, mats) local F, vs, gens, o, z, e1, e2, M; F := GF(p); z := Zero(F); o := One(F); vs := AsList(FullRowSpace(F, 2)); e1 := First(vs, x -> x[1] = o and x[2] = z); e2 := First(vs, x -> x[1] = z and x[2] = o); gens := [PermList(List(vs, v -> Position(vs, v + e1))), PermList(List(vs, v -> Position(vs, v + e2)))]; for M in mats do Add(gens, PermList(List(vs, v -> Position(vs, v * M)))); od; return Group(gens); end;;
F := GF(13); a := Z(13)^4; z := Zero(F); o := One(F);
G := mkaff(13, [[[a,z],[z,o]],[[o,z],[z,a]]]);;

Print("size ", Size(G), "\n");

