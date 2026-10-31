# affine_group.g: G = F_p^d : C_k, y acting on F_p^d by R = C^E0 (C = companion matrix of a primitive polynomial of
# degree D0 over GF(P0), a Singer cycle of order P0^D0 - 1), the order of R dividing K0.  As a permutation group on
# P0^D0 + K0 points: translations of F_p^d, and y = (v -> R v) times a K0-cycle.  Read before export_sd.g with P0, D0,
# K0, E0 bound.  Sets G, prints the order of R.
F := GF(P0);;
pol := MinimalPolynomial(F, PrimitiveRoot(GF(P0^D0)));;
Cm := TransposedMat(CompanionMat(pol));;
Rm := Cm^E0;;
if K0 mod Order(Rm) <> 0 then Error("affine_group: order of R does not divide K0"); fi;
V := Elements(F^D0);;
nv := Length(V);;
gens := [];;
for i in [1..D0] do
  e := List([1..D0], j -> Zero(F)); e[i] := One(F);
  Add(gens, PermList(Concatenation(List(V, v -> Position(V, v + e)), [nv+1..nv+K0])));
od;
yp := PermList(Concatenation(List(V, v -> Position(V, Rm * v)), List([0..K0-1], j -> nv + (j + 1) mod K0 + 1)));;
Add(gens, yp);
G := Group(gens);;
if Size(G) <> nv * K0 then Error("affine_group: wrong order"); fi;
Print("ORDER_R ", Order(Rm), "\n");
