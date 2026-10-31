# G = F_7^3 x| S3 as affine permutations on 343 points, S3 = <s,t> with s = diag(1,2,4), t = swap of coordinates 1,2
# (t s t = s^-1). Exports bi-coset pairs for subgroups of order 6 (dc2_lib.g). Also the Z_7^3 x| C6 = s x (-1)?? (skipped).
Read("dc2_lib.g");
F := GF(7);
vecs := Elements(F^3);
pos := function(v) return Position(vecs, v); end;
mkperm := function(M, c) return PermList(List(vecs, v -> pos(v * M + c))); end;
I3 := IdentityMat(3, F);
s := [[1,0,0],[0,2,0],[0,0,4]] * Z(7)^0;
s := List(s, r -> List(r, x -> x * Z(7)^0));
s := [[Z(7)^0,0*Z(7),0*Z(7)],[0*Z(7),Z(7)^2,0*Z(7)],[0*Z(7),0*Z(7),Z(7)^4]];
t := [[Z(7)^0,0*Z(7),0*Z(7)],[0*Z(7),0*Z(7),Z(7)^0],[0*Z(7),Z(7)^0,0*Z(7)]];
gens := [mkperm(s, Zero(F^3)), mkperm(t, Zero(F^3)),
         mkperm(I3, [Z(7)^0, 0*Z(7), 0*Z(7)]), mkperm(I3, [0*Z(7), Z(7)^0, 0*Z(7)]), mkperm(I3, [0*Z(7), 0*Z(7), Z(7)^0])];
G := Group(gens);
Print("order ", Size(G), " (expect 2058)\n");
Print("s^-1 check: ", (mkperm(s,Zero(F^3)))^3 = (), " t^2: ", (mkperm(t,Zero(F^3)))^2 = (), "\n");
ExportPairs(G, 6, "x2058/S3aff");
QUIT;
