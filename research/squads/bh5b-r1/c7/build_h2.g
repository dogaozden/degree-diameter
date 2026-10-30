Read("dc2_lib.g");
# F_7^2 : AGL(1,7) = {v -> v*M + u : M = [[a,b],[0,1]]}, order 49*42
F7 := GF(7); vecs := Elements(F7^2);
tr := List([[1,0],[0,1]], u -> PermList(List(vecs, v -> Position(vecs, v + u*One(F7)))));
mA := PermList(List(vecs, v -> Position(vecs, v * [[3*One(F7),0*One(F7)],[0*One(F7),One(F7)]]))); # placeholder, replaced below
mA := PermList(List(vecs, v -> Position(vecs, v * [[3*One(F7),0*One(F7)],[0*One(F7),One(F7)]])));
mB := PermList(List(vecs, v -> Position(vecs, v * [[One(F7),One(F7)],[0*One(F7),One(F7)]])));
F7AGL := Group(Concatenation(tr, [mA, mB]));
Print("F7^2:AGL(1,7) order ", Size(F7AGL), "\n");
