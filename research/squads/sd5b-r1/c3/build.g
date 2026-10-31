# c3 family: G = C_m : H, H non-cyclic, action through a cyclic quotient of H on C_m (m odd composite).
# Enumerates homs H -> Aut(C_m) with cyclic nontrivial image (via cyclic subgroups W of Aut(C_m) and
# generator-exponent tuples), dedups by IdGroup, exports each group with export_sd.g (NOEXT: K = 9 is odd).
# Writes c3/manifest.txt: "idx N ID m Hdesc tag".
EXPDIR := "/home/user/degree-diameter/research/squads/sd5b-r1/c3/";;
BuildFam := function(m, H, cap)
  local C, A, Al, Ex, gens, r, seenW, res, ids, w, d, W, key, tup, imgs, hom, G, id, L;
  C := CyclicGroup(IsPcGroup, m);
  A := AutomorphismGroup(C);
  Al := AsList(A);
  Ex := Exponent(H);
  gens := SmallGeneratingSet(H);
  r := Length(gens);
  seenW := [];
  res := [];
  ids := [];
  for w in Al do
    d := Order(w);
    if d = 1 or Ex mod d <> 0 then continue; fi;
    W := Group(w);
    key := Set(List(AsList(W), x -> Image(x, C.1)));
    if key in seenW then continue; fi;
    Add(seenW, key);
    for tup in Tuples([0..d-1], r) do
      if ForAll(tup, e -> e = 0) then continue; fi;
      imgs := List(tup, e -> w^e);
      hom := GroupHomomorphismByImages(H, A, gens, imgs);
      if hom = fail then continue; fi;
      G := SemidirectProduct(H, hom, C);
      id := IdGroup(G);
      if not id in ids then
        Add(ids, id);
        Add(res, [G, id, tup]);
        if Length(res) >= cap then return res; fi;
      fi;
    od;
  od;
  return res;
end;;
