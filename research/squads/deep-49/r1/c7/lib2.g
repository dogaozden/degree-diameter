# c7: N = C_m (m prime, normal Sylow, characteristic) semidirect H, H from SmallGroups(|H|).
# Iso classes = Aut(H)-orbits on Hom(H, Aut(N)) (exact for characteristic N).
Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/lib.g");
Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
SemiReps := function(m, H)
  local A, Ael, N, nat, Hab, hg, cands, vecs, tup, psi, phi, Eh,
        v, autH, orb, done, reps, idx, w, pa, al, k, res, pai;
  N := CyclicGroup(IsPermGroup, m);
  A := AutomorphismGroup(N);
  Ael := Elements(A);
  nat := NaturalHomomorphismByNormalSubgroup(H, DerivedSubgroup(H));
  Hab := Image(nat);
  hg := MinimalGeneratingSet(Hab);
  cands := List(hg, h -> Filtered(Ael, x -> x^Order(h) = One(A)));
  Eh := AsList(H);
  vecs := [];
  for tup in Cartesian(cands) do
    psi := GroupHomomorphismByImages(Hab, A, hg, tup);
    if psi <> fail then
      phi := nat * psi;
      v := List(Eh, h -> Position(Ael, Image(phi, h)));
      Add(vecs, [v, phi]);
    fi;
  od;
  autH := GeneratorsOfGroup(AutomorphismGroup(H));
  pa := List(autH, al -> List(Eh, h -> Position(Eh, Image(al, h))));
  done := [];
  reps := [];
  for idx in [1..Length(vecs)] do
    if not vecs[idx][1] in done then
      orb := [vecs[idx][1]]; k := 1;
      while k <= Length(orb) do
        for pai in pa do
          w := List(pai, i -> orb[k][i]);
          if not w in orb then Add(orb, w); fi;
        od;
        k := k + 1;
      od;
      Append(done, orb);
      Add(reps, vecs[idx][2]);
    fi;
  od;
  res := List(reps, phi -> SemidirectProduct(H, phi, N));
  return res;
end;

RunOrder := function(ORD, m, hsz, ilist)
  local i, H, Gs, G, k, d, metac, fn, dir;
  dir := "/home/user/degree-diameter/research/squads/deep-49/r1/c7/exp/";
  for i in ilist do
    H := SmallGroup(hsz, i);
    Gs := SemiReps(m, H);
    k := 0;
    for G in Gs do
      k := k + 1;
      if GabOrder(G) <= 309 then
        d := Length(MinimalGeneratingSet(G));
        metac := IsMetac(G);
        Print("ORD ", ORD, " H ", i, " k ", k, " ab ", AbelianInvariants(G),
              " d ", d, " metac ", metac, "\n");
        if (not metac) and d <= 3 then
          fn := Concatenation(dir, "o", String(ORD), "_h", String(i),
                              "_", String(k), ".exp");
          ExportGroup(G, fn);
          Print("EXPORTED ", fn, "\n");
        fi;
      else
        Print("ORD ", ORD, " H ", i, " k ", k, " SKIP ab ",
              AbelianInvariants(G), "\n");
      fi;
    od;
  od;
end;
