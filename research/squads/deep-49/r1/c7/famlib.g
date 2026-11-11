Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/lib.g");
Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
# C13 : C_c where the generator of C_c acts as an automorphism of order img
MkFimg := function(c, img)
  local C, N, a, hom;
  N := CyclicGroup(IsPermGroup, 13);
  C := CyclicGroup(IsPermGroup, c);
  a := First(Elements(AutomorphismGroup(N)), x -> Order(x) = img);
  hom := GroupHomomorphismByImages(C, AutomorphismGroup(N), [C.1], [a]);
  return Image(IsomorphismPcGroup(SemidirectProduct(C, hom, N)));
end;
PcOf := function(n, i)
  return Image(IsomorphismPcGroup(SmallGroup(n, i)));
end;
# direct products X x Y over SmallGroups(a) x SmallGroups(b), or the given base X's
PairFam := function(label, Xs, Ys, dir)
  local X, Y, G, cnt, fn, k, res, ex;
  cnt := 0; k := 0;
  for X in Xs do
    for Y in Ys do
      G := DirectProduct(X, Y);
      k := k + 1;
      if GabOrder(G) <= 309 and Length(MinimalGeneratingSet(G)) <= 3 then
        if not IsMetac(G) then
          cnt := cnt + 1;
          fn := Concatenation(dir, label, "_", String(k), ".exp");
          ExportGroup(G, fn);
          Print("EXP ", label, " ", k, " ", Size(G), " ab ",
                AbelianInvariants(G), " d ",
                Length(MinimalGeneratingSet(G)), " ", fn, "\n");
        fi;
      fi;
    od;
  od;
  Print("family ", label, " pairs ", k, " exported ", cnt, "\n");
end;
DIR := "/home/user/degree-diameter/research/squads/deep-49/r1/c7/exp/";
