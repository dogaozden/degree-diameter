Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/famlib.g");
Reset(GlobalMersenneTwister, 7);
C4 := CyclicGroup(IsPermGroup, 4);
Pfam := function(lo, hi)
  local i, P, A, k, x, o, o2, o5, z, hom, G, cnt, fn, nsamp, seen;
  for i in [lo..hi] do
    P := PcOf(625, i);
    A := AutomorphismGroup(P);
    seen := [];
    nsamp := 0;
    for k in [1..400] do
      if nsamp >= 4 then break; fi;
      x := Random(A);
      o := Order(x);
      if o mod 2 = 0 then
        o2 := 2^PValuation(o, 2);
        o5 := o / o2;
        if o2 >= 4 then
          z := (x^o5)^(o2/4);
          if Order(z) = 4 and not z in seen then
            hom := GroupHomomorphismByImages(C4, A, [C4.1], [z]);
            if hom <> fail then
              G := SemidirectProduct(C4, hom, P);
              if GabOrder(G) <= 309 and Length(MinimalGeneratingSet(G)) <= 3 and not IsMetac(G) then
                nsamp := nsamp + 1;
                Add(seen, z);
                fn := Concatenation(DIR, "f2500p", String(i), "_", String(nsamp), ".exp");
                ExportGroup(G, fn);
                Print("EXP P", i, " s", nsamp, " ab ", AbelianInvariants(G), " ord ", Order(z), "\n");
              fi;
            fi;
          fi;
        fi;
      fi;
    od;
  od;
end;
Pfam(11, 15);
QUIT;
