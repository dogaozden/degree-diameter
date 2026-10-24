# Candidates G = (P x| H) x C_k, P = ExtraspecialGroup(27,3), H <= Aut(P) up to conjugacy, 1093 <= |G| <= 1400.
P := ExtraspecialGroup(27,3);;
A := AutomorphismGroup(P);;
Print("P: order ", Size(P), " exponent ", Exponent(P), " |Z(P)| ", Size(Centre(P)), "\n");;
Print("Aut(P) order ", Size(A), "\n");;
cls := ConjugacyClassesSubgroups(A);;
Print("classes of subgroups of Aut(P): ", Length(cls), "\n");;
for i in [1..Length(cls)] do
  H := Representative(cls[i]);;
  d := Size(H);;
  if d <= 51 then
    hom := GroupHomomorphismByImages(H, A, GeneratorsOfGroup(H), GeneratorsOfGroup(H));;
    S := SemidirectProduct(H, hom, P);;
    for k in [1..51] do
      if 41 <= d*k and d*k <= 51 then
        G := S;;
        if k > 1 then G := DirectProduct(S, CyclicGroup(IsPermGroup, k)); fi;;
        n := Size(G);;
        ab := Product(AbelianInvariants(G));;
        if IdGroupsAvailable(n) then idg := IdGroup(G);; else idg := "?";; fi;;
        Print("CAND class=", i, " |H|=", d, " H=", StructureDescription(H), " k=", k, " n=", n,
              " id=", idg, " ab=", ab, " abinv=", AbelianInvariants(G), "\n");;
      fi;;
    od;;
  fi;;
od;;
QUIT;;
