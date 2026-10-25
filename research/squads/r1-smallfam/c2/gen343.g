P := ExtraspecialGroup(343,7);;
Print("P343: ", Size(P), " exp ", Exponent(P), " ", StructureDescription(P), "\n");
A := AutomorphismGroup(P);;
Print("Aut343: ", Size(A), " ", StructureDescription(A), "\n");
ZP := Centre(P);;
isfpf := function(H)
  local h, g;
  for h in Elements(H) do
    if h <> One(H) then
      for g in AsList(P) do
        if not g in ZP and Image(h, g) * g^-1 in ZP then
          return false;
        fi;
      od;
    fi;
  od;
  return true;
end;;
S2 := SylowSubgroup(A, 2);;
S3 := SylowSubgroup(A, 3);;
Print("S2 ", Size(S2), " S3 ", Size(S3), "\n");
cl2 := ConjugacyClassesSubgroups(S2);;
cl3 := ConjugacyClassesSubgroups(S3);;
for c in Concatenation(cl2, cl3) do
  H := Representative(c);
  if Size(H) in [4,8,9] then
    hom := GroupHomomorphismByImages(H, A, GeneratorsOfGroup(H), GeneratorsOfGroup(H));
    G := SemidirectProduct(H, hom, P);
    n := Size(G);
    pc := Range(IsomorphismPcGroup(G));;
    Print("CAND n=", n, " H=", StructureDescription(H), " fpf=", isfpf(H), " PCC=PcGroupCode(", CodePcGroup(pc), ",", n, ")", " SD=", StructureDescription(G), "\n");
  fi;
od;
QUIT;
