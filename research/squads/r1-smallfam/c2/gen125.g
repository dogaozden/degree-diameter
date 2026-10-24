P := ExtraspecialGroup(125,5);;
A := AutomorphismGroup(P);;
cl := ConjugacyClassesSubgroups(A);;
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
want := function(H)
  local s;
  s := Size(H);
  return (s = 12 and IsCyclic(H)) or (s = 12 and StructureDescription(H) = "C3 : C4") or (s = 12 and StructureDescription(H) = "D12")
      or (s = 10 and IsCyclic(H)) or (s = 24 and StructureDescription(H) in ["C24","SL(2,3)","C3 : C8"])
      or (s = 20 and StructureDescription(H) = "C20");
end;;
for c in cl do
  H := Representative(c);
  if want(H) then
    hom := GroupHomomorphismByImages(H, A, GeneratorsOfGroup(H), GeneratorsOfGroup(H));
    G := SemidirectProduct(H, hom, P);
    n := Size(G);
    if false then
      idg := IdGroup(G);
      Print("CAND n=", n, " H=", StructureDescription(H), " fpf=", isfpf(H), " SG=SmallGroup", idg, " SD=", StructureDescription(G), "\n");
    else
      pc := Range(IsomorphismPcGroup(G));;
      code := CodePcGroup(pc);
      Print("CAND n=", n, " H=", StructureDescription(H), " fpf=", isfpf(H), " PCC=PcGroupCode(", code, ",", n, ")", " SD=", StructureDescription(G), "\n");
    fi;
  fi;
od;
QUIT;
