P := ExtraspecialGroup(125,5);;
Print("P: ", Size(P), " exp ", Exponent(P), " ", StructureDescription(P), "\n");
A := AutomorphismGroup(P);;
Print("Aut: ", Size(A), " ", StructureDescription(A), "\n");
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
Print("element orders in Aut: ", Collected(List(AsList(A), Order)), "\n");
tm := Runtime();;
cl := ConjugacyClassesSubgroups(A);;
Print("nclasses ", Length(cl), " time ", Runtime() - tm, "ms\n");
for c in cl do
  H := Representative(c);
  if Size(H) in [9,10,11,12,20,24,25,26] then
    Print("H size ", Size(H), " ", StructureDescription(H), " fpf=", isfpf(H), " nconj=", Size(c), " cyc=", IsCyclic(H), "\n");
  fi;
od;
QUIT;
