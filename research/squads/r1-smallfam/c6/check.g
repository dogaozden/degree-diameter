MK := function(M, R)
  return Group(PermList(List([0..M-1], x -> ((x+1) mod M) + 1)), PermList(List([0..M-1], x -> ((R*x) mod M) + 1)));
end;;
L := [[549,2,548],[77,15,4],[133,9,4],[105,12,2],[403,3,87],[121,10,40],[189,6,17],[55,20,2],[93,30,11],[455,6,4],[125,20,7],[221,12,4]];;
for t in L do
  G := MK(t[1], t[3]);;
  Print(t[1]*t[2], " m=", t[1], " k=", t[2], " r=", t[3], " size=", Size(G), " ab=", AbelianInvariants(G), " ", StructureDescription(G), "\n");
od;
QUIT;
