# isomorphism test for the 6 pairs of split metacyclic groups with equal order distribution / centre size (r2c)
Mk := function(m, k, r)
  local F, G;
  F := FreeGroup("a", "b");
  G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
  return Image(IsomorphismPcGroup(G));
end;;
pairs := [[41,60,2,123,20,43],[17,144,3,153,16,10],[41,60,4,123,20,4],[82,30,23,246,10,25],[17,144,2,153,16,19],[34,72,9,306,8,19]];
for p in pairs do
  G1 := Mk(p[1],p[2],p[3]); G2 := Mk(p[4],p[5],p[6]);
  Print(p, " sizes ", Size(G1), " ", Size(G2), " iso: ", IsomorphismGroups(G1, G2) <> fail, "\n");
od;
QUIT;
