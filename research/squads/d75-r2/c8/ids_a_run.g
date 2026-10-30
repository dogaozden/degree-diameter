Read("/home/user/degree-diameter/research/squads/d75-r2/c8/ids_a.g");
L := [[73,3,3],[83,2,4],[37,6,3],[37,9,2],[167,2,2],[113,2,3],[19,9,4],[19,18,2],[173,2,2],[71,5,2],[79,3,3],[89,2,4],[89,4,2],[179,2,2]];;
for t in L do
  G := mkMeta(t[1], t[2], t[3]);;
  Print(t, " ", Size(G), " ", IsAbelian(G), " ", Size(Centre(G)), " ", IdGroup(G), "\n");
od;
QUIT;
