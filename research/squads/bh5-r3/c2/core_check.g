# for each (order, id, h, i) reported best: is the class-representative subgroup H_i non-normal (core trivial)?
checks := [[558,10,3,2],[549,1,3,1],[549,3,3,2],[540,101,3,1],[540,101,3,4],[540,100,3,1],[552,18,3,1],[552,20,3,1]];
for c in checks do
  G := SmallGroup(c[1], c[2]);
  Hs := SubsOfOrder(G, c[3]);
  Print(c, " |Hs|=", Length(Hs), " core size of H_i = ", Size(Core(G, Hs[c[4]])), " normal=", IsNormal(G, Hs[c[4]]), "\n");
od;
QUIT;
