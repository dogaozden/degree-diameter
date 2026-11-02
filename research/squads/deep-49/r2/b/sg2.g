Read("/home/user/degree-diameter/research/squads/deep-49/r2/b/exp_b.g");
D := "/home/user/degree-diameter/research/squads/deep-49/r2/b/";
L := [[2486,3],[2494,3],[2498,1],[2524,3],[2564,3],[2572,3],[2526,1],[1996,1],[1996,3],[2012,1],[2012,3],[2036,1],[2036,3],[2036,4],[2084,1],[2084,3],[2084,4],[2092,1],[2092,3]];
for p in L do
  ExportNoAut(SmallGroup(p[1], p[2]), Concatenation(D, "SG", String(p[1]), "_", String(p[2]), ".exp"));
od;
ExportNoAut(Image(IsomorphismPermGroup(DirectProduct(AlternatingGroup(5), CyclicGroup(34)))), Concatenation(D, "NS_A5xC34.exp"));
ExportNoAut(Image(IsomorphismPermGroup(DirectProduct(SL(2,5), CyclicGroup(17)))), Concatenation(D, "NS_SL25xC17.exp"));
ExportNoAut(Image(IsomorphismPermGroup(DirectProduct(PSL(2,8), CyclicGroup(4)))), Concatenation(D, "NS_PSL28xC4.exp"));
ExportNoAut(Image(IsomorphismPermGroup(DirectProduct(PSL(2,7), AlternatingGroup(4)))), Concatenation(D, "NS_PSL27xA4.exp"));
Print("exports done\n");
QUIT;
