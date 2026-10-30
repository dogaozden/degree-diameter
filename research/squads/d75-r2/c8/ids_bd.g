Read("/home/user/degree-diameter/research/squads/d75-r2/c8/ids_a.g");;
Lb := [[657,3,73,3],[658,7,47,2],[660,6,11,10],[660,12,11,5],[663,17,13,3],[664,4,83,2],[666,2,37,9],[666,3,37,6],[666,6,37,3],[666,9,37,2],[668,2,167,2],[670,5,67,2],[672,16,7,6],[676,13,13,4],[678,3,113,2],[680,5,17,8],[680,10,17,4],[680,20,17,2],[682,11,31,2],[684,2,19,18],[684,4,19,9],[684,6,19,6],[684,12,19,3],[684,18,19,2],[688,8,43,2],[690,15,23,2],[692,2,173,2],[696,6,29,4],[696,12,29,2],[702,9,13,6],[702,18,13,3],[708,6,59,2],[710,2,71,5],[710,5,71,2],[711,3,79,3],[712,2,89,4],[712,4,89,2],[714,17,7,6],[714,21,17,2],[715,13,11,5],[716,2,179,2]];;
for t in Lb do
  G := DirectProduct(CyclicGroup(IsPermGroup, t[2]), mkMeta(t[3], t[4], 1));;
  Print("B ", t[1], " ", t[2], " ", t[3], " ", t[4], " ", IdGroup(G), "\n");
od;
Ld := [[672,"SL23xC28"],[696,"SL23xC29"],[720,"SL23xC30"]];;
Print("D SL23xC28 ", IdGroup(DirectProduct(SpecialLinearGroup(2,3), CyclicGroup(IsPermGroup,28))), "\n");
Print("D SL23xC29 ", IdGroup(DirectProduct(SpecialLinearGroup(2,3), CyclicGroup(IsPermGroup,29))), "\n");
Print("D SL23xC30 ", IdGroup(DirectProduct(SpecialLinearGroup(2,3), CyclicGroup(IsPermGroup,30))), "\n");
Print("D 2OxC14 ", IdGroup(DirectProduct(SmallGroup(48,28), CyclicGroup(IsPermGroup,14))), "\n");
Print("D GL23xC14 ", IdGroup(DirectProduct(GL(2,3), CyclicGroup(IsPermGroup,14))), "\n");
Print("D SL25xC6 ", IdGroup(DirectProduct(SpecialLinearGroup(2,5), CyclicGroup(IsPermGroup,6))), "\n");
QUIT;
