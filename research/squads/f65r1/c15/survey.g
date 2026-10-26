Read("/home/user/degree-diameter/research/fresh65/tools/bicoset.g");
Cases := [
 ["PSL27xZ7", DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 7)), 3],
 ["PSL28xZ3", DirectProduct(PSL(2,8), CyclicGroup(IsPermGroup, 3)), 4],
 ["A5xZ18", DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 18)), 3],
 ["SL25xZ9", DirectProduct(SmallGroup(120,5), CyclicGroup(IsPermGroup, 9)), 3],
 ["A5xS3xZ3", DirectProduct(AlternatingGroup(5), SymmetricGroup(3), CyclicGroup(IsPermGroup, 3)), 3],
 ["PSL2_11", PSL(2,11), 3],
 ["A5xA5", DirectProduct(AlternatingGroup(5), AlternatingGroup(5)), 9],
 ["A5xA5_10", DirectProduct(AlternatingGroup(5), AlternatingGroup(5)), 10],
 ["A5xZ12", DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 12)), 2],
 ["PSL27xZ5", DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 5)), 2]
];
for c in Cases do
    G := c[2]; h := c[3];
    iso := IsomorphismPermGroup(G); G := Image(iso);
    t := Runtime();
    cc := Filtered(ConjugacyClassesSubgroups(G), x -> Size(Representative(x)) = h and Size(Core(G, Representative(x))) = 1);
    reps := List(cc, Representative);
    Print("CASE ", c[1], " |G|=", Size(G), " h=", h, " coreFreeClasses=", Length(reps), " time=", Runtime()-t, "\n");
    for i in [1..Length(reps)] do for j in [i..Length(reps)] do
        cnt := CountUnions(G, reps[i], reps[j], 6);
        Print("  PAIR ", c[1], " i=", i, " j=", j, " sameclass=", i=j, " perSide=", Size(G)/h, " candidates=", cnt, "\n");
    od; od;
od;
QUIT;
