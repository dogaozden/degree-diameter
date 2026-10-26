Read("/home/user/degree-diameter/research/fresh65/tools/bicoset.g");
W := "/home/user/degree-diameter/research/squads/f65r1/c15/work/";
Cases := [
 ["PSL27xZ7", DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 7)), 3],
 ["PSL28xZ3", DirectProduct(PSL(2,8), CyclicGroup(IsPermGroup, 3)), 4],
 ["A5xZ18", DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 18)), 3],
 ["SL25xZ9", DirectProduct(SmallGroup(120,5), CyclicGroup(IsPermGroup, 9)), 3],
 ["A5xS3xZ3", DirectProduct(AlternatingGroup(5), SymmetricGroup(3), CyclicGroup(IsPermGroup, 3)), 3],
 ["A5xA5", DirectProduct(AlternatingGroup(5), AlternatingGroup(5)), 9],
 ["A5xA5_10", DirectProduct(AlternatingGroup(5), AlternatingGroup(5)), 10],
 ["A5xZ12", DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 12)), 2],
 ["PSL27xZ5", DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 5)), 2],
 ["S6", SymmetricGroup(6), 2],
 ["A6xZ2", DirectProduct(AlternatingGroup(6), CyclicGroup(IsPermGroup, 2)), 2],
 ["S5xZ6", DirectProduct(SymmetricGroup(5), CyclicGroup(IsPermGroup, 6)), 2],
 ["S5xZ7", DirectProduct(SymmetricGroup(5), CyclicGroup(IsPermGroup, 7)), 2],
 ["PGL29", PGL(2,9), 2]
];
for c in Cases do
    G := c[2]; h := c[3];
    iso := IsomorphismPermGroup(G); G := Image(iso);
    cc := Filtered(ConjugacyClassesSubgroups(G), x -> Size(Representative(x)) = h and Size(Core(G, Representative(x))) = 1);
    reps := List(cc, Representative);
    Print("CASE ", c[1], " |G|=", Size(G), " h=", h, " classes=", Length(reps), "\n");
    for i in [1..Length(reps)] do for j in [i..Length(reps)] do
        cnt := CountUnions(G, reps[i], reps[j], 6);
        lab := Concatenation(c[1], "_", String(i), "_", String(j));
        if cnt <= 7000000 then
            ExportBicoset(G, reps[i], reps[j], Concatenation(W, lab, ".txt"), lab);
            Print("EXPORT ", lab, " perSide=", Size(G)/h, " candidates=", cnt, "\n");
        else
            Print("SKIP ", lab, " perSide=", Size(G)/h, " candidates=", cnt, "\n");
        fi;
    od; od;
od;
Print("ALLDONE\n");
QUIT;
