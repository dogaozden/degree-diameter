# Coset (bi-coset) graphs of almost-simple groups at (6,5) (job fresh-6-5).
# For each group G below and every pair (L, R) of conjugacy classes of subgroups of the same order h with
# |G|/h in [343, IMAX], export B(G; L, R) for bicoset.c, unless it has more than MAXC candidate unions.
# usage: gap -q -c 'OUTDIR:="../bc/simple";; IMAX:=420;; MAXC:=3000000;;' bicoset.g scan_simple.g
GROUPS := [
  ["PSL2_13", PSL(2,13)], ["PGL2_13", PGL(2,13)], ["PSL2_16", PSL(2,16)], ["PSL2_17", PSL(2,17)],
  ["PSL2_19", PSL(2,19)], ["PGL2_11", PGL(2,11)], ["PGL2_17", PGL(2,17)], ["PGL2_19", PGL(2,19)],
  ["PSL2_23", PSL(2,23)], ["PSL2_25", PSL(2,25)], ["PSL2_27", PSL(2,27)], ["PSL2_29", PSL(2,29)],
  ["PSL2_31", PSL(2,31)], ["PSL2_37", PSL(2,37)], ["PGammaL2_8", PrimitiveGroup(9, 9)],
  ["A7", AlternatingGroup(7)], ["S7", SymmetricGroup(7)], ["S6", SymmetricGroup(6)],
  ["PGammaL2_9", PrimitiveGroup(10, 7)], ["M10", PrimitiveGroup(10, 6)], ["PGL2_9", PrimitiveGroup(10, 4)],
  ["PSL3_3", PSL(3,3)], ["PSU3_3", PSU(3,3)], ["M11", MathieuGroup(11)], ["A8", AlternatingGroup(8)],
  ["PSL3_4", PSL(3,4)], ["PSp4_3", PSp(4,3)], ["Sz8", SuzukiGroup(IsPermGroup, 8)],
  ["PSL2_7xC7", DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 7))],
];
for gg in GROUPS do
    name := gg[1]; G := gg[2];
    if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
    G := Image(SmallerDegreePermutationRepresentation(G));
    cls := Filtered(ConjugacyClassesSubgroups(G), c -> Index(G, Representative(c)) >= 343 and Index(G, Representative(c)) <= IMAX);
    Print("GROUP ", name, " |G|=", Size(G), " classes=", Length(cls), "\n");
    for i in [1..Length(cls)] do
        for j in [i..Length(cls)] do
            L := Representative(cls[i]); R := Representative(cls[j]);
            if Size(L) <> Size(R) then continue; fi;
            c := CountUnions(G, L, R, 6);
            lab := Concatenation("cs_", name, "_h", String(Size(L)), "_L", String(i), "_R", String(j));
            if c = 0 or c > MAXC then
                Print("SKIP ", lab, " index=", Index(G, L), " cand=", c, " ", StructureDescription(L), "/", StructureDescription(R), "\n");
                continue;
            fi;
            r := ExportBicoset(G, L, R, Concatenation(OUTDIR, "/", lab, ".tmp"), lab);
            Exec(Concatenation("mv ", OUTDIR, "/", lab, ".tmp ", OUTDIR, "/", lab, ".txt"));
            Print("EXPORT ", lab, " index=", Index(G, L), " cand=", c, " ", StructureDescription(L), "/", StructureDescription(R), "\n");
        od;
    od;
od;
Print("ALLDONE\n");
QUIT;
