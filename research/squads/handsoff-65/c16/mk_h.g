# Groups G = P x| Q of order 343*|Q| (P = SmallGroup(343,i), Q in {C4, V4} for |Q|=4 or {C6, S3} for |Q|=6), Q acting
# through random sampled homomorphisms into Aut(P). Exports bi-coset pairs for subgroups of order |Q|
# (n = 2|G|/|H|: |Q|=4 gives n = |G|/2, |Q|=6 gives n = |G|/3, both 686 for the right orders).
# usage: gap -q -c 'QN:="C4"; ' mk_h.g   (QN in C4, V4, C6, S3)
Read("dc2_lib.g");
if QN = "C4" then Q := CyclicGroup(IsPermGroup, 4); fi;
if QN = "V4" then Q := Group([(1,2),(3,4)]); fi;
if QN = "C6" then Q := CyclicGroup(IsPermGroup, 6); fi;
if QN = "S3" then Q := SymmetricGroup(3); fi;
h := Size(Q);
gq := GeneratorsOfGroup(Q);
for i in [1..5] do
  P := SmallGroup(343, i);
  A := AutomorphismGroup(P);
  homs := [];
  for t in [1..1500]do
    if Length(homs) >= 4 then break; fi;
    imgs := fail;
    x := Random(A); o := Order(x);
    if QN = "C4" and o mod 4 = 0 then imgs := [x^(o/4)]; fi;
    if QN = "C6" and o mod 6 = 0 then imgs := [x^(o/6)]; fi;
    if QN = "V4" and o mod 2 = 0 then
      w := Random(A); ow := Order(w);
      if ow mod 2 = 0 then imgs := [x^(o/2), w^(ow/2)]; fi;
    fi;
    if QN = "S3" and o mod 3 = 0 then
      w := Random(A); ow := Order(w);
      if ow mod 2 = 0 then imgs := [w^(ow/2), x^(o/3)]; fi;
    fi;
    if imgs <> fail then
      hom := GroupHomomorphismByImages(Q, A, gq, imgs);
      if hom <> fail then
        if ForAll(homs, hh -> not ForAll(gq, g -> g^hom = g^hh)) then
          Add(homs, hom);
        fi;
      fi;
    fi;
  od;
  Print("QN ", QN, " P", i, " ", StructureDescription(P), " actions: ", Length(homs), "\n");
  for k in [1..Length(homs)] do
    G := SemidirectProduct(Q, homs[k], P);
    G := Image(IsomorphismPermGroup(G));
    Print("  G order ", Size(G), " k=", k, "\n");
    ExportPairs(G, h, Concatenation("x", String(343*h), "/", QN, "_g", String(i), "_", String(k)));
  od;
od;
QUIT;
