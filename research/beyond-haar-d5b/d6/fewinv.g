# tables of few-involution groups of order 176-192 for (6,5) 2+2 lifts; prints the number of involutions
L := [ ["sl23xc8", DirectProduct(SL(2,3), CyclicGroup(8))], ["q8xc22", DirectProduct(QuaternionGroup(8), CyclicGroup(22))],
       ["q16xc11", DirectProduct(QuaternionGroup(16), CyclicGroup(11))], ["bo48xc4", DirectProduct(SmallGroup(48,28), CyclicGroup(4))],
       ["dic176", DicyclicGroup(176)], ["q8xc24", DirectProduct(QuaternionGroup(8), CyclicGroup(24))],
       ["c3q64", SmallGroup(192, 3)], ["sl23xq8", DirectProduct(SL(2,3), QuaternionGroup(8))] ];
for p in L do
  G := p[2]; el := Elements(G); e := Position(el, One(G)); el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  out := OutputTextFile(Concatenation("grp/fi_", p[1], ".txt"), false); SetPrintFormattingStatus(out, false);
  AppendTo(out, String(Size(G)), "\n");
  for g in el do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n"); od;
  CloseStream(out);
  Print(p[1], " order ", Size(G), " involutions ", Number(el, x -> Order(x) = 2), " ", StructureDescription(G), "\n");
od;
QUIT;
