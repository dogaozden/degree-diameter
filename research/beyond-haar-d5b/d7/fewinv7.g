L := [ ["sl23xc13", DirectProduct(SL(2,3), CyclicGroup(13))], ["q16xc19", DirectProduct(QuaternionGroup(16), CyclicGroup(19))],
       ["q8xc39", DirectProduct(QuaternionGroup(8), CyclicGroup(39))], ["bo48xc7", DirectProduct(SmallGroup(48,28), CyclicGroup(7))],
       ["q32xc10", DirectProduct(QuaternionGroup(32), CyclicGroup(10))], ["sl23xc14", DirectProduct(SL(2,3), CyclicGroup(14))],
       ["q8c4xc10", DirectProduct(SmallGroup(32,10), CyclicGroup(10))], ["c4q8xc10", DirectProduct(SmallGroup(32,35), CyclicGroup(10))] ];
for p in L do
  G := p[2]; el := Elements(G); e := Position(el, One(G)); el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  out := OutputTextFile(Concatenation("grp/fi_", p[1], ".txt"), false); SetPrintFormattingStatus(out, false);
  AppendTo(out, String(Size(G)), "\n");
  for g in el do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n"); od;
  CloseStream(out);
  Print(p[1], " order ", Size(G), " involutions ", Number(el, x -> Order(x) = 2), "\n");
od;
QUIT;
