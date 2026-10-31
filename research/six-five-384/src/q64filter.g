# For each order-128 group id in Q128 (the Sylow-2 quotients G/O_3(G) of the order-384 groups), list the ids of
# its quotients of order 64 by central subgroups of order 2. Output lines "q128 <id> : <ids of order-64 quotients>".
# usage: gap -q -A -c 'Q128:=[1,2];; FN:="q64of128.txt";;' q64filter.g
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
for id in Q128 do
  P := SmallGroup(128, id);
  zs := Filtered(Elements(Centre(P)), x -> Order(x) = 2);
  ids := Set(zs, z -> IdGroup(P / Subgroup(P, [z]))[2]);
  AppendTo(out, "q128 ", id, " : ", JoinStringsWithSeparator(List(ids, String), " "), "\n");
od;
CloseStream(out);
QUIT;
