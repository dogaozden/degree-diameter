#!/bin/bash
# usage: gettable.sh n id outfile : multiplication table of SmallGroup(n,id), AsSSortedList order, 0-based
cat > /tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad/gt.g << EOG
G := SmallGroup($1, $2); el := AsSSortedList(G); tab := MultiplicationTable(el);
out := OutputTextFile("$3", false); SetPrintFormattingStatus(out, false);
for row in tab do WriteAll(out, Concatenation(JoinStringsWithSeparator(List(row, x -> String(x-1)), " "), "\n")); od;
CloseStream(out); QUIT;
EOG
gap -q -b /tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad/gt.g < /dev/null
