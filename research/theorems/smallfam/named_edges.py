"""Edge list of a Haar graph found by named.py, rebuilt by GAP from the same expression (for apsp verification).
Usage: python3 named_edges.py "GAP expression" OUT i1 i2 ... iDELTA
  (indices = the SOL line of named.py: 0-based positions in AsSSortedList of the IsomorphismPermGroup image)
Then: verify/apsp OUT DELTA D   must print RESULT VALID."""
import subprocess
import sys

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from named import PRELUDE  # noqa: E402

expr, out, idx = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3:]]
script = PRELUDE + f'''
GRP0 := {expr};; GRP := Image(IsomorphismPermGroup(GRP0));; el := AsSSortedList(GRP);; N := Length(el);;
S := List({idx}, i -> el[i + 1]);;
f := OutputTextFile("{out}", false);; SetPrintFormattingStatus(f, false);;
AppendTo(f, 2 * N, "\\n");;
for i in [1..N] do for s in S do AppendTo(f, i - 1, " ", N + Position(el, s * el[i]) - 1, "\\n");; od; od;
CloseStream(f);; Print("wrote ", 2 * N, " vertices\\n"); QUIT;
'''
print(subprocess.run(['gap', '-q', '-o', '8g'], input=script, capture_output=True, text=True).stdout.strip())
