"""c7: one GAP session that writes the multiplication table and StructureDescription of every group of orders 17-25
into $SCRATCH/cache/<n>_<i>.tab and .struct (same format as screen.export_table), so the lift screen does not start
GAP once per group (that start cost about 6 s per group under the current load)."""
import os
import sys
SMALLFAM = '/home/user/degree-diameter/research/theorems/smallfam'
sys.path.insert(0, SMALLFAM)
from allgroups import gap  # noqa: E402
CACHE = os.path.join(os.environ['SCRATCH'], 'cache')
os.makedirs(CACHE, exist_ok=True)
script = f'''dir := "{CACHE}";;
for n in [17..25] do
  for i in [1..NrSmallGroups(n)] do
    GRP := SmallGroup(n, i);; el := AsSSortedList(GRP);; nn := Length(el);;
    base := Concatenation(dir, "/", String(n), "_", String(i));;
    f := OutputTextFile(Concatenation(base, ".tab"), false);; SetPrintFormattingStatus(f, false);;
    AppendTo(f, nn, " ", Position(el, One(GRP)) - 1, "\\n");;
    for x in el do AppendTo(f, JoinStringsWithSeparator(List(el, y -> String(Position(el, x * y) - 1)), " "), "\\n");; od;
    CloseStream(f);;
    g := OutputTextFile(Concatenation(base, ".struct"), false);; SetPrintFormattingStatus(g, false);;
    AppendTo(g, StructureDescription(GRP), "\\n");; CloseStream(g);;
  od;
od;;
QUIT;
'''
gap(script, 1200)
print('cached', len([f for f in os.listdir(CACHE) if f.endswith('.tab')]), 'tables in', CACHE)
