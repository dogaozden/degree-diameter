"""Third batch: nonsolvable centreless candidates (A5 x D21, S5 x D11), built with groups.py."""
import sys
import mk
from groups import table as gtable
from build1 import OUT
SPECS = {
    "A5xD21": lambda: gtable("perm 5 1,2,0,3,4 ; 1,2,3,4,0 x dih 21"),
    "S5xD11": lambda: gtable("perm 5 1,0,2,3,4 ; 1,2,3,4,0 x dih 11"),
}
if __name__ == "__main__":
    for name in (sys.argv[1:] or list(SPECS)):
        T = SPECS[name]()
        pr = mk.props(T, name)
        mk.write_bin(T, OUT + name + ".bin")
        print(pr, flush=True)
