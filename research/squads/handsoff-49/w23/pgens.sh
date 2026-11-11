#!/bin/bash
# prints P spec and generator indices for the nonabelian groups of order 625 used by w15
cd /home/user/degree-diameter/research/squads/handsoff-49/w15
python3 - << 'PY'
import sys
sys.path.insert(0,'/home/user/degree-diameter/research/squads/handsoff-49/tools')
import groups as GR
specs = {
 'meta25_25_6': ("meta 25 25 6", [1, 25]),
 'meta125_5_26': ("meta 125 5 26", [1, 125]),
 'semi5_25': ("semi 5 25 1 1 0 1", [1, 5, 25]),
 'M125xZ5': ("meta 25 5 6 x cyc 5", [5, 125, 1]),
}
for k,(s,g) in specs.items():
    T = GR.table(s)
    print(k, len(T), s, ','.join(map(str,g)))
PY
