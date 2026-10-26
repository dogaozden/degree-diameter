#!/usr/bin/env python3
"""Put the table printed by results.py between the TABLE markers of BEYOND_TABLE.md."""
import subprocess, os, re
here = os.path.dirname(os.path.abspath(__file__))
tab = subprocess.run(["python3", os.path.join(here, "results.py")], capture_output=True, text=True, check=True).stdout
p = os.path.join(here, "BEYOND_TABLE.md")
s = open(p).read()
s = re.sub(r"<!-- TABLE -->.*?<!-- /TABLE -->", "<!-- TABLE -->\n" + tab + "<!-- /TABLE -->", s, flags=re.S)
open(p, "w").write(s)
