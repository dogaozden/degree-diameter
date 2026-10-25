#!/usr/bin/env python3
# usage: score_line.py CARD IDEA CODE COMMAND M BEST_COST VALID(0/1) LIFT_VERTICES NEXT  -> prints one JSON line
import json, sys
card, idea, code, command, m, best_cost, valid, lift_v, nxt = sys.argv[1:10]
valid = valid == '1'
rec = {"card": card, "idea": idea, "code": code, "command": command, "m": int(m), "best_cost": int(best_cost),
       "score": int(lift_v) if valid else 0, "valid": valid, "next": nxt}
print(json.dumps(rec))
