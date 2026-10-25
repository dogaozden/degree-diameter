import json, sys
# usage: score.py BEST_COST BEST_GROUP VALID SCORE NEXT COMMAND IDEA
best_cost, best_group, valid, score, nxt, command, idea = sys.argv[1:8]
rec = {"card": "c3", "idea": idea,
       "code": "/home/user/degree-diameter/research/squads/r2-smallfam/c3/run_screen.sh",
       "command": command, "score": int(score), "best_cost": int(best_cost), "best_group": best_group,
       "cell": "(3,10)", "valid": valid == "true", "next": nxt}
print(json.dumps(rec))
