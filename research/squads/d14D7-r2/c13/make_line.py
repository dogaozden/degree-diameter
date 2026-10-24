import json
rec = {
    "card": "c13",
    "idea": "Type-2 units on the single matching of the (13,7) cover (H(11), j=1, Z_3, Delta 13): 81 flags from SA packing (pack, 200 CPU s) instead of the random scan (76)",
    "code": "/home/user/degree-diameter/research/squads/d14D7-r2/c13/run_c13.sh",
    "command": "cd /home/user/degree-diameter/research/cell147/units && ./pack ../data/gh_11.txt 200 1 /home/user/degree-diameter/research/squads/d14D7-r2/c13/c13_packA_s1.flags && CHECKONLY=1 ./pack ../data/gh_11.txt 0 1 /dev/null /home/user/degree-diameter/research/squads/d14D7-r2/c13/c13_packA_s1.flags && /home/user/degree-diameter/research/squads/d14D7-r2/c13/final13.sh c13_pA /home/user/degree-diameter/research/squads/d14D7-r2/c13/c13_packA_s1.flags 1",
    "score": 1063098,
    "unit": "vertices n = 2*177156*3 + 2*81 (81 type-2 units); QUICK check only (unit endpoints and new vertices, pairs beyond D = 0); no all-pairs check",
    "valid": True,
    "next": "Refine with a longer SA (the 200 s run was still improving) or GROW seeds; a cold warm-start (T0 0.05) from these 81 flags gave no gain. Model: flagged points pairwise non-collinear; distance-4 pairs need one endpoint flag line on their path (dually for lines).",
}
line = json.dumps(rec, ensure_ascii=False)
assert "\n" not in line
with open("/home/user/degree-diameter/research/squads/d14D7-r2/scoreboard.jsonl", "a") as f:
    f.write(line + "\n")
print(line)
