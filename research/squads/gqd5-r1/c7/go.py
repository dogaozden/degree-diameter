import sys, json, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c7')
import build
D = '/home/user/degree-diameter/research/squads/gqd5-r1/c7/'
O1 = json.load(open(D + 'O1.json'))
P18 = json.load(open(D + 'P18.json'))
P18b = json.load(open(D + 'W18_s5.json'))
out = sys.argv[1]; seed = int(sys.argv[2])
print(build.run(seed, out, O_a=O1, O_b=O1, P_a=P18, P_b=P18b))
