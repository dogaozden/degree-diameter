# Resumable GAP isomorphism tests for the invariant-matched pairs (runs/pairs.json). Each call tests about 12 pending
# pairs with GAP (timeout 85 s); results accumulate in runs/iso_results.txt ("ISO key rep" / "NONISO key rep").
import json, os, subprocess, glob
R = '/home/user/degree-diameter/research/squads/deep-49/r1/c2/runs'
pairs = json.load(open(R + '/pairs.json'))
res_file = R + '/iso_results.txt'
done = {}
if os.path.exists(res_file):
    for l in open(res_file):
        p = l.split()
        if len(p) == 3: done[p[2]] = (p[0], p[1])
pending = [p for p in pairs if p[4] not in done][:12]
if pending:
    lst = ",".join('[%d,%d,%d,"%s",%d,%d,%d,"%s"]' % (p[1], p[2], p[3], p[0], p[5], p[6], p[7], p[4]) for p in pending)
    g = f'''SetPrintFormattingStatus("*stdout*", false);
mk := function(m,k,r)
  local F, G;
  F := FreeGroup("a","b");
  G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
  return Image(IsomorphismPcGroup(G));
end;
L := [{lst}];
for x in L do
  G1 := mk(x[1],x[2],x[3]); G2 := mk(x[5],x[6],x[7]);
  if Size(G1) = Size(G2) and IsomorphismGroups(G1,G2) <> fail then Print("ISO ", x[4], " ", x[8], "\\n");
  else Print("NONISO ", x[4], " ", x[8], "\\n"); fi;
od;
QUIT;
'''
    open(R + '/iso_batch.g', 'w').write(g)
    out = subprocess.run(['nice', '-n', '10', 'gap', '-q', '--quitonbreak', R + '/iso_batch.g'], stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=85).stdout
    with open(res_file, 'a') as f:
        for l in out.splitlines():
            if l.startswith('ISO ') or l.startswith('NONISO '):
                f.write(l + "\n")
    done = {}
    for l in open(res_file):
        p = l.split()
        if len(p) == 3: done[p[2]] = (p[0], p[1])
left = [p for p in pairs if p[4] not in done]
print('pairs', len(pairs), 'decided', len(done), 'pending', len(left))
