import subprocess, sys, os
G='/home/user/degree-diameter/research/squads/cells/d10D8_work/glift'
m=int(sys.argv[1]); seeds=int(sys.argv[2])
best=None
for s in range(seeds):
    fn=f'work/s3_{m}.txt'
    subprocess.run(['python3','-I','gen_dual.py','3','dual3.phi',str(m),str(s),fn,'bil'],check=True)
    r=subprocess.run(['timeout','900','nice','-n','10',G,fn,'all'],capture_output=True,text=True)
    cost=int(r.stdout.split()[1])
    if best is None or cost<best[0]: best=(cost,s)
    if cost==0: print('FOUND seed',s,flush=True); break
print('m',m,'best cost',best,flush=True)
