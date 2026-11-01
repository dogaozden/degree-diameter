import subprocess, time, os, json, sys
M='/home/user/degree-diameter/research/squads/raise9/r1/m01'
budget=float(sys.argv[1]) if len(sys.argv)>1 else 95
samples=int(sys.argv[2]) if len(sys.argv)>2 else 10
done=set()
if os.path.exists(f'{M}/results.jsonl'):
    for l in open(f'{M}/results.jsonl'): done.add(json.loads(l)['key'])
t0=time.time()
for line in open(f'{M}/jobs.txt'):
    f=line.split()
    if not f: continue
    k,m,fam,p,n=f[0],f[1],f[2],f[3],f[4]
    key=f'{fam}{p}n{n}_o{k}{m}{f[2] if False else ""}'
    key=f'{fam}_{p}_n{n}_k{f[0]}m{f[1]}f{f[2]}' if False else None
    # job line: k m f fam p n
    k,m,ff,fam,p,n=f[0],f[1],f[2],f[3],f[4],f[5]
    key=f'{fam}_{p}_n{n}_k{k}m{m}f{ff}'
    if key in done: continue
    rem=budget-(time.time()-t0)
    if rem<25: break
    env=dict(os.environ, ORBIT=f'{k} {m} {ff}', RANDORB=str(samples), THREADS='1', UNCDUMP=f'{M}/unc/{key}.txt')
    if os.path.exists(env['UNCDUMP']): os.remove(env['UNCDUMP'])
    cmd=['nice','-n','10',f'{M}/haar_m01','17','9','60','1','1','/dev/null',fam,p,n]
    ts=time.time()
    try:
        r=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=min(100,rem+60))
        out=r.stdout; err=r.stderr; rc=r.returncode
    except subprocess.TimeoutExpired as e:
        out=(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else (e.stdout or ''); err=''; rc='timeout'
    open(f'{M}/logs/{key}.err','w').write(err); open(f'{M}/logs/{key}.out','w').write(out)
    rand=[l for l in out.splitlines() if l.startswith('RANDORB d=')]
    rec={'key':key,'fam':fam,'p':int(p),'n':int(n),'orbit':f'{k} {m} {ff}','rc':rc,'secs':round(time.time()-ts,1),'summary':rand[0] if rand else None}
    with open(f'{M}/results.jsonl','a') as fh: fh.write(json.dumps(rec)+'\n')
    print(key, rec['summary'] or rc, flush=True)
