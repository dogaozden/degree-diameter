import subprocess,os,time,re
exec(open('rank.py').read().split("print(len(rows)")[0])
keep=[r for r in rows if r[5]<=50 and r[4]<=50 and not r[2]]
keep.sort(key=lambda r:(r[5],r[4],r[0],r[1]))
top=keep[:50]
env=dict(os.environ,OMP_NUM_THREADS='1',THREADS='1')
log=open('screen.log','a')
for N,I,ab,dd,z,q,s in top:
    tab=f't{N}_{I}.bin'
    t0=time.time()
    r=subprocess.run(['timeout','300','nice','-n','10','python3','../../tools/gapgroup.py','table',str(N),str(I),tab],capture_output=True,text=True,env=env)
    if r.returncode!=0:
        log.write(f'{N} {I} TABLEFAIL {r.stderr[-300:]}\n'); log.flush(); continue
    tg=time.time()-t0
    out=subprocess.run(['timeout','40','nice','-n','10','../../tools/haar5','anneal',tab,'7','8','1'],capture_output=True,text=True,env=env).stdout
    m=[l for l in out.splitlines() if l.startswith('RESULT')]
    line=m[-1] if m else 'NORESULT '+out[-200:]
    best=re.search(r'best=(\d+)',line)
    log.write(f'{N} {I} q={q} z={z} {s[:40]!r} tab={tg:.1f}s | {line[:200]}\n'); log.flush()
    os.remove(tab) if False else None
