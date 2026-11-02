import glob,re,os,json
DIR='/home/user/degree-diameter/research/squads/beyond15/r1/c05/runs'
rows={}
for f in sorted(glob.glob(DIR+'/d*_k*_s*.log')):
    b=os.path.basename(f)[:-4]
    m=re.match(r'd(\d+)D(\d+)_k(\d+)_s(\d+)',b)
    if not m: continue
    txt=open(f).read()
    st=re.search(r'start cost=(\d+)',txt); res=re.search(r'best=(\d+) evals=(\d+)',txt)
    rows.setdefault((int(m[1]),int(m[2]),int(m[3])),{})[int(m[4])]=(int(st[1]) if st else None, int(res[1]) if res else None, int(res[2]) if res else None)
for key in sorted(rows):
    print(key, rows[key])
