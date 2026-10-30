import re,sys,glob,os
# summarise haarex2 logs in this folder: order_id | structure | aut | pairs covered | sets | valid | minA
meta = {  # from next_361_380.txt
 '364_1':('C13 x (C7 : C4)',1008),'366_3':('C61 x S3',360),'368_21':('C23 x (C4 : C4)',704),
 '368_26':('C23 x Q16',704),'372_10':('C31 x A4',720),'378_2':('C2 x (C7 : C27)',378),
 '378_16':('S3 x (C7 : C9)',756),'378_24':('C2 x (C7 : (C9 : C3))',756),'378_25':('C2 x (C7 : (C9 : C3))',756),
 '378_33':('C63 x S3',216),'378_46':('C14 x (C9 : C3)',324),'380_1':('C19 x (C5 : C4)',720)}
order = ['378_16','378_24','378_25','372_10','380_1','368_21','368_26','378_2','366_3','378_46','378_33','364_1']
rows=[]
for gid in order:
    o,i = gid.split('_')
    log = f'h{o}_{i}.log'
    if not os.path.exists(log):
        rows.append(f'{gid} | {meta[gid][0]} | {meta[gid][1]} | not run | - | - | -'); continue
    txt = open(log).read()
    m = re.search(r'pair classes=(\d+)', txt); tot = int(m.group(1)) if m else None
    pidx = [int(x) for x in re.findall(r'^PAIR (\d+) ', txt, re.M)]
    last = max(pidx) if pidx else -1
    sets = sum(int(x) for x in re.findall(r'sets=(\d+)', txt))
    valid = len(re.findall(r'^VALID', txt, re.M))
    aside = len(re.findall(r'^ASIDE', txt, re.M))
    mins = [int(x) for x in re.findall(r'minA=(\d+)', txt)]
    minA = min(mins) if mins else None
    d = re.search(r'^DONE .*?sets=(\d+) Acovered=(\d+) valid=(\d+) minA=(\d+)', txt, re.M)
    if d:
        sets, acov, valid, minA = int(d.group(1)), int(d.group(2)), int(d.group(3)), int(d.group(4))
        cov = f'0..{tot} of {tot} (complete)'
        aside = acov
    else:
        cov = f'0..{last} of {tot} (partial, timeout)'
        aside = aside
    rows.append(f'{gid} | {meta[gid][0]} | {meta[gid][1]} | {cov} | {sets} | {valid} (side-A covers {aside}) | {minA}')
print('\n'.join(rows))
