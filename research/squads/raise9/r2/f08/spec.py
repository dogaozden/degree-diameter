import sys
# map candidate line "N name p k r" -> haar group spec tokens
def spec(name,p,k,r):
    if name=='sl5': return f"prod sl 5 meta {p} {k} {r}"
    if name.startswith('m'): pass
    return None
