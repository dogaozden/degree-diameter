import sys
path, needle = sys.argv[1], sys.argv[2]
txt = open(path, encoding='utf-8', errors='replace').read()
pages = txt.split('\f')
for pno, pg in enumerate(pages, start=1):
    if needle in pg:
        print(f"{path}: first page containing {needle!r} = PDF page {pno}")
        break
else:
    print(f"{path}: {needle!r} not found")
