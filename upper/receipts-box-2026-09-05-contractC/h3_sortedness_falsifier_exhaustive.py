import itertools, math
def ang(a,b):
    d=abs(a-b)%(2*math.pi)
    return min(d,2*math.pi-d)
found=[]
for h in range(4,9):
    base=[2*math.pi*k/h for k in range(h)]
    for perm in itertools.permutations(range(1,h)):
        order=(0,)+perm
        gaps=[ang(base[order[i]],base[order[(i+1)%h]]) for i in range(h)]
        if all(g < math.pi - 1e-9 for g in gaps) and abs(sum(gaps)-2*math.pi) < 1e-9:
            if list(order)!=list(range(h)) and list(order)!=[0]+list(range(h-1,0,-1)):
                found.append((h,order,[round(g,4) for g in gaps]))
    print("h=",h,"scrambled hits so far:",len(found))
for f in found[:10]:
    print(f)
