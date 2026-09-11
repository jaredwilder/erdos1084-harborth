import itertools, math, random
def ang(a,b):
    d=abs(a-b)%(2*math.pi)
    return min(d,2*math.pi-d)
random.seed(7)
hits=0; trials=0
for trial in range(4000):
    h=random.choice([4,5,6,7])
    base=sorted(random.uniform(0,2*math.pi) for _ in range(h))
    ok=all(base[i+1]-base[i] > 1e-3 for i in range(h-1))
    if not ok: continue
    trials+=1
    for perm in itertools.permutations(range(1,h)):
        order=(0,)+perm
        gaps=[ang(base[order[i]],base[order[(i+1)%h]]) for i in range(h)]
        if all(g < math.pi - 1e-9 for g in gaps) and abs(sum(gaps)-2*math.pi) < 1e-7:
            if list(order)!=list(range(h)) and list(order)!=[0]+list(range(h-1,0,-1)):
                hits+=1
                if hits<=5:
                    print("COUNTEREXAMPLE h=",h,"order",order)
                    print("  args",[round(x,4) for x in base])
                    print("  gaps",[round(g,4) for g in gaps], "sum",round(sum(gaps),6))
print("trials",trials,"scrambled hits",hits)
