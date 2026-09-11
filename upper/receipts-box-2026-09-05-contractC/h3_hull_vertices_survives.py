# H3, honestly tested: hull VERTICES only, v0 strictly interior, listing sorted by
# argument about v0.  Does InsideAngleAt hold at every vertex?
import math, random
def arg(p,q): return math.atan2(q[1]-p[1], q[0]-p[0])
def norm_pi(t):
    while t <= -math.pi: t += 2*math.pi
    while t > math.pi: t -= 2*math.pi
    return t
def inside_angle(Y,X,Z,V):
    aX,aV,aZ = arg(Y,X),arg(Y,V),arg(Y,Z)
    d1,d2,d3 = norm_pi(aV-aX), norm_pi(aZ-aV), norm_pi(aZ-aX)
    pos = (0 <= d1 <= math.pi) and (0 <= d2 <= math.pi) and (0 <= d3 <= math.pi)
    neg = (0 >= d1 >= -math.pi) and (0 >= d2 >= -math.pi) and (0 >= d3 >= -math.pi)
    return pos or neg
def hull(pts):
    pts=sorted(set(pts))
    if len(pts)<3: return pts
    def half(ps):
        out=[]
        for p in ps:
            while len(out)>=2 and (out[-1][0]-out[-2][0])*(p[1]-out[-2][1])-(out[-1][1]-out[-2][1])*(p[0]-out[-2][0])<=0:
                out.pop()
            out.append(p)
        return out
    lo=half(pts); up=half(pts[::-1])
    return lo[:-1]+up[:-1]
random.seed(23)
bad=0; trials=0; badex=[]
for _ in range(30000):
    n=random.choice([3,4,5,6,7,8])
    pts=[(random.uniform(-5,5),random.uniform(-5,5)) for _ in range(n)]
    H=hull(pts)
    if len(H)<3: continue
    cx=sum(p[0] for p in H)/len(H); cy=sum(p[1] for p in H)/len(H)
    V=(cx,cy)
    P=sorted(H,key=lambda q: arg(V,q))
    h=len(P)
    gaps=[]
    ok=True
    for i in range(h):
        a1=arg(V,P[i]); a2=arg(V,P[(i+1)%h])
        d=(a2-a1)%(2*math.pi)
        if d>=math.pi-1e-12: ok=False
        gaps.append(d)
    if not ok: continue          # H2 guarantees every central gap < pi
    trials+=1
    for i in range(h):
        X,Y,Z=P[i%h],P[(i+1)%h],P[(i+2)%h]
        if not inside_angle(Y,X,Z,V):
            bad+=1; badex.append((h,P,i+1)); break
print("configs tested", trials, "InsideAngleAt FAILURES", bad)
for b in badex[:3]:
    print("  h=",b[0],"vertex",b[2],[tuple(round(c,3) for c in p) for p in b[1]])
