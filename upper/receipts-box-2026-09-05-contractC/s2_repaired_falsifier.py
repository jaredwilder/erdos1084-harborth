# Falsifier for the REPAIRED S2: strict same-side as a positive PRODUCT.
import math, random
def cross(a,b,c): return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
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
random.seed(101)
tested=0; bad=0; ex=[]
for _ in range(400000):
    P=[(random.uniform(-3,3),random.uniform(-3,3)) for _ in range(4)]
    v,X,Y,Z=P
    if cross(Y,X,v)*cross(Y,X,Z) <= 0: continue
    if cross(Y,Z,v)*cross(Y,Z,X) <= 0: continue
    tested+=1
    if not inside_angle(Y,X,Z,v):
        bad+=1
        if len(ex)<3: ex.append((v,X,Y,Z))
print("configs satisfying the REPAIRED strict same-side hypotheses:", tested)
print("of those, InsideAngleAt FAILURES:", bad)
for e in ex: print("  ", [tuple(round(c,3) for c in q) for q in e])
