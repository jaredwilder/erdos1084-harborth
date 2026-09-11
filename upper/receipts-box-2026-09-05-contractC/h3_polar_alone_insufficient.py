# Does the SORTED-about-v0 polar data ALONE (no hull) imply InsideAngleAt?  NO.
# And does adding "v0 in the interior of the hull of the listed points" rescue it?  Search.
import math, random
def arg(p,q):   # argument of q-p
    return math.atan2(q[1]-p[1], q[0]-p[0])
def norm_pi(t):
    while t <= -math.pi: t += 2*math.pi
    while t > math.pi: t -= 2*math.pi
    return t
def inside_angle(Y,X,Z,V):
    # V inside angle X-Y-Z ?  equivalently arg(V) between arg(X),arg(Z) on the short side
    aX, aV, aZ = arg(Y,X), arg(Y,V), arg(Y,Z)
    d1 = norm_pi(aV-aX); d2 = norm_pi(aZ-aV); d3 = norm_pi(aZ-aX)
    return (0 <= d1 <= math.pi) and (0 <= d2 <= math.pi) and (0 <= d3 <= math.pi) \
        or (0 >= d1 >= -math.pi) and (0 >= d2 >= -math.pi) and (0 >= d3 >= -math.pi)
def in_hull_interior(V, pts):
    # V strictly inside hull of pts: for the convex polygon, check strict same side of every edge
    import itertools
    n=len(pts)
    # order pts by argument about V (they are, by construction)
    ok=True
    for i in range(n):
        A,B=pts[i],pts[(i+1)%n]
        cr=(B[0]-A[0])*(V[1]-A[1])-(B[1]-A[1])*(V[0]-A[0])
        if cr<=1e-12: ok=False
    return ok
random.seed(11)
bad_nohull=0; bad_withhull=0; trials=0
for _ in range(20000):
    h=random.choice([3,4,5,6])
    args=sorted(random.uniform(0,2*math.pi) for _ in range(h))
    if any(args[i+1]-args[i] > math.pi for i in range(h-1)): continue
    if 2*math.pi-(args[-1]-args[0]) > math.pi: continue
    rad=[random.uniform(0.2,5.0) for _ in range(h)]
    P=[(rad[i]*math.cos(args[i]), rad[i]*math.sin(args[i])) for i in range(h)]
    V=(0.0,0.0)
    trials+=1
    for i in range(h):
        X,Y,Z=P[i%h],P[(i+1)%h],P[(i+2)%h]
        if not inside_angle(Y,X,Z,V):
            bad_nohull+=1
            if in_hull_interior(V,P):
                bad_withhull+=1
                if bad_withhull<=3:
                    print("HULL-INTERIOR COUNTEREXAMPLE", h, [tuple(round(c,3) for c in p) for p in P], "vertex", i+1)
            break
print("configs", trials, "failing InsideAngleAt without hull condition:", bad_nohull,
      "| still failing WITH v0 strictly interior:", bad_withhull)
