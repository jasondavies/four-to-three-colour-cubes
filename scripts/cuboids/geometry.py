"""Physical corner/edge geometry for four-to-three cuboid assemblies.
Faces are (+x,-x,+y,-y,+z,-z); rotations are proper quarter turns.
"""
from itertools import product, combinations
from collections import Counter

def rotations():
    found={tuple(range(6))}; pending=list(found)
    while pending:
        p=pending.pop()
        for g in ((0,1,5,4,2,3),(3,2,0,1,4,5)):
            q=tuple(p[i] for i in g)
            if q not in found: found.add(q); pending.append(q)
    assert len(found)==24
    return sorted(found)
ROT=rotations()

def canonical(c,group=ROT):return min(tuple(c[i] for i in r) for r in group)
def cyclic(t):return min(t,t[1:]+t[:1],t[2:]+t[:2])
def corners(c):
    out=[]
    for signs in product((0,1),repeat=3):
        t=tuple(c[2*a+signs[a]] for a in range(3))
        if sum(signs)%2:t=(t[0],t[2],t[1])
        out.append(cyclic(t))
    return out
EDGES=[(i,j) for i,j in combinations(range(6),2) if i//2!=j//2]
def edges(c):return {tuple(sorted((c[i],c[j]))) for i,j in EDGES}
SOURCES=sorted({canonical(c) for c in product(range(4),repeat=6) if len(set(c))==4})
CS=list(map(lambda c:set(corners(c)),SOURCES)); ES=list(map(edges,SOURCES))
MINIMAL=[i for i,cs in enumerate(CS) if not any(ds<cs for ds in CS)]
REDUCTION=[i if i in MINIMAL else next(j for j in MINIMAL if CS[j]<=cs) for i,cs in enumerate(CS)]
assert len(SOURCES)==68 and len(MINIMAL)==38
assert all(ES[j]<=ES[i] for i,j in enumerate(REDUCTION))

PLUS={(0,1,2),(0,3,1),(0,2,3),(1,3,2)}
TYPES={}
for i in MINIMAL:
    tri={k for k in CS[i] if len(set(k))==3}
    bucket={a for a in range(4) if (a,a) in ES[i]}
    if not bucket:
        missing=next(iter(set(combinations(range(4),2))-ES[i]))
        TYPES[i]=('C',missing)
    else:
        assert tri in (PLUS,{cyclic((a,c,b)) for a,b,c in PLUS})
        TYPES[i]=('ordinary',0 if tri==PLUS else 1,bucket,max(Counter(SOURCES[i]).values())==3)

def reduced(counts):
    out=[0]*68
    for i,n in enumerate(counts):out[REDUCTION[i]]+=n
    return out

