"""Physical corner/edge geometry for the 4-to-3 thin-cuboid investigation.
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
AXIAL=[r for r in ROT if set(r[4:])=={4,5}]
assert len(AXIAL)==8

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
def long_edges(c):return [tuple(sorted((c[i],c[j]))) for i in (0,1) for j in (2,3)]
SOURCES=sorted({canonical(c) for c in product(range(4),repeat=6) if len(set(c))==4})
CS=list(map(lambda c:set(corners(c)),SOURCES)); ES=list(map(edges,SOURCES))
MINIMAL=[i for i,cs in enumerate(CS) if not any(ds<cs for ds in CS)]
REDUCTION=[i if i in MINIMAL else next(j for j in MINIMAL if CS[j]<=cs) for i,cs in enumerate(CS)]
assert len(SOURCES)==68 and len(MINIMAL)==38
assert all(ES[j]<=ES[i] for i,j in enumerate(REDUCTION))
TARGETS=sorted({canonical(c,AXIAL) for c in product(range(4),repeat=6) if len(set(c))==3})
def family(t):
    ct=Counter(t)
    if sorted(ct.values())==[1,1,4]:
        a=ct.most_common(1)[0][0];f,g=[i for i,x in enumerate(t) if x!=a]
        return 'Q' if f//2==g//2 else 'R'
    if all(t[2*i]==t[2*i+1] for i in range(3)):return 'D'
    return 'other'

def requirements(t,c):
    req=Counter(('corner',k) for k in corners(t))
    for e in long_edges(t):req[('edge',e)]+=c-2
    return [(k,d) for k,d in sorted(req.items()) if d]

def neighbours(req,indices=MINIMAL):
    kind,key=req
    sets=CS if kind=='corner' else ES
    return sum(1<<j for j,i in enumerate(indices) if key in sets[i])

def hall_options(t,c,indices=MINIMAL):
    # Identical source neighbourhoods can be merged; a maximal deficient
    # set takes every demand position with each selected neighbourhood.
    grouped=Counter()
    for req,d in requirements(t,c):grouped[neighbours(req,indices)]+=d
    ns=list(grouped);ds=[grouped[n] for n in ns]
    unions=[0]*(1<<len(ns));demands=[0]*len(unions);best={}
    for s in range(1,len(unions)):
        bit=s&-s;j=bit.bit_length()-1
        unions[s]=unions[s^bit]|ns[j];demands[s]=demands[s^bit]+ds[j]
        n=unions[s];r=demands[s]-1
        if r>best.get(n,-1):best[n]=r
    # Deficiency is a disjunction. Keep only its weakest inequalities.
    return [(n,r) for n,r in best.items() if not any(m!=n and m&~n==0 and q>=r for m,q in best.items())]

def matches(t,c,counts,indices=MINIMAL):
    pool=[i for i,n in zip(indices,counts) for _ in range(n)]
    req=[r for r,d in requirements(t,c) for _ in range(d)]
    ns=sorted(([j for j,i in enumerate(pool) if r[1] in (CS if r[0]=='corner' else ES)[i]] for r in req),key=len)
    owner=[-1]*len(pool)
    def aug(k,seen):
        for j in ns[k]:
            if j in seen:continue
            seen.add(j)
            if owner[j]<0 or aug(owner[j],seen):owner[j]=k;return True
        return False
    return all(aug(k,set()) for k in range(len(ns)))

if __name__=='__main__':
    print('sources',len(SOURCES),'reduced',len(MINIMAL),'axial targets',len(TARGETS),Counter(map(family,TARGETS)))
