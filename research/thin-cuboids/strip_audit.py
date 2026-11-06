#!/usr/bin/env python3
"""Audit the proposed 2 x 3 x c strip proof using independently generated physical rotations.

Samples are controls, not a proof of the universal upper bound. Lower
witnesses are tested against every properly oriented target configuration.
"""
from itertools import permutations,product,combinations
from collections import Counter
from functools import lru_cache
from pathlib import Path
import random,json
from geometry import SOURCES,MINIMAL,REDUCTION,CS,ES,TARGETS,corners,cyclic
from construct import threshold,TYPES
from strip import strip_target,strip_requirements,TARGETS_STRIP
TARGETS=TARGETS_STRIP
normals=[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
rot=[]
for p in permutations(range(3)):
    parity=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
    for signs in product((-1,1),repeat=3):
        if parity*signs[0]*signs[1]*signs[2]!=1:continue
        row=[]
        for v in normals:
            w=[0]*3
            for a in range(3):w[p[a]]=signs[a]*v[a]
            row.append(normals.index(tuple(w)))
        rot.append(tuple(row))
assert len(set(rot))==24
corner_faces=[tuple(2*a+s[a] for a in range(3)) for s in product((0,1),repeat=3)]
edge_faces=[(i,j) for i in (0,1) for j in (4,5)]+[(i,j) for i in (0,1) for j in (2,3)]
slots=corner_faces+edge_faces
physical=[{} for _ in slots]
for j,faces in enumerate(slots):
    for i,cube in enumerate(SOURCES):
        for req in {tuple(cube[r[f]] for f in faces) for r in rot}:
            physical[j][req]=physical[j].get(req,0)|(1<<i)
# Independently check every local corner and long-edge compatibility and
# every source reduction directly through the 24 physical rotations.
for t in TARGETS:
    cc=corners(t)
    for j,faces in enumerate(slots):
        req=tuple(t[f] for f in faces);mask=physical[j].get(req,0)
        predicted=sum(1<<i for i in range(68) if (cc[j] in CS[i] if j<8 else tuple(sorted(req)) in ES[i]))
        assert mask==predicted,(t,j)
        for i,k in enumerate(REDUCTION):
            if mask>>k&1:assert mask>>i&1

@lru_cache(None)
def masks(t):return tuple(physical[j].get(tuple(t[f] for f in faces),0) for j,faces in enumerate(slots))
def physical_match(t,c,counts):
    inventory=[i for i,n in enumerate(counts) for _ in range(n)]
    bits=masks(tuple(t))
    demands=list(bits[:12])+[m for m in bits[12:] for _ in range(c-2)]
    ns=sorted(([j for j,s in enumerate(inventory) if m>>s&1] for m in demands),key=len)
    if not ns[0]:return False
    owners=[-1]*len(inventory)
    def aug(k,seen):
        for j in ns[k]:
            if j in seen:continue
            seen.add(j)
            if owners[j]<0 or aug(owners[j],seen):owners[j]=k;return True
        return False
    return all(aug(k,set()) for k in range(len(ns)))

# Audit the three displayed target orientations and demands.
for c in (3,4,7):
    for a,b,d in permutations(range(4),3):
        q=(b,d,a,a,a,a);h1=(a,a,b,d,a,b);h2=(b,d,a,a,a,b)
        assert Counter(corners(q))==Counter({cyclic((a,a,b)):4,cyclic((a,a,d)):4})
        hc=Counter({cyclic((a,a,b)):2,cyclic((a,a,d)):2,cyclic((a,b,b)):2,cyclic((a,b,d)):1,cyclic((a,d,b)):1})
        assert Counter(corners(h1))==Counter(corners(h2))==hc
        e=lambda a,b:('edge',tuple(sorted((a,b))))
        expect=[{e(a,b):2*c-2,e(a,d):2*c-2},
                {e(a,a):2,e(a,b):2*c-2,e(a,d):2*c-4},
                {e(b,b):1,e(a,b):2*c-3,e(a,d):2*c-3,e(b,d):1}]
        for t,edge_demand in zip((q,h1,h2),expect):
            assert dict((r,n) for r,n in strip_requirements(t,c) if r[0]=='edge')==edge_demand

checkers=[i for i in MINIMAL if TYPES[i][0]=='C']
Ts=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==0 and TYPES[i][3]]
P=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==0 and not TYPES[i][3]]
lower28=[7 if i in Ts else 0 for i in range(68)]
assert not any(physical_match(t,3,lower28) for t in TARGETS)
branches=Counter();positives=0
for c in range(3,7):
    for i in range(68):
        x=lower28.copy();x[i]+=1
        t,branch=strip_target(c,x)
        assert physical_match(t,c,x),(c,i,t,branch)
        branches[branch]+=1;positives+=1
# A no-D, no-Q inventory that forces the lower-max-T (H-bb) branch.
special=[0]*68
for i in Ts:
    colour=next(iter(TYPES[i][2]));special[i]=3 if colour==3 else 5
for bucket in ({0,3},{1,3},{2,3},{2,3},{0,1}):
    i=next(i for i in P if TYPES[i][2]==bucket);special[i]+=1
for i in checkers:special[i]+=1
assert sum(special)==29
for c in range(3,7):
    t,branch=strip_target(c,special);assert branch=='H-bb'
    assert physical_match(t,c,special)
    branches[branch]+=1;positives+=1
lower_rows=[]
for c in range(3,21):
    n0=(24*c-6)//5;x=[0]*68
    for j in range(n0):x[checkers[j%6]]+=1
    assert not any(physical_match(t,c,x) for t in TARGETS),c
    lower_rows.append({'length':c,'failing_inventory':n0})
rng=random.Random(20261105)
for c in range(3,21):
    N=threshold(c)
    for k in range(40):
        support=rng.sample(range(68),rng.randint(1,68));x=[0]*68
        for _ in range(N):x[rng.choice(support)]+=1
        t,branch=strip_target(c,x)
        assert physical_match(t,c,x),(c,x,t,branch)
        branches[branch]+=1;positives+=1
    for family in (checkers,[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==0]):
        x=[0]*68
        for j in range(N):x[family[j%len(family)]]+=1
        t,branch=strip_target(c,x);assert physical_match(t,c,x)
        branches[branch]+=1;positives+=1
    for i in checkers:
        x=[0]*68;x[i]=N
        t,branch=strip_target(c,x);assert physical_match(t,c,x)
        branches[branch]+=1;positives+=1
record={'status':'passed','proper_rotations':24,'physical_sources':68,'reduced_sources':38,'oriented_targets':len(TARGETS),
        'local_compatibility_checks':len(TARGETS)*16*68,'positive_inventory_controls':positives,
        'construction_branches':dict(branches),'balanced_checkerboard_lower_controls':lower_rows,
        'thresholds':[{'length':c,'frame_positions':4*c+4,'frame_threshold':threshold(c),'volume':6*c,'complete_threshold':max(29,6*c)} for c in range(3,21)],
        'H_bb_control':[{'faces':SOURCES[i],'count':n} for i,n in enumerate(special) if n],
        'scope':'Independent physical-rotation audit of geometry, displayed obstructions, and constructive controls. The universal upper bound is the written proof; positive controls are not exhaustive. This audit does not execute Lean or establish priority.'}
Path(__file__).with_name('strip-audit-results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
