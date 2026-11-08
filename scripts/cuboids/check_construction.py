#!/usr/bin/env python3
"""Independent physical-rotation audits and constructive controls.
No inventory search or finite sample is used as an upper-bound proof.
"""
import json,random
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from collections import Counter
from construct import SOURCES,MINIMAL,TYPES,CS,ES,threshold,construct,matching,corners,cyclic


def parity(p):return (-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
ROT=[]
for p in permutations(range(3)):
    for signs in product((1,-1),repeat=3):
        if parity(p)*signs[0]*signs[1]*signs[2]!=1:continue
        ROT.append(tuple(2*p[i]+(bit if signs[i]>0 else 1-bit) for i in range(3) for bit in range(2)))
assert len(set(ROT))==24
CORNERS=[tuple(2*i+s[i] for i in range(3)) for s in product((0,1),repeat=3)]
EDGES=[(i,j) for i,j in combinations(range(6),2) if i//2!=j//2]
AXIS=[next(k for k in range(3) if k not in (i//2,j//2)) for i,j in EDGES]
FACES=CORNERS+EDGES

@lru_cache(None)
def masks(t):
    return [sum(1<<i for i,s in enumerate(SOURCES) if any(all(s[r[f]]==t[f] for f in fs) for r in ROT)) for fs in FACES]

def solves(t,shape,x):
    return matching(x,[1]*8+[shape[k]-2 for k in AXIS],masks(t))

def random_composition(n,k,rng):
    if k==1:return [n]
    cuts=sorted(rng.sample(range(n+k-1),k-1));out=[];last=-1
    for c in cuts+[n+k-1]:out.append(c-last-1);last=c
    return out

def main():
    rng=random.Random(20261106);branches=Counter();tested=0;covered_shapes=set()
    def check(shape,x):
        nonlocal tested
        t,k=construct(shape,x)
        assert solves(t,shape,x),(shape,t,k,x)
        branches[k]+=1;tested+=1;covered_shapes.add(tuple(shape))
    shapes=list(combinations_with_replacement(range(2,13),3))+[(2,4,100),(3,3,100),(3,40,100),(10,10,100),(30,30,30),(100,100,100)]
    for shape in shapes:
        N=threshold(*shape)
        for _ in range(6):
            x=[0]*68
            support=rng.sample(MINIMAL,rng.randint(1,38))
            for i,n in zip(support,random_composition(N,len(support),rng)):x[i]=n
            check(shape,x)
        # Original unreduced physical varieties too.
        x=[0]*68
        for _ in range(N):x[rng.randrange(68)]+=1
        check(shape,x)
        # Checkerboard-only distributions exercise the weighted selection.
        ids=[i for i in MINIMAL if TYPES[i][0]=='C']
        for _ in range(6):
            x=[0]*68
            for i,n in zip(ids,random_composition(N,6,rng)):x[i]=n
            check(shape,x)
    # Force no-D/no-Q inputs by capping each majority bucket, and populate
    # the otherwise rare H branch with varied P cubes and minority types.
    forced=Counter()
    for shape in combinations_with_replacement(range(2,13),3):
        a,b,c=shape;N=threshold(*shape);h=4*a-1
        if N>16*a+2:continue
        for _ in range(180):
            x=[0]*68;slots=[h]*4
            # One to six checkerboards or minority ordinary cubes.
            eligible=[i for i in MINIMAL if TYPES[i][0]=='C' or TYPES[i][1]==1]
            for _ in range(rng.randint(1,6)):x[rng.choice(eligible)]+=1
            for _ in range(N-sum(x)):
                ids=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==0 and all(slots[j] for j in TYPES[i][2])]
                if not ids:break
                # Bias toward T, but use all twelve P varieties as well.
                weights=[8 if TYPES[i][3] else 1 for i in ids]
                i=rng.choices(ids,weights=weights)[0];x[i]+=1
                for j in TYPES[i][2]:slots[j]-=1
            if sum(x)==N:
                t,k=construct(shape,x);forced[k]+=1;check(shape,x)
    # Saturated buckets exercise the narrow no-D/no-Q boundary deliberately.
    explicit=[]
    tid={u:next(i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==0 and TYPES[i][3] and u in TYPES[i][2]) for u in range(4)}
    pid={e:next(i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==0 and not TYPES[i][3] and TYPES[i][2]==set(e)) for e in combinations(range(4),2)}
    cid={e:next(i for i in MINIMAL if TYPES[i]==('C',e)) for e in combinations(range(4),2)}
    for a in range(2,13):
        h=4*a-1;x=[0]*68
        for u,n in enumerate([h,h-2,h-4,h-4]):x[tid[u]]=n
        for e,n in [((1,2),1),((1,3),1),((2,3),3)]:x[pid[e]]=n
        x[cid[0,1]]=3;x[cid[2,3]]=3
        for b in range(a,2*a+3):
            for c in range(b,3*a+5-b):
                shape=(a,b,c)
                if threshold(*shape)==sum(x):
                    t,k=construct(shape,x);assert k.startswith('H');check(shape,x)
                    explicit.append({'shape':shape,'branch':k})
    for shape in [(2,4,4),(2,4,5)]:
        x=[0]*68
        for u,n in enumerate([7,7,3,3]):x[tid[u]]=n
        x[pid[2,3]]=4;x[cid[0,1]]=2;x[cid[2,3]]=3
        t,k=construct(shape,x);assert k=='H-short';check(shape,x)
        explicit.append({'shape':shape,'two_high_colours':True,'branch':k})
    # The former strip proof's second H orientation is unnecessary: stress
    # the two-high-colour boundary with t=(7,7,2,2), P total five.
    for b in (2,3):
        for c in range(max(b,2),7):
            x=[0]*68
            for u,n in enumerate([7,7,2,2]):x[tid[u]]=n
            x[pid[2,3]]=5;x[cid[0,1]]=3;x[cid[2,3]]=3
            t,k=construct((2,b,c),x);assert k=='H-short';check((2,b,c),x)
            explicit.append({'shape':(2,b,c),'two_high_colours':True,'branch':k})
    # Exhaustive geometry for the directional Q and H demands.
    directional=0
    for u,v,w in permutations(range(4),3):
        for label,t,expected in [
            ('Q',(v,w,u,u,u,u),[Counter({(u,u):4}),Counter({tuple(sorted((u,v))):2,tuple(sorted((u,w))):2}),Counter({tuple(sorted((u,v))):2,tuple(sorted((u,w))):2})]),
            ('H',(v,w,u,u,u,v),[Counter({(u,u):2,tuple(sorted((u,v))):2}),Counter({(v,v):1,tuple(sorted((u,v))):1,tuple(sorted((u,w))):1,tuple(sorted((v,w))):1}),Counter({tuple(sorted((u,v))):2,tuple(sorted((u,w))):2})])]:
            actual=[Counter(tuple(sorted((t[i],t[j]))) for (i,j),ax in zip(EDGES,AXIS) if ax==k) for k in range(3)]
            assert actual==expected,(label,t,actual,expected)
            masks(t);directional+=1
    # Audit the H reservations themselves, not just successful whole-target
    # matching: every assigned pool must physically fit its designated slot.
    reservation_checks=0
    for u,v,w in permutations(range(4),3):
        target=(v,w,u,u,u,v);codes=corners(target);physical=masks(target)
        for sign in (0,1):
            tu=next(i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==sign and TYPES[i][3] and u in TYPES[i][2])
            tv=next(i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==sign and TYPES[i][3] and v in TYPES[i][2])
            used=Counter()
            for slot,code in enumerate(codes):
                if code in (cyclic((u,u,v)),cyclic((u,u,w))):pool=[tu];used['Tu']+=1
                elif code==cyclic((u,v,v)):pool=[tv];used['Tv']+=1
                elif code in CS[tu]:
                    pool=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==sign];used['majority']+=1
                else:
                    pool=[i for i in MINIMAL if (TYPES[i][0]=='ordinary' and TYPES[i][1]!=sign) or (TYPES[i][0]=='C' and code in CS[i])];used['minority']+=1
                for i in pool:
                    assert physical[slot]>>i&1,(target,sign,slot,i)
                    reservation_checks+=1
            assert used==Counter(Tu=4,Tv=2,majority=1,minority=1)
            for k,(f,g) in enumerate(EDGES):
                if target[f]==target[g]:
                    i=tu if target[f]==u else tv
                    assert physical[k+8]>>i&1
                    reservation_checks+=1
    # Check the three lower-bound mechanisms against every oriented target
    # on representative shapes. Proper rotations preserving each axis suffice
    # to remove duplicate targets without losing axis assignments.
    axis_rot=[r for r in ROT if all(r[i]//2==i//2 for i in range(6))]
    canon=lambda t:min(tuple(t[i] for i in r) for r in axis_rot)
    targets=sorted({canon(t) for t in product(range(4),repeat=6) if len(set(t))==3})
    lower_shapes=[(2,2,2),(2,4,4),(2,4,5),(2,4,6),(2,5,5),(3,3,3),(3,3,8),(3,4,7),(4,4,4),(4,6,6),(5,6,10),(2,4,15)]
    lower_checks=0
    for shape in lower_shapes:
        a,b,c=shape
        ordinary=[0]*68
        for i in MINIMAL:
            if TYPES[i][0]=='ordinary' and TYPES[i][1]==0 and TYPES[i][3]:ordinary[i]=4*a-1
        checker=[0]*68;ids=[i for i in MINIMAL if TYPES[i][0]=='C'];n=(24*c-1)//5-1
        for k in range(n):checker[ids[k%6]]+=1
        for t in targets:
            for x in [ordinary,checker]:
                assert not solves(t,shape,x),(shape,t,x)
                lower_checks+=1
    # Purely arithmetic regimes, including all boundaries in a large grid.
    numeric=0
    for a in range(2,41):
        for b in range(a,81):
            for c in range(b,161):
                N=threshold(a,b,c);L=4*(a+b+c)-16
                sa,sb,sc=N-4*a,N-4*b,N-4*c
                assert sc>=5 and N<=6*sc+5
                assert sb>=7 and sb>=2*b-1 and sa>=4*b-1 and sc>=(4*b-1)//3
                assert (N==L)==(b+c>=3*a+4 and c<=5*(a+b)-19)
                assert N>=4*a+2*b+2*c-5
                if N<=16*a+2:
                    assert b+c<=3*a+4
                    if a>=3:
                        assert 16*a-14>11*a
                        assert 16*a-9>=2*a+b+1
                numeric+=1
    result=dict(status='passed',shapes=len(covered_shapes),initial_shapes=len(shapes),constructive_controls=tested,branches=dict(branches),forced_noQ_controls=dict(forced),explicit_boundary_controls=len(explicit),directional_tables=directional,H_reservation_incidences=reservation_checks,oriented_targets=len(targets),physical_lower_checks=lower_checks,arithmetic_shapes=numeric,scope='Controls and geometry audit, not an exhaustive inventory proof. The upper bound is the written argument. This audit does not execute Lean.')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
