"""Constructive investigation of 2 x 3 x c frames; x is the thickness-two axis."""
from itertools import product,permutations,combinations
from collections import Counter
from geometry import SOURCES,MINIMAL,REDUCTION,CS,ES,ROT,canonical,corners,cyclic
from construct import TYPES,reduced,threshold
AXES=[r for r in ROT if all(set(r[2*a:2*a+2])=={2*a,2*a+1} for a in range(3))]
assert len(AXES)==4
TARGETS_STRIP=sorted({canonical(t,AXES) for t in product(range(4),repeat=6) if len(set(t))==3})

def strip_requirements(t,c):
    req=Counter(('corner',k) for k in corners(t))
    for axis,weight in ((1,1),(2,c-2)):
        a,b=[k for k in range(3) if k!=axis]
        for i in (2*a,2*a+1):
            for j in (2*b,2*b+1):
                req['edge',tuple(sorted((t[i],t[j])))]+=weight
    return [(r,n) for r,n in sorted(req.items()) if n]

def strip_target(c,counts):
    assert c>=3 and len(counts)==68 and sum(counts)>=threshold(c)
    x=reduced(counts);N=sum(x);L=4*c+4;s=N-4*c
    assert N>=L and s>=5 and N<=6*s+5
    ordinary=[sum(x[i] for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==j) for j in (0,1)]
    missing={e:sum(x[i] for i in MINIMAL if TYPES[i]==('C',e)) for e in combinations(range(4),2)}
    degree={v:sum(n for e,n in missing.items() if v in e) for v in range(4)}
    A,B=sorted(ordinary,reverse=True)
    good=[v for v in range(4) if A+degree[v]>=4 and B+degree[v]>=4 and A+B+degree[v]>=8]
    if good:
        for v in good:
            for a,b,d in permutations(sorted(set(range(4))-{v})):
                if missing[tuple(sorted((a,b)))]<=s and missing[tuple(sorted((a,d)))]<=N-12:
                    return (a,a,b,b,d,d),'D'
        raise AssertionError('The heavy-edge argument should supply a D orientation')
    majority=0 if ordinary[0]>=ordinary[1] else 1
    assert ordinary[majority]>=N-6 and max(missing.values())<=3
    for a in range(4):
        bucket=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==majority and a in TYPES[i][2]]
        if sum(x[i] for i in bucket)>=8:
            chosen=[]
            for i in bucket:chosen.extend([i]*min(x[i],8-len(chosen)))
            freq={b:sum(cyclic((a,a,b)) in CS[i] for i in chosen) for b in range(4) if b!=a}
            b,d=[b for b in freq if freq[b]>=4][:2]
            return (b,d,a,a,a,a),'Q'
    ts={a:sum(x[i] for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==majority and TYPES[i][3] and a in TYPES[i][2]) for a in range(4)}
    assert sum(ts.values())>=18
    a=max(ts,key=ts.get)
    minority=next(i for i in MINIMAL if x[i] and (TYPES[i][0]=='C' or TYPES[i][1]!=majority))
    minority_tri=[set(k) for k in CS[minority] if len(set(k))==3 and a in k]
    if ts[a]>=6:
        for triple in minority_tri:
            for b in sorted(triple-{a}):
                if ts[b]>=2:
                    d=next(iter(triple-{a,b}))
                    return (a,a,b,d,a,b),'H-aa'
    else:
        assert min(ts.values())>=3 and ts[a]>=4
        triple=minority_tri[0];b,d=sorted(triple-{a})
        return (b,d,a,a,a,b),'H-bb'
    raise AssertionError('The majority counts should supply an H target')

if __name__=='__main__':
    print('Strip target orientations:',len(TARGETS_STRIP))
