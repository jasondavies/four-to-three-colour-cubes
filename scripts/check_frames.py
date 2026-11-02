#!/usr/bin/env python3
"""Finite geometric checks for the frame extension (not a proof for all sizes)."""
from collections import Counter
from itertools import combinations, permutations, product
from check_three_colour_threshold import canonical, corner_types, match, require

EDGES = [(f,g) for f,g in combinations(range(6),2) if f//2 != g//2]
def edges(c): return [tuple(sorted((c[f], c[g]))) for f,g in EDGES]
def cyc(t): return min(t,t[1:]+t[:1],t[2:]+t[:2])

def main():
    sources=sorted({canonical(c) for c in product(range(4),repeat=6) if len(set(c))==4})
    targets=sorted({canonical(c) for c in product(range(4),repeat=6) if len(set(c))==3})
    cs=[set(corner_types(c)) for c in sources]
    es=[set(edges(c)) for c in sources]
    minimal=[i for i,c in enumerate(cs) if not any(d<c for d in cs)]
    reduction=[i if i in minimal else next(j for j in minimal if cs[j]<=c) for i,c in enumerate(cs)]
    plus={(0,1,2),(0,3,1),(0,2,3),(1,3,2)}
    bichrom=set(combinations(range(4),2))
    tclasses=[[],[]]
    for i in minimal:
        mono={a for a in range(4) if any(k.count(a)>=2 for k in cs[i])}
        if mono:
            require(bichrom<=es[i],f'Ordinary edge availability {i}')
            require(all((a,a) in es[i] for a in mono),'Bucket monochromatic edge')
            if max(Counter(sources[i]).values())==3:
                s=0 if {t for t in cs[i] if len(set(t))==3}==plus else 1
                tclasses[s].append(i)
        else:
            single=tuple(a for a in range(4) if sources[i].count(a)==1)
            require(es[i]==bichrom-{single},f'Checkerboard missing pair {i}')
    require([len(c) for c in tclasses]==[4,4],'T classes')
    require(all(es[j]<=es[i] for i,j in enumerate(reduction)),'Reduction preserves edges')
    for a,b,c in permutations(range(4),3):
        u=(a,b,a,b,a,c)
        require(Counter(corner_types(u))==Counter(map(cyc,[(a,a,a),(a,a,b),(a,a,b),(a,a,c),(a,b,b),(b,b,c),(a,b,c),(a,c,b)])),'U corners')
        require(Counter(edges(u))==Counter({(a,a):3,(b,b):1,tuple(sorted((a,b))):4,tuple(sorted((a,c))):2,tuple(sorted((b,c))):2}),'U edges')
    # Check actual matching, including repeated edge occurrences, against all targets.
    corner_adj=[[[i for i in range(68) if t in cs[i]] for t in corner_types(c)] for c in targets]
    edge_adj=[[[i for i in range(68) if e in es[i]] for e in edges(c)] for c in targets]
    for n in range(2,7):
        adj=[cc+[pool for pool in ee for _ in range(n-2)] for cc,ee in zip(corner_adj,edge_adj)]
        for group in tclasses:
            counts=[4*n-1 if i in group else 0 for i in range(68)]
            require(not any(match(slots,counts) for slots in adj),f'Extremal n={n}')
            for i in range(68):
                counts[i]+=1
                require(any(match(slots,counts) for slots in adj),f'Positive control n={n}, added={i}')
                counts[i]-=1
        print(f'n={n}: both obstructions and all 136 one-cube extensions checked',flush=True)
    print('Frame edge facts, reduction, and all U multisets agree.')
if __name__=='__main__': main()
