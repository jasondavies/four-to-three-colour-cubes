#!/usr/bin/env python3
"""Independent geometry audit: no imports from the construction or generated tables.
Enumerates physical face colourings under determinant-one signed permutations.
This is an audit of established finite geometry, not a replacement for the proof.
"""
from itertools import product, permutations, combinations
from collections import Counter
import json

rots=[]
for p in permutations(range(3)):
    parity=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
    for flips in product((0,1),repeat=3):
        if parity*(-1)**sum(flips)!=1:continue
        rots.append(tuple(2*p[i]+(j^flips[i]) for i in range(3) for j in range(2)))
assert len(set(rots))==24
canon=lambda c:min(tuple(c[r[f]] for f in range(6)) for r in rots)
cyc=lambda t:min(t,t[1:]+t[:1],t[2:]+t[:2])
frames={}
for r in rots:
    fs=(r[0],r[2],r[4]);frames.setdefault(frozenset(fs),fs)
assert len(frames)==8

def corner_counts(c):return Counter(cyc(tuple(c[f] for f in fs)) for fs in frames.values())
def edge_set(c):return {tuple(sorted((c[r[0]],c[r[2]]))) for r in rots}

raw=[c for c in product(range(4),repeat=6) if len(set(c))==4]
sources=sorted(set(map(canon,raw)))
assert len(sources)==68
cs={c:set(corner_counts(c)) for c in sources}
es={c:edge_set(c) for c in sources}
reduced=[c for c in sources if not any(cs[d]<cs[c] for d in sources)]
assert len(reduced)==38
for c in sources:
    for d in reduced:
        if cs[d]<=cs[c]:assert es[d]<=es[c]
    assert any(cs[d]<=cs[c] for d in reduced)

pairs=set(combinations(range(4),2));triples=list(combinations(range(4),3))
ordinary=[];checkers=[];signatures=set();bucket_checks=0
for c in reduced:
    monos={u for u in range(4) if (u,u) in es[c]}
    tri=frozenset(k for k in cs[c] if len(set(k))==3)
    if not monos:
        checkers.append(c);missing=pairs-es[c];assert len(missing)==1
        uv=next(iter(missing))
        assert all(len(set(k))==3 for k in cs[c])
        assert {tuple(sorted(k)) for k in tri}=={t for t in triples if not set(uv)<=set(t)}
        assert all(cyc((u,w,v)) in tri for u,v,w in tri)
        for pq in pairs:
            assert any(set(pq)<=set(k) for k in tri)==(pq!=uv)
    else:
        ordinary.append(c);signatures.add(tri)
        assert pairs<=es[c]
        assert len(tri)==4
        for u,v,w in triples:assert (cyc((u,v,w)) in tri)+(cyc((u,w,v)) in tri)==1
        ct=Counter(c)
        if max(ct.values())==3:
            u=next(u for u,n in ct.items() if n==3)
            assert monos=={u}
            assert all(cyc((u,u,v)) in cs[c] for v in range(4) if v!=u)
        else:assert len(monos)==2
        for u in monos:
            assert sum(cyc((u,u,v)) in cs[c] for v in range(4) if v!=u)>=2
            bucket_checks+=1
assert len(checkers)==6 and len(ordinary)==32 and len(signatures)==2
assert {next(iter(pairs-es[c])) for c in checkers}==pairs
sig0,sig1=signatures
assert sig0.isdisjoint(sig1)
assert sig0|sig1=={cyc(p) for tri in triples for p in permutations(tri)}
for sig in signatures:
    fam=[c for c in ordinary if frozenset(k for k in cs[c] if len(set(k))==3)==sig]
    assert len(fam)==16
    assert sum(max(Counter(c).values())==3 for c in fam)==4
    assert sum(max(Counter(c).values())==2 for c in fam)==12
    assert Counter(next(u for u,n in Counter(c).items() if n==3) for c in fam if max(Counter(c).values())==3)==Counter({u:1 for u in range(4)})

raw_targets=[c for c in product(range(4),repeat=6) if len(set(c))==3]
no_tri=all_tri=balance_checks=0
for t in raw_targets:
    cc=corner_counts(t)
    for u,v,w in triples:
        assert cc[cyc((u,v,w))]==cc[cyc((u,w,v))]
        balance_checks+=1
    if not any(len(set(k))==3 for k in cc):
        no_tri+=1;ct=Counter(t)
        assert sorted(ct.values())==[1,1,4]
        single=[f for f in range(6) if ct[t[f]]==1]
        assert single[0]//2==single[1]//2
    if all(len(set(k))==3 for k in cc):
        all_tri+=1
        assert all(t[2*j]==t[2*j+1] for j in range(3))
        assert sorted(cc.values())==[4,4]

out=dict(status='passed',rotations=24,physical_source_colourings=len(raw),source_varieties=68,reduced_varieties=38,ordinary_classes=2,bucket_incidence_checks=bucket_checks,physical_target_colourings=len(raw_targets),orientation_balance_checks=balance_checks,no_tricoloured_corner_targets=no_tri,all_tricoloured_corner_targets=all_tri,scope='Finite geometry audit independent of the construction; no exhaustive inventory theorem.')
print(json.dumps(out,indent=2))
