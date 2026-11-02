#!/usr/bin/env python3
"""Generate finite geometry for kernel-checked three-colour proofs."""
from collections import Counter
from itertools import product
from pathlib import Path
from cube_geometry import canonical, corners, ROT

OUT = Path(__file__).resolve().parents[1] / 'ThreeColour'
OUT.mkdir(exist_ok=True)
sources = sorted({canonical(c) for c in product(range(4), repeat=6) if len(set(c)) == 4})
targets = sorted({canonical(c) for c in product(range(4), repeat=6) if len(set(c)) == 3})
cs = [set(corners(c)) for c in sources]
minimal = [i for i,c in enumerate(cs) if not any(d < c for d in cs)]
reduce = [i if i in minimal else next(j for j in minimal if cs[j] <= c)
          for i,c in enumerate(cs)]
plus = {(0,1,2),(0,3,1),(0,2,3),(1,3,2)}
typ, orient, buckets, third, repeated = [], [], [], [], []
for i in reduce:
    c = sources[i]
    mono = {a for a in range(4) if any(k.count(a) >= 2 for k in cs[i])}
    kind = 'C' if not mono else 'T' if max(Counter(c).values()) == 3 else 'P'
    typ.append(kind); buckets.append(mono)
    orient.append(0 if {k for k in cs[i] if len(set(k)) == 3} == plus else 1)
    repeated.append(tuple(a for a in range(4) if c.count(a) == 2))
    third.append({(a,b) for a in mono for b in range(4) if b != a and
                  min((a,a,b),(a,b,a),(b,a,a)) in cs[i]})
checks = [i for i in minimal if typ[i] == 'C']
G = {}
G['triple'] = [{i for i in range(68) if typ[i] == 'T' and a in buckets[i]} for a in range(4)]
G['pair'] = [{i for i in range(68) if typ[i] == 'P' and a in buckets[i]} for a in range(4)]
G['bucket'] = [G['triple'][a] | G['pair'][a] for a in range(4)]
G['ordinary'] = [{i for i in range(68) if typ[i] != 'C' and orient[i] == s} for s in range(2)]
G['checker'] = [{i for i in range(68) if reduce[i] == j} for j in checks]
G['eligible'] = [{i for i in range(68) if typ[i] == 'C' and d not in repeated[i]} for d in range(4)]
G['support'] = [[{i for i in range(68) if (a,b) in third[i]} for b in range(4)] for a in range(4)]
G['pairSupport'] = [[{i for i in range(68) if typ[i] == 'P' and (a,b) in third[i]} for b in range(4)] for a in range(4)]
G['tripleClass'] = [[G['triple'][a] & G['ordinary'][s] for s in range(2)] for a in range(4)]

def vec(xs): return '![' + ', '.join(xs) + ']'
def group(xs): return '{' + ', '.join(map(str, sorted(xs))) + '}' if xs else '∅'
def nested(xs): return vec([group(x) if isinstance(x, set) else nested(x) for x in xs])
def code(k): return 16*k[0]+4*k[1]+k[2]
def array_fun(xs, ty): return 'fun i => (#['+', '.join(xs)+'] : Array ('+ty+'))[i.val]!'
lines = ['import ThreeColour.Core',
         """/-! Finite geometry and reduced source pools.

`sourceFaces`, `sourceCorners`, and `fits` describe the original 68 varieties.
The pools `triple`, `pair`, `checker`, `ordinary`, `support`, and `eligible`
are preimages under the chosen corner-containment reduction to 38 minimal
varieties. In particular, `allCheckers` has 36 original varieties mapping to
six checkerboards; it is not the set of six geometric checkerboards itself.
The three pools `allTriples`, `allPairs`, `allCheckers` have sizes 8, 24, 36.
Construction certificates use the original `fits`, so their geometry is
checked for every member of each preimage pool.

`omitted j` is the pair of singleton colours of reduced checkerboard `j`.
`eligible d` comprises the checkerboard preimages supporting the three-colour
palette that omits `d`. Target lookups are used with their distinct-colour
hypotheses; entries for invalid parameter combinations are placeholders.
-/""", 'namespace ThreeColour',
         'abbrev Colour := Fin 4', 'abbrev Target := Fin 120',
         'def sourceFaces : Source → Fin 6 → Colour := '+array_fun([vec(list(map(str,c))) for c in sources], 'Fin 6 → Colour'),
         'def targetFaces : Target → Fin 6 → Colour := '+array_fun([vec(list(map(str,c))) for c in targets], 'Fin 6 → Colour'),
         'def sourceCorners : Source → Finset (Fin 64) := '+array_fun([group({code(k) for k in x}) for x in cs], 'Finset (Fin 64)'),
         'def targetCorner : Target → Slot → Fin 64 := '+array_fun([vec([str(code(k)) for k in corners(c)]) for c in targets], 'Slot → Fin 64'),
         'def fits (t : Target) (k : Slot) (i : Source) : Bool := decide (targetCorner t k ∈ sourceCorners i)',
         'def Solvable (a : Inventory) : Prop := ∃ t : Target, Builds a (fits t)',
         'def total (a : Inventory) : ℕ := mass a Finset.univ']
for name, xs in G.items():
    shape = f'Fin {len(xs)} → '
    if isinstance(xs[0], list): shape += f'Fin {len(xs[0])} → '
    lines.append(f'def {name} : {shape}SourceSet := '+nested(xs))
for name, tag in [('allTriples','T'),('allPairs','P'),('allCheckers','C')]:
    lines.append(f'def {name} : SourceSet := '+group({i for i in range(68) if typ[i] == tag}))
q, r = [], []
for a in range(4):
    qq, rr = [], []
    for b in range(4):
        qqq, rrr = [], []
        for c in range(4):
            if len({a,b,c}) < 3: qqq.append('0'); rrr.append('0')
            else:
                qqq.append(str(targets.index(canonical((b,c,a,a,a,a)))))
                rrr.append(str(targets.index(canonical((b,a,c,a,a,a)))))
        qq.append(vec(qqq)); rr.append(vec(rrr))
    q.append(vec(qq)); r.append(vec(rr))
lines += ['def qTarget : Colour → Colour → Colour → Target := '+vec(q),
          'def rTarget : Colour → Colour → Colour → Target := '+vec(r),
          'def oppositeTarget : Colour → Target := '+vec([str(targets.index(canonical(tuple(x for a in range(4) if a != d for x in (a,a))))) for d in range(4)]),
          'def omitted : Fin 6 → Finset Colour := '+vec([group(set(range(4))-set(repeated[i])) for i in checks]),
          'end ThreeColour']
(OUT/'Data.lean').write_text('\n\n'.join(lines)+'\n')
print('Generated', OUT/'Data.lean')

# Lower-bound fixtures: selected Hall-deficient slot sets, checked in Lean.
winners = [[7 if typ[i]=='T' and orient[i]==s else 0 for i in range(68)] for s in range(2)]
bad=[]
for x in winners:
    row=[]
    for target in targets:
        tc=corners(target)
        for bits in range(1,256):
            demand={tc[k] for k in range(8) if bits>>k&1}
            capacity=sum(x[i] for i in range(68) if cs[i]&demand)
            if capacity<bits.bit_count():
                row.append(group({k for k in range(8) if bits>>k&1}));break
        else: raise ValueError('Lower example unexpectedly builds target')
    bad.append(array_fun(row,'Finset Slot'))
(OUT/'LowerData.lean').write_text('\n'.join([
    'import ThreeColour.Data','namespace ThreeColour',
    'def extremal : Fin 2 → Inventory := '+vec([array_fun(list(map(str,x)),'ℕ') for x in winners]),
    'def deficientSlots : Fin 2 → Target → Finset Slot := '+vec(bad),
    'end ThreeColour','']))

(OUT/'PhysicalDefs.lean').write_text('''import ThreeColour.Data
import ColourCubes.Physical
namespace ThreeColour
def FaceFits (t : Target) (i : Source) (k : Slot) (r : Fin 24) : Prop :=
  ∀ f : Fin 3, sourceFaces i (ColourCubes.rotations r (ColourCubes.exposedFaces k f)) =
    targetFaces t (ColourCubes.exposedFaces k f)
instance (t : Target) (i : Source) (k : Slot) (r : Fin 24) : Decidable (FaceFits t i k r) := by
  unfold FaceFits; infer_instance
def PhysicalSolvable (x : Inventory) : Prop :=
  ∃ t : Target, ∃ f : Slot ↪ Stock x, ∀ k, ∃ r : Fin 24, FaceFits t (f k).1 k r
end ThreeColour
''')
raw_source=[]; raw_target=[]; raw_rotation=[]
for n in range(4096):
    c=tuple((n//4**f)%4 for f in range(6))
    canon=canonical(c)
    raw_source.append(str(sources.index(canon)) if len(set(c))==4 else '0')
    raw_target.append(str(targets.index(canon)) if len(set(c))==3 else '0')
    raw_rotation.append(str(next(j for j,r in enumerate(ROT) if all(c[f]==canon[r[f]] for f in range(6)))))
(OUT/'RawData.lean').write_text('\n'.join([
    'import ThreeColour.PhysicalDefs','namespace ThreeColour','open scoped BigOperators',
    'abbrev Raw := Fin 4096',
    'def rawFaces (n : Raw) (f : Fin 6) : Colour := ⟨n.val / 4^f.val % 4, Nat.mod_lt _ (by decide)⟩',
    'def encode (c : Fin 6 → Colour) : Raw := Fin.ofNat 4096 (∑ f, (c f).val * 4^f.val)',
    'def sourceIndex : Raw → Source := '+array_fun(raw_source,'Source'),
    'def targetIndex : Raw → Target := '+array_fun(raw_target,'Target'),
    'def rawRotation : Raw → Fin 24 := '+array_fun(raw_rotation,'Fin 24'),
    'def Uses (n : ℕ) (c : Fin 6 → Colour) : Prop := ColourCubes.Uses n c',
    'instance (n : ℕ) (c : Fin 6 → Colour) : Decidable (Uses n c) := by unfold Uses; infer_instance',
    'end ThreeColour','']))

reflection=[]; reflection_rot=[]
for c in sources:
    reflected=(c[1],c[0],*c[2:])
    can=canonical(reflected)
    reflection.append(str(sources.index(can)))
    reflection_rot.append(str(next(r for r,p in enumerate(ROT) if all(can[p[f]]==reflected[f] for f in range(6)))))
(OUT/'ReflectionData.lean').write_text('\n'.join([
    'import ThreeColour.LowerData','import ColourCubes.Physical','namespace ThreeColour',
    'def reflection : Source → Source := '+array_fun(reflection,'Source'),
    'def reflectionRotation : Source → Fin 24 := '+array_fun(reflection_rot,'Fin 24'),
    'def reflectFace (f : Fin 6) : Fin 6 := if f.val < 2 then ColourCubes.opposite f else f',
    'def reflectInventory (x : Inventory) : Inventory := fun i => x (reflection i)',
    'end ThreeColour','']))

rsingle=[]; rpair=[]; rmajor=[]
for a in range(4):
    rs=[]; rp=[]
    others=[b for b in range(4) if b != a]
    rmajor.append(str(targets.index(canonical((others[0],a,others[1],a,a,a)))))
    for j in checks:
        d=next(d for d in range(4) if d not in repeated[j] and d != a)
        bc=[b for b in range(4) if b not in (a,d)]
        rs.append(str(targets.index(canonical((bc[0],a,bc[1],a,a,a)))))
    for b in range(4):
        rps=[]
        for j in checks:
            ds=[d for d in range(4) if d not in repeated[j] and d not in (a,b)]
            if a==b or not ds: rps.append('0')
            else:
                c=next(c for c in range(4) if c not in (a,b,ds[0]))
                rps.append(str(targets.index(canonical((b,a,c,a,a,a)))))
        rp.append(vec(rps))
    rsingle.append(vec(rs)); rpair.append(vec(rp))
(OUT/'RData.lean').write_text('\n'.join([
    'import ThreeColour.Data', 'namespace ThreeColour',
    'def rSingleTarget : Colour → Fin 6 → Target := '+vec(rsingle),
    'def rPairTarget : Colour → Colour → Fin 6 → Target := '+vec(rpair),
    'def rMajorTarget : Colour → Target := '+vec(rmajor),
    'def flip : Fin 2 → Fin 2 := ![1,0]',
    'def Good (a b : Colour) (j : Fin 6) : Prop := ∃ d ∈ omitted j, d ≠ a ∧ d ≠ b',
    'instance (a b : Colour) (j : Fin 6) : Decidable (Good a b j) := by unfold Good; infer_instance',
    'end ThreeColour','']))

# Export generated definitions through Lean's module system.
for path in OUT.rglob('*.lean'):
    text = path.read_text()
    if text.startswith('module\n'):
        continue
    lines = text.splitlines()
    imports = []
    while lines and (lines[0].startswith('import ') or not lines[0].strip()):
        line = lines.pop(0)
        if line.startswith('import '):
            imports.append('public ' + line)
    path.write_text('module\n\n' + '\n'.join(imports) +
                    '\n\n@[expose] public section\n\n' + '\n'.join(lines) + '\n')
