#!/usr/bin/env python3
"""Draw the obstruction (TikZ and SVG) and README bucket diagram (SVG).

Face tuples are read from `lowerFamily` in the Lean source and checked against
the obstruction fixture. Corner checks support the explanatory panels. Pass a
directory to write elsewhere; `scripts/check-generated.py` compares the outputs.
"""
from collections import Counter
import json
import math
from pathlib import Path
import re
import sys

from cube_geometry import ROT, canonical, require, rotate

ROOT = Path(__file__).resolve().parents[1]
# Okabe-Ito colours: distinguishable with colour-blindness, and dark digits stay
# legible on each. Digits carry the colour identity in greyscale.
COLOURS = ('E69F00', '56B4E9', '009E73', 'F0E442')
# (column, row) -> face index in the order +x,-x,+y,-y,+z,-z. Seen from outside
# with +z up, +y lies to the right of +x. Swapping sides would draw the mirror
# image, which is the other obstruction.
NET = {(1, 0): 4, (0, 1): 3, (1, 1): 0, (2, 1): 2, (3, 1): 1, (1, 2): 5}
COPIES = 7


def obstruction():
    """Return the printed tuples, read from Lean and checked against the fixture."""
    source = (ROOT / 'ThreeColour/Family.lean').read_text(encoding='utf-8')
    block = re.search(r'def lowerFamily.*?\(!\[(.*?)\] :', source, re.S)
    require(block is not None, 'lowerFamily not found')
    tuples = [tuple(map(int, t.split(',')))
              for t in re.findall(r'!\[([0-9,]+)\]', block.group(0))]
    require(len(tuples) == 4 and all(len(t) == 6 for t in tuples), 'Unexpected lowerFamily')
    fixture = json.loads((ROOT / 'data/lower-obstruction.json').read_text(encoding='utf-8'))
    require({(tuple(e['faces']), e['count']) for e in fixture['collection']}
            == {(t, COPIES) for t in tuples}, 'Fixture differs from lowerFamily')
    return tuples


def corner_view(cube):
    """Rotate a cube so its repeated colour occupies the +x,+y,+z corner."""
    colour, multiplicity = Counter(cube).most_common(1)[0]
    require(multiplicity == 3, 'Expected a colour on exactly three faces')
    views = [v for v in (rotate(cube, r) for r in ROT)
             if v[0] == v[2] == v[4] == colour]
    require(views, 'Repeated colour does not occupy a corner')
    view = min(views)
    require(canonical(view) == canonical(cube), 'Rotation changed the variety')
    return view


def word(cube):
    return ''.join(map(str, cube))


# The cyclic order is counterclockwise as viewed from outside the cube.
AVAILABLE = ((0, 1, 2), (0, 3, 1), (0, 2, 3), (1, 3, 2))
MISSING = tuple((a, c, b) for a, b, c in AVAILABLE)


def validate_geometry(cubes):
    """Check the corner claims illustrated in both renderings."""
    from itertools import permutations
    from cube_geometry import corners, cyclic
    for cube in cubes:
        actual = {t for t in corners(cube) if len(set(t)) == 3}
        require(actual == set(AVAILABLE), 'Unexpected trichromatic orientation')
        require(not actual.intersection(cyclic(t) for t in MISSING),
                'An illustrated missing orientation is present')
    require(Counter(corners((0, 0, 1, 1, 2, 2))) ==
            Counter({(0, 1, 2): 4, (0, 2, 1): 4}), 'Unexpected D target corners')
    for a, b, c in permutations(range(4), 3):
        target = corners((a, a, a, a, b, c))
        require(all(t.count(a) == 2 for t in target), 'Unexpected Q target corner')
        eligible = [cube for cube in cubes if any(t.count(a) >= 2 for t in corners(cube))]
        require(len(eligible) == 1 and eligible[0].count(a) == 3,
                'Q target must have only seven eligible source cubes')


def number(value):
    return f'{value:.3f}'.rstrip('0').rstrip('.')


class Drawing:
    """One vector scene, emitted as either SVG or TikZ."""
    def __init__(self, width, height,
                 title='Why the exceptional 28 cubes cannot build a three-colour target',
                 description=('Seven copies of each of four cube varieties share '
                              'one orientation on every colour triple and lack its reverse. '
                              'A target with a trichromatic corner needs both orientations. '
                              'A target without such a corner needs eight cubes with the same '
                              'repeated colour, but only seven are available.')):
        self.width, self.height = width, height
        self.title, self.description = title, description
        self.items = []

    def polygon(self, points, fill, stroke='#222', width=1.2):
        self.items.append(('polygon', points, fill, stroke, width))

    def line(self, points, stroke='#555', width=1.2, dashed=False):
        self.items.append(('line', points, stroke, width, dashed))

    def circle(self, x, y, radius, fill='white', stroke='#222', width=1.5):
        self.items.append(('circle', x, y, radius, fill, stroke, width))

    def text(self, x, y, value, size=18, bold=False, anchor='middle'):
        self.items.append(('text', x, y, str(value), size, bold, anchor))

    def svg(self):
        from html import escape
        out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.width}" '
               f'height="{self.height}" viewBox="0 0 {self.width} {self.height}" '
               'role="img" aria-labelledby="title description">',
               f'<title id="title">{escape(self.title)}</title>',
               f'<desc id="description">{escape(self.description)}</desc>',
               '<rect width="100%" height="100%" fill="white"/>',
               '<g font-family="Helvetica,Arial,sans-serif" fill="#111" stroke-linejoin="round">']
        for kind, *args in self.items:
            if kind == 'text':
                x, y, value, size, bold, anchor = args
                weight = 'bold' if bold else 'normal'
                out.append(f'<text x="{number(x)}" y="{number(y)}" font-size="{size}" '
                           f'font-weight="{weight}" text-anchor="{anchor}" '
                           f'dy="0.35em">{escape(value)}</text>')
            elif kind == 'circle':
                x, y, radius, fill, stroke, width = args
                out.append(f'<circle cx="{number(x)}" cy="{number(y)}" r="{radius}" '
                           f'fill="{fill}" stroke="{stroke}" stroke-width="{width}"/>')
            else:
                points, *style = args
                points = ' '.join(f'{number(x)},{number(y)}' for x, y in points)
                if kind == 'polygon':
                    fill, stroke, width = style
                    out.append(f'<polygon points="{points}" fill="{fill}" '
                               f'stroke="{stroke}" stroke-width="{width}"/>')
                else:
                    stroke, width, dashed = style
                    dash = ' stroke-dasharray="4 3"' if dashed else ''
                    out.append(f'<polyline points="{points}" fill="none" stroke="{stroke}" '
                               f'stroke-width="{width}"{dash}/>')
        return '\n'.join(out + ['</g>', '</svg>']) + '\n'

    def tikz(self):
        # 158 mm fits the paper's 160 mm text block. Font sizes scale with geometry.
        scale = 158 / self.width
        point_scale = scale * 72.27 / 25.4
        colours = {'white': 'white', '#222': 'black!87', '#555': 'black!67',
                   '#ccc': 'black!20', **{f'#{c}': f'cube{i}' for i, c in enumerate(COLOURS)}}
        def point(p):
            return f'({number(p[0])},{number(p[1])})'
        out = ['% Generated by scripts/generate_figure.py; do not edit.']
        out += [f'\\definecolor{{cube{i}}}{{HTML}}{{{c}}}' for i, c in enumerate(COLOURS)]
        out.append(f'\\begin{{tikzpicture}}[x={number(scale)}mm,y=-{number(scale)}mm]')
        out.append(f'\\path[use as bounding box] (0,0) rectangle ({self.width},{self.height});')
        for kind, *args in self.items:
            if kind == 'text':
                x, y, value, size, bold, anchor = args
                value = value.replace('&', r'\&').replace('×', r'\(\times\)')
                anchor = {'middle': 'center', 'start': 'west', 'end': 'east'}[anchor]
                # Standard Computer Modern sizes avoid font substitution warnings.
                size = min((8, 9, 10, 10.95, 12), key=lambda s: abs(s - size * point_scale))
                font = rf'\sffamily\fontsize{{{number(size)}}}{{{number(size * 1.2)}}}\selectfont'
                if bold:
                    font += r'\bfseries'
                out.append(f'\\node[anchor={anchor},inner sep=0pt,outer sep=0pt,font={{{font}}}] '
                           f'at {point((x,y))} {{{value}}};')
            elif kind == 'circle':
                x, y, radius, fill, stroke, width = args
                out.append(f'\\filldraw[fill={colours[fill]},draw={colours[stroke]},'
                           f'line width={number(width * point_scale)}pt] {point((x,y))} '
                           f'circle[radius={number(radius * scale)}mm];')
            else:
                points, *style = args
                path = ' -- '.join(point(p) for p in points)
                if kind == 'polygon':
                    fill, stroke, width = style
                    options = f'fill={colours[fill]},draw={colours[stroke]}'
                    path += ' -- cycle'
                else:
                    stroke, width, dashed = style
                    options = f'draw={colours[stroke]}' + (',dashed' if dashed else '')
                out.append(f'\\draw[{options},line join=round,line width={number(width * point_scale)}pt] {path};')
        return '\n'.join(out + ['\\end{tikzpicture}']) + '\n'


def marker(d, x, y):
    d.circle(x, y, 4.5)
    d.circle(x, y, 1.3, fill='#222', width=0)


def net(d, cube, x, y, unit, labels=None, highlight=False):
    for (col, row), face in NET.items():
        left, top = x + col * unit, y + row * unit
        d.polygon([(left, top), (left + unit, top),
                   (left + unit, top + unit), (left, top + unit)], f'#{COLOURS[cube[face]]}')
        d.text(left + unit / 2, top + unit / 2,
               labels[face] if labels else cube[face], size=19)
    if highlight:
        marker(d, x + 2 * unit, y + unit)


def corner(d, triple, x, y, unit=24):
    """Three outside faces around a vertex; left, right, top read counterclockwise."""
    side = math.sqrt(3) * unit / 2
    polygons = (
        [(0, 0), (-side, -unit/2), (-side, unit/2), (0, unit)],
        [(0, 0), (0, unit), (side, unit/2), (side, -unit/2)],
        [(0, 0), (side, -unit/2), (0, -unit), (-side, -unit/2)],
    )
    for colour, points in zip(triple, polygons):
        d.polygon([(x + px, y + py) for px, py in points], f'#{COLOURS[colour]}')
        d.text(x + sum(px for px, _ in points)/4,
               y + sum(py for _, py in points)/4, colour, size=18)
    d.text(x, y + unit + 17, word(triple), size=18)


def target(d, x, y, unit):
    """D(0,1,2): draw +x, +y, +z faces, each divided into four squares."""
    def project(a, b, c):
        return x + (b-a) * math.sqrt(3)/2 * unit, y + ((a+b)/2-c) * unit
    faces = ((0, lambda a,b: (2,a,2-b)),
             (1, lambda a,b: (2-a,2,2-b)),
             (2, lambda a,b: (a,b,2)))
    for colour, point in faces:
        for a in range(2):
            for b in range(2):
                points = [project(*point(a+s, b+t)) for s,t in ((0,0),(1,0),(1,1),(0,1))]
                d.polygon(points, f'#{COLOURS[colour]}')
                d.text(sum(px for px,_ in points)/4, sum(py for _,py in points)/4,
                       colour, size=18)
    marker(d, *project(2,2,2))  # 012
    marker(d, *project(2,2,0))  # 021; the bottom face is hidden.


def draw_sources(d, cubes, compact):
    d.text(16, 24, 'A   The exceptional collection: 28 cubes', size=20, bold=True, anchor='start')
    for i, cube in enumerate(cubes):
        if compact:
            x, y, unit = 43 + 198 * i, 50, 29
        else:
            x, y, unit = 70 + 280 * (i % 2), 58 + 160 * (i // 2), 30
        net(d, corner_view(cube), x, y, unit, highlight=True)
        d.text(x + 2 * unit, y + 3 * unit + 23, f'{COPIES} × {word(cube)}', size=19)
    y = 185 if compact else 354
    marker(d, 25, y)
    d.text(40, y, 'Monochromatic corner; fold the nets away from you.', size=17, anchor='start')


def draw_orientations(d, compact):
    if compact:
        top, columns, available_y, missing_y = 222, (70, 180, 290, 400), 292, 397
    else:
        top, columns, available_y, missing_y = 400, (70, 210, 350, 490), 475, 585
    heading = ('B   A target with a trichromatic corner needs both orientations' if compact
               else 'B   The missing corner orientations')
    d.text(16, top, heading, size=20, bold=True, anchor='start')
    d.text(16, available_y - 41, 'Available on every source cube', size=18, bold=True, anchor='start')
    d.text(16, missing_y - 41, 'Missing from the whole collection', size=18, bold=True, anchor='start')
    for x, yes, no in zip(columns, AVAILABLE, MISSING):
        corner(d, yes, x, available_y)
        corner(d, no, x, missing_y)
    d.text(16, missing_y + 68, 'Read each corner counterclockwise from outside.', size=17, anchor='start')


def draw_target(d, compact):
    if compact:
        d.line([(460, 246), (460, 474)], stroke='#ccc')
        d.text(626, 255, 'Example target D(0,1,2)', size=18, bold=True)
        x, y, unit = 584, 346, 29
        label_x, yes_y, no_y = 737, 319, 414
        note_y = 464
    else:
        d.text(16, 686, 'A target with a trichromatic corner', size=20, bold=True, anchor='start')
        d.text(16, 712, 'needs both orientations.', size=20, bold=True, anchor='start')
        x, y, unit = 180, 806, 36
        label_x, yes_y, no_y = 421, 773, 875
        note_y = 934
    target(d, x, y, unit)
    for py, ly, value, description, hidden in (
        (y, yes_y, '012', 'available', False),
        (y + 2 * unit, no_y, '021', 'missing', True),
    ):
        d.line([(x+6, py), (label_x-62, ly)], dashed=hidden)
        d.text(label_x, ly, value, size=20, bold=True)
        d.text(label_x, ly+24, description, size=17)
    centre = 626 if compact else 280
    d.text(centre, note_y, '4 corners of each type', size=18)
    if compact:
        d.text(centre, note_y+24, 'Opposite faces have equal colours.', size=15)
    else:
        d.text(centre, note_y+26, 'Opposite faces have equal colours.', size=18)


def draw_nontrichromatic(d, compact):
    top = 530 if compact else 1008
    d.text(16, top, 'C   Targets with no trichromatic corners', size=20, bold=True, anchor='start')
    net(d, (0,0,0,0,1,2), 52, top+30, 25 if compact else 30,
        labels=('a','a','a','a','b','c'))
    d.text(102 if compact else 112, top+(129 if compact else 148), 'Q(a;b,c)', size=18)
    if compact:
        for y, text in ((top+36, 'Four a faces; b and c on opposite faces.'),
                        (top+65, 'Every corner contains colour a twice.'),
                        (top+100, 'Eight corners need eight distinct cubes;'),
                        (top+129, 'only the seven cubes with repeated colour a qualify.')):
            d.text(218, y, text, size=18, anchor='start')
    else:
        for y, text in ((top+40, 'Four a faces;'), (top+67, 'b and c opposite.'),
                        (top+102, 'Every corner has'), (top+129, 'colour a twice.')):
            d.text(244, y, text, size=20, anchor='start')
        d.text(280, top+174, 'Eight corners need eight distinct cubes.', size=20)
        d.text(280, top+204, 'Only seven cubes can supply them.', size=20, bold=True)


def illustration(cubes, compact):
    d = Drawing(800 if compact else 560, 684 if compact else 1238)
    draw_sources(d, cubes, compact)
    d.line([(16, 203 if compact else 377), (d.width-16, 203 if compact else 377)], stroke='#ccc')
    draw_orientations(d, compact)
    draw_target(d, compact)
    d.line([(16, 510 if compact else 985), (d.width-16, 510 if compact else 985)], stroke='#ccc')
    draw_nontrichromatic(d, compact)
    return d


def bucket_illustration():
    """Show examples, checking memberships directly from their corner types."""
    from cube_geometry import corners, cyclic
    examples = (
        ('T', (0,1,0,2,0,3), {0}),
        ('P', (0,1,0,2,1,3), {0,1}),
        ('C', (0,0,1,1,2,3), set()),
    )
    d = Drawing(560, 450, title='Counting colour-bucket memberships',
                description='A T cube belongs to one colour bucket, a P cube to two, '
                            'and a checkerboard cube to none. In an unsolvable reduced '
                            'collection, each of the four buckets contains at most seven cubes.')
    d.text(104, 25, 'Reduced cubes', size=20, bold=True)
    d.text(460, 25, 'Colour buckets', size=20, bold=True)
    for colour in range(4):
        y = 60 + 100 * colour
        d.polygon([(390,y), (530,y), (520,y+55), (400,y+55)], f'#{COLOURS[colour]}')
        d.text(460, y+27, colour, size=22, bold=True)
        d.text(460, y+76, 'at most 7', size=18)
    for i, (kind, cube, expected) in enumerate(examples):
        types = set(corners(cube))
        memberships = {a for a in range(4)
                       if sum(cyclic((a,a,b)) in types for b in range(4) if b != a) >= 2}
        require(memberships == expected, f'Unexpected {kind} bucket memberships')
        y = 55 + 135 * i
        net(d, cube, 40, y, 26)
        count = len(memberships)
        label = '1 membership' if count == 1 else f'{count} memberships'
        d.text(104, y+101, f'{kind}: {label}', size=19)
        for a in sorted(memberships):
            start = (156, y+39)
            # Separate endpoints keep the two arrows into bucket 0 distinguishable.
            end = (394, 82) if kind == 'T' else ((399,109) if a == 0 else (395,187))
            d.line([start, end], width=1.7)
            dx, dy = end[0]-start[0], end[1]-start[1]
            length = math.hypot(dx,dy)
            ux, uy = dx/length, dy/length
            d.polygon([end, (end[0]-9*ux-4*uy, end[1]-9*uy+4*ux),
                       (end[0]-9*ux+4*uy, end[1]-9*uy-4*ux)], '#555', stroke='#555')
    return d


def main():
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'paper'
    cubes = obstruction()
    validate_geometry(cubes)
    (directory / 'obstruction-figure.tex').write_text(illustration(cubes, compact=True).tikz(), encoding='utf-8')
    (directory / 'obstruction-figure.svg').write_text(illustration(cubes, compact=False).svg(), encoding='utf-8')
    (directory / 'bucket-figure.svg').write_text(bucket_illustration().svg(), encoding='utf-8')


if __name__ == '__main__':
    main()
