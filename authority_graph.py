#!/usr/bin/env python3
"""Draw Government.tla's authority graph.

With no seed, draws the graph of 1789 (the initial state). With a seed, TLC
simulates STEPS random steps and the graph is drawn as it stands at the end:
agencies and courts Congress created, edges amendments added or dropped,
statutory edges the courts struck, and the edge that fired last.
"""

import argparse

import graphviz

import tlaviz

KIND_COLOUR = {'Power': 'royalblue3', 'Select': 'forestgreen',
               'Amend': 'darkorchid', 'Control': 'gray35'}
NODE_STYLE = {
    'People':       dict(shape='ellipse', fillcolor='plum'),
    'States':       dict(shape='ellipse', fillcolor='plum'),
    'Constitution': dict(shape='note',    fillcolor='lightyellow'),
    'Congress':     dict(shape='box',     fillcolor='lightblue'),
    'Executive':    dict(shape='box',     fillcolor='lightsalmon'),
    'VicePresident': dict(shape='box',    fillcolor='peachpuff'),
    'Judiciary':    dict(shape='box',     fillcolor='lightgreen'),
}


def create_graph(state, founding, layers, title):
    dot = graphviz.Digraph('Authority', format='png')
    dot.attr(rankdir='TB', bgcolor='white', dpi='150', ranksep='1.0', nodesep='0.6',
             label=title, labelloc='t', fontname='Helvetica', fontsize='14')
    dot.attr('node', style='filled', fontname='Helvetica', fontsize='12')
    dot.attr('edge', fontname='Helvetica', fontsize='8', arrowsize='0.6')

    seated = set(state['seated'])
    for n, style in NODE_STYLE.items():
        label = n
        if n in ('Executive', 'VicePresident'):
            label = 'Vice President' if n == 'VicePresident' else n
            label += '\n(seated)' if n in seated else '\n(vacant)'
            if n in state['nominated']:
                label += '\nnominee pending'
            if state['trial'] == n:
                label += '\non trial'
        if n == 'Judiciary' and state['trial'] == 'Judiciary':
            label += '\n(a judge on trial)'
        dot.node(n, label, **style)
    for n in sorted(state['live']):
        label = f'{n}\n' + ('(seated)' if n in seated else '(vacant)')
        if n in state['nominated']:
            label += '\nnominee pending'
        if state['trial'] == n:
            label += '\non trial'
        dot.node(n, label, shape='box', style='filled,rounded', fillcolor='white')
    with dot.subgraph() as s:
        s.attr(rank='same')
        s.node('People')
        s.node('States')

    last = state['last']
    challenged = set(state['challenged'])
    for e in sorted(state['edges'], key=tlaviz.fmt):
        r = dict(e)
        layer = 'control' if r['kind'] == 'Control' else 'grant'
        if layer not in layers:
            continue
        attrs = dict(color=KIND_COLOUR[r['kind']], fontcolor=KIND_COLOUR[r['kind']])
        label = r['label']
        if r['basis'] == 'Statute':
            attrs['style'] = 'dashed'
        elif e not in founding:
            label += ' (amendment)'
            attrs['penwidth'] = '2'
        if e in challenged:
            label += ' ⚖ challenged'
            attrs['color'] = attrs['fontcolor'] = 'red3'
        if e == last:
            label = f'{label} (fired last)'
            attrs['penwidth'] = '3'
        dot.edge(r['from'], r['to'], label=label, **attrs)

    for e in founding:
        r = dict(e)
        layer = 'control' if r['kind'] == 'Control' else 'grant'
        if e not in state['edges'] and layer in layers:
            dot.edge(r['from'], r['to'], label=f"{r['label']} (repealed)",
                     style='dotted', color='gray70', fontcolor='gray60')

    with dot.subgraph(name='cluster_legend') as s:
        s.attr(label='Edges', fontname='Helvetica', fontsize='11', style='rounded')
        rows = ''.join(f'<TR><TD ALIGN="LEFT"><FONT COLOR="{c}">━━ {k}</FONT></TD></TR>'
                       for k, c in KIND_COLOUR.items())
        rows += ('<TR><TD ALIGN="LEFT">- - - by statute</TD></TR>'
                 '<TR><TD ALIGN="LEFT">━━ by the Constitution</TD></TR>'
                 '<TR><TD ALIGN="LEFT"><FONT COLOR="red3">⚖ challenged in court</FONT></TD></TR>')
        s.node('legend', f'<<TABLE BORDER="0" CELLSPACING="2">{rows}</TABLE>>',
               shape='plaintext', style='')
    return dot


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('seed', nargs='?', type=int,
                        help='simulate from this seed (default: draw the initial graph)')
    parser.add_argument('--steps', type=int, default=40,
                        help='steps to simulate when a seed is given (default: 40)')
    parser.add_argument('--layer', choices=['grant', 'control', 'all'], default='all',
                        help='draw only the grant layer, only the control layer, or both')
    args = parser.parse_args()
    layers = {'grant', 'control'} if args.layer == 'all' else {args.layer}
    steps = args.steps if args.seed is not None else 0

    print(f'Running TLC on Government ({steps} steps'
          + (f', seed {args.seed})...' if args.seed is not None else ')...'))
    trace = tlaviz.simulate('Government', args.seed or 0, steps)
    founding = set(trace[0][1]['edges'])
    action, state = trace[-1]

    if args.seed is None:
        title = 'The authority graph of 1789'
    else:
        ratified = [x for x, v in state['amendment'] if v == 'Ratified']
        title = (f'The authority graph after {len(trace) - 1} random steps (seed {args.seed})'
                 + (f' - amendments ratified: {", ".join(ratified)}' if ratified else ''))
        print('Actions taken:', ', '.join(a for a, _ in trace[1:]))

    edges = state['edges']
    print(f"{len(edges)} edges: "
          + ', '.join(f"{sum(1 for e in edges if e.get('kind') == k)} {k}" for k in KIND_COLOUR)
          + f"; {sum(1 for e in edges if e.get('basis') == 'Statute')} by statute")
    if state['live']:
        print('Bodies created by statute:', ', '.join(state['live']))

    dot = create_graph(state, founding, layers, title)
    output_file = 'Government_authority'
    if args.seed is not None:
        output_file += f'_seed{args.seed}'
    if args.layer != 'all':
        output_file += f'_{args.layer}'
    dot.render(output_file, cleanup=True)
    print(f'Generated {output_file}.png')


if __name__ == '__main__':
    main()
