#!/usr/bin/env python3
"""Draw the state graph of a gov-tla module, to a limited depth.

TLC explores every behaviour of up to DEPTH steps from the initial state;
each state is drawn as what differs from the initial state, coloured by who
acted to reach it.
"""

import argparse
import os
from collections import Counter, defaultdict

import graphviz

import tlaviz

DEFAULT_DEPTH = {'Constitution': 2, 'Executive': 1, 'Judiciary': 1, 'Government': 1}


def state_label(lines, extra=None):
    rows = [tlaviz.html_escape(tlaviz.clip(text)) for _, text in lines] or ['Initial state']
    if extra:
        rows.insert(0, f'<B>{tlaviz.html_escape(extra)}</B>')
    return '<' + '<BR ALIGN="LEFT"/>'.join(rows) + '<BR ALIGN="LEFT"/>>'


def create_visualization(module, states, edges, dist, merge=4, all_edges=False):
    depth = max(dist.values())
    init = next(n for n, d in dist.items() if d == 0)
    forward = [(s, t, a) for s, t, a in edges if dist[t] == dist[s] + 1]
    shown_edges = edges if all_edges else forward

    # The edge that first reached each state decides its colour.
    reached_by = {}
    for s, t, a in sorted(forward, key=lambda e: dist[e[0]]):
        reached_by.setdefault(t, a)

    # Collapse wide fans at the frontier: siblings reached from the same
    # parents by the same action become one node.
    group_of = {}
    if merge:
        parents = defaultdict(set)
        for s, t, a in forward:
            parents[t].add((s, a))
        groups = defaultdict(list)
        for n, d in dist.items():
            if d == depth and d > 0:
                key = (frozenset(parents[n]), reached_by[n],
                       tlaviz.category(reached_by[n], states[n]))
                groups[key].append(n)
        for i, members in enumerate(g for g in groups.values() if len(g) >= merge):
            for n in members:
                group_of[n] = f'group{i}'

    def rep(n):
        return group_of.get(n, n)

    dot = graphviz.Digraph(module, format='png')
    dot.attr(rankdir='TB', bgcolor='white', dpi='150', ranksep='0.8', nodesep='0.3')
    dot.attr('node', shape='box', fontname='Courier', fontsize='10', margin='0.15')
    dot.attr('edge', fontname='Helvetica', fontsize='9', arrowsize='0.7')

    used = set()
    drawn = set()
    by_depth = defaultdict(list)
    for n in states:
        by_depth[dist[n]].append(n)
    for d in sorted(by_depth):
        with dot.subgraph() as s:
            s.attr(rank='same')
            members_of = defaultdict(list)
            for n in by_depth[d]:
                members_of[rep(n)].append(n)
            for node, members in members_of.items():
                cat = tlaviz.category(reached_by.get(members[0]), states[members[0]])
                used.add(cat)
                fill = tlaviz.CATEGORIES[cat][0]
                if len(members) == 1:
                    lines = tlaviz.diff_lines(states[init], states[node])
                    s.node(node, state_label(lines), style='filled', fillcolor=fill)
                else:
                    # Show what the merged states have in common, and
                    # which variables differ between them.
                    diffs = [tlaviz.diff_lines(states[init], states[m]) for m in members]
                    common = set(diffs[0]).intersection(*map(set, diffs[1:]))
                    lines = [l for l in diffs[0] if l in common]
                    varying = sorted({p for ls in diffs for p, l in ls if (p, l) not in common})
                    if varying:
                        lines.append(('', tlaviz.clip('vary: ' + ', '.join(varying))))
                    s.node(node, state_label(lines, f'{len(members)} states'),
                           style='filled,dashed', fillcolor=fill)
                drawn.add(node)

    seen = set()
    forward_set = set(forward)
    for src, dst, action in shown_edges:
        key = (rep(src), rep(dst), action)
        if key in seen or src == dst:
            continue
        seen.add(key)
        style = "solid" if (src, dst, action) in forward_set else "dotted"
        dot.edge(rep(src), rep(dst), label=action, style=style)

    tlaviz.add_legend(dot, used)
    return dot, len(drawn)


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('module', nargs='?', default='Constitution', choices=tlaviz.MODULES)
    parser.add_argument('depth', nargs='?', type=int,
                        help='steps from the initial state (default: 2 for Constitution, '
                             '1 for the others)')
    parser.add_argument('--merge', type=int, default=4, metavar='N',
                        help='collapse N or more sibling states at the deepest level '
                             'reached by the same action into one node; 0 never '
                             'collapses (default: 4)')
    parser.add_argument('--all-edges', action='store_true',
                        help='also draw edges that do not go one level deeper '
                             '(back to earlier states, or across a level), dotted')
    parser.add_argument('--keep-dot', action='store_true',
                        help="keep TLC's raw state dump as MODULE_states_depthN.dot")
    args = parser.parse_args()
    module = args.module
    depth = args.depth if args.depth is not None else DEFAULT_DEPTH[module]

    print(f'Running TLC on {module} to depth {depth}...')
    dot_out = f'{module}_states_depth{depth}.dot' if args.keep_dot else None
    states, edges, dist = tlaviz.bfs_graph(module, depth, dot_out)
    print(f'Found {len(states)} states and {len(edges)} transitions')
    if dot_out:
        print(f'Kept TLC dump in {dot_out}')

    print(f'Creating visualization (depth <= {depth})...')
    dot, nodes = create_visualization(module, states, edges, dist,
                                      merge=args.merge, all_edges=args.all_edges)
    output_file = f'{module}_depth{depth}'
    dot.render(os.path.join(tlaviz.VISUALS, output_file), cleanup=True)
    print(f'Generated visuals/{output_file}.png ({nodes} nodes)')

    print('\nStates by depth:')
    print('Depth | States')
    print('------+-------')
    for d, count in sorted(Counter(dist.values()).items()):
        print(f'  {d}   | {count:6d}')

    print('\nTransitions one level deeper, by action:')
    actions = Counter(a for s, t, a in edges if dist[t] == dist[s] + 1)
    width = max(len(a) for a in actions) if actions else 6
    print(f'{"Action":<{width}} | Count | Who acted')
    print(f'{"-" * width}-+-------+----------')
    for a, count in actions.most_common():
        print(f'{a:<{width}} | {count:5d} | {tlaviz.CATEGORIES[tlaviz.category(a)][1]}')


if __name__ == '__main__':
    main()
