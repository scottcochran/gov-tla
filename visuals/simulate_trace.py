#!/usr/bin/env python3
"""Simulate and visualize one random behaviour of a gov-tla module.

TLC picks each step at random (reproducibly, given a seed) and stops after
STEPS steps, or earlier if no action is enabled. Each state is drawn as what
differs from the initial state; the lines that changed in that step are bold.
"""

import argparse
import random

import graphviz

import tlaviz


def create_trace_visualization(module, trace):
    dot = graphviz.Digraph(f'{module}Trace', format='png')
    dot.attr(rankdir='TB', bgcolor='white', dpi='150')
    dot.attr('node', shape='box', fontname='Courier', fontsize='10', margin='0.15')
    dot.attr('edge', fontname='Helvetica', fontsize='9')

    init = trace[0][1]
    used = set()
    for i, (action, state) in enumerate(trace):
        cat = tlaviz.category(action, state)
        used.add(cat)
        if i == 0:
            head = 'Start'
            changed = set()
        else:
            head = f'Step {i}: {action}'
            prev, now = tlaviz.flatten(trace[i - 1][1]), tlaviz.flatten(state)
            changed = {p for p in now if prev.get(p) != now[p]}
        rows = [f'<B>{tlaviz.html_escape(head)}</B>']
        lines = tlaviz.diff_lines(init, state)
        for path, text in lines:
            text = tlaviz.html_escape(tlaviz.clip(text))
            rows.append(f'<B>▸ {text}</B>' if path in changed else f'  {text}')
        if not lines:
            rows.append('  (initial state)' if i == 0 else '  (back to the initial state)')
        reverted = sorted(p for p in changed if p not in {path for path, _ in lines})
        if reverted:                            # changed back to the initial value
            text = tlaviz.clip('back to initial: ' + ', '.join(reverted))
            rows.append(f'<B>▸ {tlaviz.html_escape(text)}</B>')
        label = '<' + '<BR ALIGN="LEFT"/>'.join(rows) + '<BR ALIGN="LEFT"/>>'
        dot.node(str(i), label, style='filled', fillcolor=tlaviz.CATEGORIES[cat][0])
        if i > 0:
            dot.edge(str(i - 1), str(i))

    tlaviz.add_legend(dot, used)
    return dot


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('module', nargs='?', default='Constitution', choices=tlaviz.MODULES)
    parser.add_argument('seed', nargs='?', type=int,
                        help='random seed, for a reproducible behaviour (default: random)')
    parser.add_argument('--steps', type=int, default=20,
                        help='length of the behaviour (default: 20)')
    args = parser.parse_args()
    module = args.module
    seed = args.seed if args.seed is not None else random.randrange(2 ** 31)

    print(f'Simulating {module} with TLC (seed {seed}, {args.steps} steps)...')
    trace = tlaviz.simulate(module, seed, args.steps)

    print(f"\n{'=' * 50}")
    print(f'{module.upper()} SIMULATION')
    print(f"{'=' * 50}\n")
    for i, (action, state) in enumerate(trace):
        if i == 0:
            print('Initial state')
            for _, text in tlaviz.diff_lines({}, state, max_items=100):
                print(f'  {text}')
        else:
            who = tlaviz.CATEGORIES[tlaviz.category(action, state)][1]
            print(f'Step {i}: {action}  ({who})')
            for line in tlaviz.changes(trace[i - 1][1], state):
                print(f'  {line}')
        print('-' * 20)

    steps = len(trace) - 1
    if steps < args.steps:
        print(f'\nDeadlock: no action is enabled after {steps} steps')
    print(f'\nBehaviour length: {len(trace)} states ({steps} steps)')

    print('\nGenerating visualization...')
    dot = create_trace_visualization(module, trace)
    output_file = f'{module}_trace'
    if args.seed is not None:
        output_file += f'_seed{args.seed}'
    tlaviz.save(dot, output_file)
    if args.seed is None:
        print(f'Re-run with seed {seed} to get the same behaviour again.')


if __name__ == '__main__':
    main()
