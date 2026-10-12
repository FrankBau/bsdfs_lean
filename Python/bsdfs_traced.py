"""BS-DFS (tight scheme) -- reference implementation with event callback.

The algorithm is a line-by-line transcription of Algorithms 1-3 of the paper
(bsdfs.tex, alg:bsdfs / alg:search / alg:fruitful).  Instrumentation is one
`emit(...)` call per event and one `steps += ...` per cost-model site; there
are no mode flags and no guards.  The paper's `Output(path)` line *is* the
output event.  Pass `emit=list.append` of a list to record a trace, or any
streaming evaluator (see trace_eval.py); pass `emit=lambda e: None` for a
counter-only run (the function returns the final step count).

Cost model (paper, sec:work-attribution), counted at exactly these sites:
    Search call at v     : 1 (entry) + 1 per scanned successor
    cascade dequeue at q : 1 (dequeue) + 1 per scanned predecessor
    producing an output  : |path| <= k+1

Event schema -- every event carries the step counter *after* the step it
represents, so all step accounting is derivable from the trace:

    ('start',   0)                            o_0, before any step
    ('enter',   step, v, h)                   after the entry step, h = |S|-1
    ('exit',    step, v, h, sd, fruitful)     before the pop
    ('output',  step, path)                   o_tau, path as a tuple
    ('cascade', step, origin, sd)             a Fruitful(...) call begins
    ('dequeue', step, q, d)                   after the dequeue step
    ('write',   step, x, old, new, kind)      kind in {'raise','fruitful','drop'}
    ('term',    step)                         o_{T+1}, after the last step

The events 'start' and 'term' realize the paper's virtual events o_0 and
o_{T+1}: the externally observable events of a run are exactly the 'start',
'output', and 'term' events of the trace.
"""
from collections import deque
import sys

def bsdfs_traced(G, s, t, k, emit):
    """Tight scheme.  Emits events; returns the total step count."""
    b = {x: 0 for x in G.nodes}
    S = []
    steps = 0

    def fruitful(v, sd):
        nonlocal steps
        emit(("cascade", steps, v, sd))                             # instr
        emit(("write", steps, v, b[v], sd, "fruitful"))             # instr
        b[v] = sd
        queue = deque([(v, sd)])
        while queue:
            q, d = queue.popleft()
            steps += 1                                              # instr
            emit(("dequeue", steps, q, d))                          # instr
            for p in G.predecessors(q):
                steps += 1                                          # instr
                if p not in S and b[p] > d + 1:
                    emit(("write", steps, p, b[p], d + 1, "drop"))  # instr
                    b[p] = d + 1
                    queue.append((p, d + 1))

    def search(v):
        nonlocal steps
        S.append(v)
        h = len(S) - 1
        steps += 1                                                  # instr
        emit(("enter", steps, v, h))                                # instr
        sd = k + 1
        for w in G.successors(v):
            steps += 1                                              # instr
            if b[w] + h < k:
                if w == t:
                    steps += h + 2                                  # instr
                    emit(("output", steps, tuple(S) + (t,)))
                    sd = 1
                elif w not in S:
                    sd = min(sd, search(w) + 1)
        if sd <= k and h > 0:                                       # early exit at s: no cascade when search(s) returns
            fruitful(v, sd)
        else:
            emit(("write", steps, v, b[v], k - h + 1, "raise"))     # instr
            b[v] = k - h + 1
        emit(("exit", steps, v, h, sd, sd <= k))                    # instr
        S.pop()
        return sd

    emit(("start", steps))
    search(s)
    emit(("term", steps))
    return steps



def pretty_print(trace, nodes=None, k=None, show_barriers=False, stream=sys.stdout):
    """Render a bsdfs_traced event list as prose.
 
    nodes           node order for the barrier column; inferred from the trace if omitted
    k               length bound, only used to label sd = k+1 as infinite
    show_barriers   prepend the barrier vector, reconstructed from the write events
    """
    if nodes is None:
        nodes = []
        for ev in trace:
            if ev[0] in ('enter', 'write', 'cascade', 'dequeue') and ev[2] not in nodes:
                nodes.append(ev[2])
            elif ev[0] == 'output':
                for v in ev[2]:
                    if v not in nodes:
                        nodes.append(v)
 
    bar = {v: 0 for v in nodes}
    depth = 0
    outputs = []
    last_out = 0
    max_gap = 0
 
    def put(step, text):
        prefix = f"{step:5d}  "
        if show_barriers:
            prefix += ' '.join(f"{bar.get(v, 0)}" for v in nodes) + "  "
        print(prefix + "  " * depth + text, file=stream)
 
    if show_barriers:
        print(f"{'step':>5}  {' '.join(nodes)}  event", file=stream)
    else:
        print(f"{'step':>5}  event", file=stream)
 
    for ev in trace:
        kind, step = ev[0], ev[1]
 
        if kind == 'start':
            put(step, "start")
 
        elif kind == 'enter':
            _, _, v, h = ev
            put(step, f"search({v}), search path has length h = {h}")
            depth += 1
 
        elif kind == 'write':
            _, _, v, old, new, how = ev
            bar[v] = new
            if how == 'raise':
                put(step, f"b[{v}] := {new}   fruitless at this depth, raised from {old}")
            elif how == 'drop':
                put(step, f"b[{v}] := {new}   cascade lowers the barrier from {old}")
            elif how == 'fruitful':
                note = "unchanged" if old == new else f"was {old}"
                put(step, f"b[{v}] := {new}   distance to t found, {note}")
            else:
                put(step, f"b[{v}] := {new}   [{how}, was {old}]")
 
        elif kind == 'exit':
            _, _, v, h, sd, fruitful = ev
            depth -= 1
            if fruitful:
                put(step, f"return({v}), shortest distance to t is {sd}")
            else:
                inf = "infinite" if k is None or sd == k + 1 else str(sd)
                put(step, f"return({v}), no path to t within budget (sd = {inf})")
 
        elif kind == 'output':
            _, _, path = ev
            outputs.append((step, path))
            gap = step - last_out
            max_gap = max(max_gap, gap)
            last_out = step
            put(step, f"OUTPUT {'->'.join(path)}   length {len(path) - 1}, delay {gap}")
 
        elif kind == 'cascade':
            _, _, v, sd = ev
            put(step, f"cascade starts at {v} with value {sd}")
 
        elif kind == 'dequeue':
            _, _, v, d = ev
            put(step, f"scan predecessors of {v}, b[{v}] is {d}")
 
        elif kind == 'term':
            gap = step - last_out
            max_gap = max(max_gap, gap)
            put(step, f"terminate after {step} steps; delay {gap}")
 
        else:
            put(step, f"{kind} {ev[2:]}")
 
    print(f"\n{len(outputs)} outputs: {', '.join(''.join(p) for _, p in outputs)}", file=stream)
    print(f"largest gap between consecutive outputs (and to termination): {max_gap} steps", file=stream)


if __name__ == "__main__":
    import networkx as nx

    # graph Z: counter-example to BC-DFS completeness
    Z = nx.parse_adjlist(['s a d', 'a c t', 'b a', 'c b z', 'd t z', 'z b c', 't'], create_using=nx.DiGraph)
    s, t, k = 's', 't', 5
    trace = []
    steps = bsdfs_traced(Z, s, t, k, trace.append)
    print(f"graph edges: {list(Z.edges)}")
    print(f"{s=}, {t=}, {k=}")
    for event in trace:
        print(event)
    print(f"steps: {steps}")

    # demo graph, showing that cascade lowering is needed
    print("")
    G = nx.parse_adjlist(["s a u", "a b t", "b c t", "c a", "u b"], create_using=nx.DiGraph)
    s, t, k = 's', 't', 5
    trace = []
    steps = bsdfs_traced(G, s, t, k, trace.append)
    print(f"graph edges: {list(G.edges)}")
    print(f"{s=}, {t=}, {k=}")
    pretty_print(trace)
    print(f"steps: {steps}")
