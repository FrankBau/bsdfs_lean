#!/usr/bin/python3

# Generates cases.txt (graphs as index-based succ/pred lists in NetworkX scan order) and expected.txt (bsdfs_traced events, nodes as indices)
import random
import networkx as nx
from bsdfs_traced import bsdfs_traced

def cases():
    Z = nx.parse_adjlist(['s a d', 'a c t', 'b a', 'c b z', 'd t z', 'z b c', 't'], create_using=nx.DiGraph)
    yield 'Z', Z, 's', 't', 5
    Y = nx.parse_adjlist(["A D", "B D E F", "C", "D A B C", "E A B D", "F B"], create_using=nx.DiGraph)
    yield 'Y', Y, 'E', 'C', 6
    Y2 = nx.DiGraph()
    Y2.add_edges_from([(0, 1), (0, 2), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 5), (3, 1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (5, 1)])
    yield 'Y2', Y2, 4, 5, 5
    for run in range(1200):
        random.seed(42 + run)
        n = random.randint(2, 9)
        p = random.uniform(0, 1)
        k = max(random.getrandbits(n).bit_count(), 1)
        G = nx.gnp_random_graph(n, p, directed=True, seed=run)
        if run < 1000:
            s, t = random.sample(range(n), 2)      # path mode
        else:
            s = t = random.randrange(n)            # cycle mode (same code, s == t)
        yield f'R{run}', G, s, t, k

def main():
    ncases = nevents = nout = 0
    with open('cases.txt', 'w') as fc, open('expected.txt', 'w') as fe:
        for name, G, s, t, k in cases():
            idx = {v: i for i, v in enumerate(G.nodes)}
            n = len(idx)
            print(f"case {name} {n} {idx[s]} {idx[t]} {k}", file=fc)
            for v in G.nodes:
                print(" ".join(str(idx[w]) for w in G.successors(v)), file=fc)
            for v in G.nodes:
                print(" ".join(str(idx[u]) for u in G.predecessors(v)), file=fc)
            trace = []
            bsdfs_traced(G, s, t, k, trace.append)
            print(f"case {name}", file=fe)
            for ev in trace:
                if ev[0] == 'output':
                    ev = (ev[0], ev[1], tuple(idx[x] for x in ev[2]))
                    nout += 1
                elif ev[0] not in ('start', 'term'):
                    ev = (ev[0], ev[1], idx[ev[2]]) + ev[3:]
                print(repr(ev), file=fe)
                nevents += 1
            ncases += 1
    print(f"{ncases} cases, {nevents} events, {nout} outputs")

main()