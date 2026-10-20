# Smoke Test

to validate the lean implementation against the BS-DFS reference implementation in Python. 

Run: `../smoke_test.sh --clean`.

Background:
`bsdfs_traced.py` contains the bsdfs reference implementation, instrumented to generate
a detailed execution trace. `bsdfs_traced(G, s, t, k)` is called from the `smoke_gen.py`
driver, which creates many `(G, s, t, k)` instances, dumps them in a machine readable way
to file  `cases.txt`, executes `bsdfs_traced(G, s, t, k)` on them, and collects all traces
in file `expected.txt`. 

Then, it builds and executes `Main.lean` which reads `cases.txt`, executes bsdfs 
(in `BsdfsExec.lean`) on them and compares the output against the traces expected.

Expected output:

```console
lean/Python$ ../smoke_test.sh 
1203 cases, 423311 events, 63611 outputs
Build completed successfully (51 jobs).
smoke test passed: traces identical
```

The trace event type (Ev) is defined in `Bsdfs/BsdfsExec.lean`.