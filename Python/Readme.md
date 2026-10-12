# Smoke Test

to validate the lean implementation against the bsdfs reference implementation (Python). 

`bsdfs_traced.py` contains the bsdfs reference implementation, instrumented to generate
a detailed execution trace. `bsdfs_traced` is called from `smoke_gen.py` which creates
many `(G, s, t, k)` instances, dumps them in a machine readable way to file 
`cases.txt`, executes `bsdfs_traced(G, s, t, k)` on them, and collects the traces in
file `expected.txt`. 

```
lean/Python$ ./smoke_gen.py 
1203 cases, 423311 events, 63611 outputs
```

Then, the lean implementaion (in Bsdfs/BsdfsExec.lean) is run (via Main.lean) on the
same instances, generating its own trace `lean_out.txt`.

```
lean/bsdfs$ lake exe bsdfs ../Python/cases.txt > ../Python/lean_out.txt
```

Both files should be identical:

```
lean$ diff Python/lean_out.txt Python/expected.txt
```