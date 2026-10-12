import Bsdfs

/-- info: 'bsdfs_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bsdfs_sound

/-- info: 'bsdfs_complete_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bsdfs_complete_once

/-- info: 'bsdfs_worst_case_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bsdfs_worst_case_delay

/-- info: 'bsdfs_amortized_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bsdfs_amortized_delay


/-! Smoke-test driver: reads cases.txt, prints the trace of `bsdfs` per case in Python repr format
    (nodes as indices), for a plain `diff` against bsdfs_traced.py. -/

def pyNode {n : Nat} (v : Fin n) : String := toString v.val

def pyKind : Kind → String
  | .raise => "'raise'" | .fruitful => "'fruitful'" | .drop => "'drop'"

def pyBool (b : Bool) : String := if b then "True" else "False"

def pyEv {n : Nat} : Ev n → String
  | .start s           => s!"('start', {s})"
  | .enter s v h       => s!"('enter', {s}, {pyNode v}, {h})"
  | .exit s v h sd f   => s!"('exit', {s}, {pyNode v}, {h}, {sd}, {pyBool f})"
  | .output s p        => s!"('output', {s}, ({", ".intercalate (p.map pyNode)}))"
  | .cascade s v sd    => s!"('cascade', {s}, {pyNode v}, {sd})"
  | .dequeue s q d     => s!"('dequeue', {s}, {pyNode q}, {d})"
  | .write s x o nw kd => s!"('write', {s}, {pyNode x}, {o}, {nw}, {pyKind kd})"
  | .term s            => s!"('term', {s})"

def nats (line : String) : List Nat := ((line.splitOn " ").filter (· ≠ "")).map String.toNat!

def runCase (n s t k : Nat) (succL predL : Array (List Nat)) : List String :=
  if hs : s < n then
    if ht : t < n then
      let toFin (xs : List Nat) : List (Fin n) := xs.filterMap fun x => if h : x < n then some ⟨x, h⟩ else none
      let succA : Array (List (Fin n)) := succL.map toFin
      let predA : Array (List (Fin n)) := predL.map toFin
      let G : Graph n := { succ := fun v => succA[v.1]!, pred := fun v => predA[v.1]! }
      (bsdfs G ⟨s, hs⟩ ⟨t, ht⟩ k).map pyEv
    else ["bad t"]
  else ["bad s"]

def main (args : List String) : IO Unit := do
  let lines ← IO.FS.lines (args.headD "cases.txt")
  let out ← IO.getStdout
  let mut i := 0
  while i < lines.size do
    let hdr := (lines[i]!.splitOn " ").filter (· ≠ "")
    let name := hdr[1]!
    let n := hdr[2]!.toNat!
    let s := hdr[3]!.toNat!
    let t := hdr[4]!.toNat!
    let k := hdr[5]!.toNat!
    let succL := (lines.extract (i + 1) (i + 1 + n)).map nats
    let predL := (lines.extract (i + 1 + n) (i + 1 + 2 * n)).map nats
    out.putStrLn s!"case {name}"
    for e in runCase n s t k succL predL do
      out.putStrLn e
    i := i + 1 + 2 * n
