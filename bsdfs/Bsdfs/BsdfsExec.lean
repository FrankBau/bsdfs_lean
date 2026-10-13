/-
  BS-DFS (tight scheme) as an executable, tick-instrumented Lean 4 function.

  Line-by-line transcription of bsdfs_traced.py (Algorithms 1-3 of bsdfs.tex): same cost model,
  same event schema, every event stamped with the step counter *after* the step it represents.
  Core Lean only (no Mathlib).  The definitions at the end say what the proofs are about; the theorems themselves
  (soundness, completeness, worst-case and amortized delay) are stated and proved in the other files of Bsdfs/.

  Cost model (sec:work-attribution), counted at exactly these sites:
    Search call at v     : 1 (entry) + 1 per scanned successor
    cascade dequeue at q : 1 (dequeue) + 1 per scanned predecessor
    producing an output  : |path| = h + 2
-/

/-- Directed graph on `Fin n`.  `pred` is stored explicitly (as NetworkX does) so that the scan
    order is the same as in the Python reference; `Graph.WF` below ties it to `succ`. -/
structure Graph (n : Nat) where
  succ : Fin n → List (Fin n)
  pred : Fin n → List (Fin n)

/-- well-formed digraph: no duplicate edges (self-loops are harmless), `pred` is exactly the reverse of `succ` -/
structure Graph.WF {n : Nat} (G : Graph n) : Prop where
  succ_nodup : ∀ u, (G.succ u).Nodup
  pred_nodup : ∀ v, (G.pred v).Nodup
  rev        : ∀ u v, v ∈ G.succ u ↔ u ∈ G.pred v

def Graph.m {n : Nat} (G : Graph n) : Nat := ((List.finRange n).map fun v => (G.succ v).length).sum

inductive Kind where
  | raise | fruitful | drop
  deriving DecidableEq

/-- the event schema of bsdfs_traced.py -/
inductive Ev (n : Nat) where
  | start   (step : Nat)
  | enter   (step : Nat) (v : Fin n) (h : Nat)
  | exit    (step : Nat) (v : Fin n) (h sd : Nat) (fruitful : Bool)
  | output  (step : Nat) (path : List (Fin n))
  | cascade (step : Nat) (origin : Fin n) (sd : Nat)
  | dequeue (step : Nat) (q : Fin n) (d : Nat)
  | write   (step : Nat) (x : Fin n) (old new : Nat) (kind : Kind)
  | term    (step : Nat)
  deriving DecidableEq

/-- algorithm state: barriers b, stack S, step counter, recorded trace -/
structure St (n : Nat) where
  b     : Vector Nat n
  S     : Array (Fin n)
  steps : Nat
  trace : Array (Ev n)

abbrev M (n : Nat) := StateM (St n)

namespace M
variable {n : Nat}
def tick (c : Nat := 1) : M n Unit := modify fun st => { st with steps := st.steps + c }
def steps : M n Nat := return (← get).steps
def emit (e : Ev n) : M n Unit := modify fun st => { st with trace := st.trace.push e }
def bar (x : Fin n) : M n Nat := return (← get).b[x]
def setBar (x : Fin n) (val : Nat) : M n Unit := modify fun st => { st with b := st.b.set x.1 val x.2 }
def stack : M n (Array (Fin n)) := return (← get).S
def push (v : Fin n) : M n Unit := modify fun st => { st with S := st.S.push v }
def pop : M n Unit := modify fun st => { st with S := st.S.pop }
end M
open M

variable {n : Nat}

/-- Algorithm 3, Fruitful(v, sd): cascade = reverse BFS from v over nodes off the stack.
    `while queue:` becomes a bounded loop over a FIFO array with read index i.  Bound n suffices
    because every node is enqueued at most once per cascade (proof obligation, not yet proved);
    exiting via the bound instead of via `break` would be a divergence from the Python code. -/
def fruitful (G : Graph n) (v : Fin n) (sd : Nat) : M n Unit := do
  emit (.cascade (← steps) v sd)
  emit (.write (← steps) v (← bar v) sd .fruitful)
  setBar v sd
  let mut queue : Array (Fin n × Nat) := #[(v, sd)]
  for i in List.range n do
    if hi : i < queue.size then
      let (q, d) := queue[i]                                -- q, d = queue.popleft()
      tick
      emit (.dequeue (← steps) q d)
      for p in G.pred q do
        tick
        if p ∉ (← stack) ∧ (← bar p) > d + 1 then
          emit (.write (← steps) p (← bar p) (d + 1) .drop)
          setBar p (d + 1)
          queue := queue.push (p, d + 1)
    else
      break

/-- Algorithm 2, Search(v); returns sd.  The depth h = |S| - 1 is an explicit argument because
    the termination measure k - h must be visible to Lean: a recursive call is guarded by
    b[w] + h < k, hence h < k. -/
def search (G : Graph n) (t : Fin n) (k : Nat) (v : Fin n) (h : Nat) : M n Nat := do
  push v                                                    -- S.append(v)
  tick
  emit (.enter (← steps) v h)
  let mut sd := k + 1
  for w in G.succ v do
    tick
    if hw : (← bar w) + h < k then
      if w = t then
        tick (h + 2)
        emit (.output (← steps) ((← stack).toList ++ [t]))
        sd := 1
      else if w ∉ (← stack) then
        sd := min sd ((← search G t k w (h + 1)) + 1)
  if sd ≤ k ∧ h > 0 then                                    -- early exit at s: no cascade when search(s) returns
    fruitful G v sd
  else
    emit (.write (← steps) v (← bar v) (k - h + 1) .raise)
    setBar v (k - h + 1)
  emit (.exit (← steps) v h sd (decide (sd ≤ k)))
  pop
  return sd
termination_by k - h

/-- Algorithm 1, BS-DFS(G, s, t, k): the complete event trace of a run -/
def bsdfs (G : Graph n) (s t : Fin n) (k : Nat) : List (Ev n) :=
  let run : M n Unit := do
    emit (.start (← steps))
    let _ ← search G t k s 0
    emit (.term (← steps))
  (Id.run (run.run { b := Vector.replicate n 0, S := #[], steps := 0, trace := #[] })).2.trace.toList

/-! ## What the proofs are about -/

/-- the outputs, in order -/
def outputs (tr : List (Ev n)) : List (List (Fin n)) :=
  tr.filterMap fun | .output _ p => some p | _ => none

/-- step stamps of the observable events o_0 = start, o_1 .. o_T = outputs, o_{T+1} = term -/
def obsSteps (tr : List (Ev n)) : List Nat :=
  tr.filterMap fun | .start s | .output s _ | .term s => some s | _ => none

/-- p is a simple s-t path (node list) with at most k edges -/
def Graph.BoundedPath (G : Graph n) (k : Nat) (s t : Fin n) (p : List (Fin n)) : Prop :=
  p.head? = some s ∧ p.getLast? = some t ∧ p.Nodup ∧ p.length ≤ k + 1 ∧ ∀ e ∈ p.zip p.tail, e.2 ∈ G.succ e.1

variable (G : Graph n) (s t : Fin n) (k : Nat)

-- path mode, every output is a simple s-t path with at most k edges: `bsdfs_sound`, proved in Bsdfs/Sound.lean

-- path mode, every such path is output exactly once: `bsdfs_complete_once`, proved in Bsdfs/Complete.lean

-- worst case (v3): every interval (o_τ, o_{τ+1}] costs at most 2k(n+m) steps (3(k+1)(n+m) as submitted, 2(k+1)(n+m) patched):
-- `bsdfs_worst_case_delay`, proved in Bsdfs/WorstCase.lean (without the assumption k ≤ n)

-- amortized (v3, needs the early exit at s): the τ-th observable event happens after at most τ(k+2)(n+m) steps (2τ(k+1)(n+m) as submitted):
-- `bsdfs_amortized_delay`, proved in Bsdfs/Amortized.lean (without the assumptions 0 < k ≤ n)
