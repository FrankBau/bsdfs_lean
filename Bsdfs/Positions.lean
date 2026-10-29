/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.BsdfsExec

/-!
  Reading the trace by position, definitions only: observable events and consecutive pairs of them, the events at a position,
  the stack before a position, and counts over ranges of positions.  Positions are indices into the event list; `Trace.stk tr p`
  is the stack just before the event at p.  Together with `Bsdfs/BsdfsExec.lean` and `Bsdfs/Traps.lean` this is everything the
  statements in `Bsdfs/Challenge.lean` refer to.  The facts about these definitions are proved from `Bsdfs/Tally.lean` on.
-/

variable {n : Nat}

/-- the step stamp of an observable event (start, output, term) -/
def Ev.obs : Ev n → Option Nat
  | .start s | .output s _ | .term s => some s
  | _ => none

namespace Trace
variable (tr : List (Ev n))

/-- the stack before position p: enter pushes, exit pops -/
def stk : Nat → List (Fin n)
  | 0 => []
  | p + 1 =>
    match tr[p]? with
    | some (.enter _ v _) => stk p ++ [v]
    | some (.exit ..) => (stk p).dropLast
    | _ => stk p

/-- number of positions q with lo < q ≤ hi and P q -/
def cnt (P : Nat → Prop) [DecidablePred P] (lo hi : Nat) : Nat :=
  (List.range' (lo + 1) (hi - lo)).countP (fun q => decide (P q))

/-- events at position q, as Booleans for counting -/
def enterAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.enter _ v _) => v == z | _ => false
def deqAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.dequeue _ v _) => v == z | _ => false

end Trace

/-- an observable event (start, output, term) at q -/
def Trace.isObs (tr : List (Ev n)) (q : Nat) : Bool := match tr[q]? with | some e => e.obs.isSome | none => false

/-- a and c are consecutive observable events -/
structure Consec (tr : List (Ev n)) (a c : Nat) : Prop where
  lt : a < c
  bound : c < tr.length
  obs_a : Trace.isObs tr a = true
  obs_c : Trace.isObs tr c = true
  between : ∀ q, a < q → q < c → Trace.isObs tr q = false

/-- entry depth, read off the event -/
def Trace.depthOf (tr : List (Ev n)) (q : Nat) : Nat := match tr[q]? with | some (.enter _ _ h) => h | _ => 0
