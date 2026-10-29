/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Tightness

/-!
  The main theorems in one place.  Each statement is copied from the file that proves it and is proved by that theorem in one line.
  The `#guard_msgs` checks make `lake build` fail if one of them depends on an axiom other than `propext`, `Classical.choice` and
  `Quot.sound` (in particular on `sorryAx`).

  To trust these theorems, read `Bsdfs/Challenge.lean`, which states them with the same names and `sorry`, and the definitions
  it uses, in `Bsdfs/BsdfsExec.lean`, `Bsdfs/Positions.lean` and `Bsdfs/Traps.lean`; `comparator.json` lets the comparator tool check that the
  statements here and there match.

  Everything else in the library is proof, checked by Lean.
-/

namespace BSDFS

/-! ## Upper bounds (path mode, s ≠ t) -/

/-- soundness: every output is a simple s-t path with at most k edges -/
theorem soundness {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hst : s ≠ t) : ∀ p ∈ outputs (bsdfs G s t k), G.BoundedPath k s t p :=
  bsdfs_sound G s t k hst

/-- completeness: every simple s-t path with at most k edges is output exactly once -/
theorem completeness {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) : ∀ p, G.BoundedPath k s t p → (outputs (bsdfs G s t k)).count p = 1 :=
  bsdfs_complete_once G s t k hG hst

/-- worst-case delay: consecutive observable events (start, outputs, termination) are at most 2k(n + m) steps apart -/
theorem worst_case_delay {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) (hk : 0 < k) :
    ∀ x ∈ (obsSteps (bsdfs G s t k)).zip (obsSteps (bsdfs G s t k)).tail, x.2 - x.1 ≤ 2 * k * (n + G.m) :=
  bsdfs_worst_case_delay G s t k hG hst hk

/-- amortized delay: the τ-th observable event happens after at most τ(k + 2)(n + m) steps -/
theorem amortized_delay {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) :
    ∀ τ (hτ : τ < (obsSteps (bsdfs G s t k)).length), (obsSteps (bsdfs G s t k))[τ] ≤ τ * (k + 2) * (n + G.m) :=
  bsdfs_amortized_delay G s t k hG hst

/-! ## Per interval (path mode, s ≠ t): between consecutive observable events a < c -/

/-- Two Entries per Pair: in (a, c], every node z is entered at most twice at the same depth h -/
theorem two_entries {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) {a c : Nat} (hC : Consec (bsdfs G s t k) a c) (z : Fin n) (h : Nat) :
    Trace.cnt (fun q => Trace.enterAt (bsdfs G s t k) z q = true ∧ Trace.depthOf (bsdfs G s t k) q = h) a c ≤ 2 :=
  bsdfs_two_entries G s t k hG hst hC z h

/-- Edge Scans: for every edge (x, y), the calls at x entered in (a, c], the dequeues of y in (a, c] and the frame of x open at
    a are at most 2k together.  These are what scans (x, y), forward and backward; that they bound the scans executed in the
    interval is the paper's argument, not checked here (the trace has no scan events). -/
theorem edge_scans {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) (hk : 0 < k) {a c : Nat} (hC : Consec (bsdfs G s t k) a c) {x y : Fin n} (hxy : y ∈ G.succ x) :
    Trace.cnt (fun q => Trace.enterAt (bsdfs G s t k) x q = true) a c + Trace.cnt (fun q => Trace.deqAt (bsdfs G s t k) y q = true) a c + (if x ∈ Trace.stk (bsdfs G s t k) a then 1 else 0) ≤ 2 * k :=
  bsdfs_edge_scans G s t k hG hst hk hC hxy

/-! ## The gate trap Γ_c -/

/-- Γ_c is a valid input of the upper bounds -/
theorem gate_valid (c : Nat) : (gate c).WF := gate_wf c

/-- n + m of Γ_c -/
theorem gate_n_plus_m (c : Nat) (hc : 1 ≤ c) : c + 4 + (gate c).m = c * c + 2 * c + 11 := gate_size c hc

/-- the counts in closed form: N(c, L) = 1 + Σ_{i=1}^{c-1} min(i, L) -/
theorem sweepCalls_formula (c L : Nat) : sweepCalls c L 0 = 1 + ((List.range' 1 (c - 1)).map (fun i => min i L)).sum := sweepCalls_eq c L

/-- the first three observable events of Γ_c: the start at step 0, the outputs s q t at step 7 and s g q t at step 7 + D1 -/
theorem gate_first_events (c k : Nat) (hc : 1 ≤ c) (hk : 6 ≤ k) : ∃ rest, obsSteps (bsdfs (gate c) (gS c) (gT c) k) = [0, 7, 7 + gateD1 c k] ++ rest :=
  gate_interval1 c k hc hk

/-- worst case, lower bound: for c ≥ k², two consecutive observable events are at least (2k - 6)(n + m) steps apart -/
theorem worst_case_lower (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) :
    ∃ x ∈ (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).zip (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).tail, (2 * k - 6) * (c + 4 + (gate c).m) ≤ x.2 - x.1 :=
  gate_worst_case_lower k c hk hc

/-- the factor 2 of the worst-case bound is optimal: for every p/q < 2 some interval takes at least (p/q) k (n + m) steps -/
theorem worst_case_tight (p q : Nat) (hpq : p < 2 * q) :
    ∃ c k, 0 < k ∧ ∃ x ∈ (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).zip (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).tail, p * k * (c + 4 + (gate c).m) ≤ q * (x.2 - x.1) :=
  worst_case_ratio p q hpq

/-- amortized, lower bound: for c ≥ k², the second output comes after at least (2k - 6)(n + m) steps -/
theorem amortized_lower (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) :
    ∃ h : 2 < (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).length, (2 * k - 6) * (c + 4 + (gate c).m) ≤ (obsSteps (bsdfs (gate c) (gS c) (gT c) k))[2] :=
  gate_amortized_lower k c hk hc

/-- the amortized bound is optimal up to lower-order terms: for every p/q < 1 the second output comes after at least
    (p/q) · 2(k + 2)(n + m) steps -/
theorem amortized_tight (p q : Nat) (hpq : p < q) :
    ∃ c k, ∃ h : 2 < (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).length, p * (2 * (k + 2) * (c + 4 + (gate c).m)) ≤ q * (obsSteps (bsdfs (gate c) (gS c) (gT c) k))[2] :=
  amortized_ratio p q hpq

/-! ## The clique trap G_c -/

/-- G_c is a valid input of the upper bounds -/
theorem clique_valid (c : Nat) : (clique c).WF := clique_wf c

/-- n + m of G_c -/
theorem clique_n_plus_m (c : Nat) (hc : 1 ≤ c) : c + 1 + (clique c).m = c * c + 1 := clique_size c hc

/-- the run on G_c: no output, the termination after c · N(c, k) steps -/
theorem clique_events (c k : Nat) (hc : 1 ≤ c) : obsSteps (bsdfs (clique c) (cS c) (cT c) k) = [0, c * sweepCalls c k 0] := clique_run c k hc

/-- for c ≥ k², the first observable event after the start takes at least (k - 1)(n + m) steps -/
theorem clique_lower_bound (k c : Nat) (hk : 2 ≤ k) (hc : k * k ≤ c) :
    ∃ h : 1 < (obsSteps (bsdfs (clique c) (cS c) (cT c) k)).length, (k - 1) * (c + 1 + (clique c).m) ≤ (obsSteps (bsdfs (clique c) (cS c) (cT c) k))[1] :=
  clique_amortized_lower k c hk hc

end BSDFS

/-! ## Axiom checks -/

/-- info: 'BSDFS.soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.soundness

/-- info: 'BSDFS.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.completeness

/-- info: 'BSDFS.worst_case_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.worst_case_delay

/-- info: 'BSDFS.amortized_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.amortized_delay

/-- info: 'BSDFS.two_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.two_entries

/-- info: 'BSDFS.edge_scans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.edge_scans

/-- info: 'BSDFS.gate_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.gate_valid

/-- info: 'BSDFS.gate_n_plus_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.gate_n_plus_m

/-- info: 'BSDFS.sweepCalls_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.sweepCalls_formula

/-- info: 'BSDFS.gate_first_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.gate_first_events

/-- info: 'BSDFS.worst_case_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.worst_case_lower

/-- info: 'BSDFS.worst_case_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.worst_case_tight

/-- info: 'BSDFS.amortized_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.amortized_lower

/-- info: 'BSDFS.amortized_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.amortized_tight

/-- info: 'BSDFS.clique_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.clique_valid

/-- info: 'BSDFS.clique_n_plus_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.clique_n_plus_m

/-- info: 'BSDFS.clique_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.clique_events

/-- info: 'BSDFS.clique_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BSDFS.clique_lower_bound
