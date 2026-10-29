/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.BsdfsExec
import Bsdfs.Traps

/-!
  The main theorems, stated with `sorry` in place of their proofs.  This file and its two imports are all you have to read:
  - `Bsdfs/BsdfsExec.lean`: `Graph`, `Graph.WF`, `Graph.m`, `bsdfs` (with `search`, `fruitful` and the step counter),
    `outputs`, `obsSteps`, `Graph.BoundedPath`;
  - `Bsdfs/Traps.lean`: the example graphs of the lower bounds, `gate`, `gS`, `gT` and `clique`, `cS`, `cT`, and the counts
    `sweepCalls` and `gateD1`.

  None of them contains a proof.  The same theorems, with the same names and statements, are proved in
  `Bsdfs/MainTheorems.lean`; `comparator.json` lets the comparator tool check that the statements match, and
  `CheckChallenge.lean` (run in CI) checks the same without it.
  Nothing imports this file, so `lake build` skips it; build it with `lake build Bsdfs.Challenge`.
-/

namespace BSDFS

/-! ## Upper bounds (path mode, s ≠ t) -/

/-- soundness: every output is a simple s-t path with at most k edges -/
theorem soundness {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hst : s ≠ t) : ∀ p ∈ outputs (bsdfs G s t k), G.BoundedPath k s t p :=
  sorry

/-- completeness: every simple s-t path with at most k edges is output exactly once -/
theorem completeness {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) : ∀ p, G.BoundedPath k s t p → (outputs (bsdfs G s t k)).count p = 1 :=
  sorry

/-- worst-case delay: consecutive observable events (start, outputs, termination) are at most 2k(n + m) steps apart -/
theorem worst_case_delay {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) (hk : 0 < k) :
    ∀ x ∈ (obsSteps (bsdfs G s t k)).zip (obsSteps (bsdfs G s t k)).tail, x.2 - x.1 ≤ 2 * k * (n + G.m) :=
  sorry

/-- amortized delay: the τ-th observable event happens after at most τ(k + 2)(n + m) steps -/
theorem amortized_delay {n : Nat} (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) :
    ∀ τ (hτ : τ < (obsSteps (bsdfs G s t k)).length), (obsSteps (bsdfs G s t k))[τ] ≤ τ * (k + 2) * (n + G.m) :=
  sorry

/-! ## The gate trap Γ_c -/

/-- Γ_c is a valid input of the upper bounds -/
theorem gate_valid (c : Nat) : (gate c).WF := sorry

/-- n + m of Γ_c -/
theorem gate_n_plus_m (c : Nat) (hc : 1 ≤ c) : c + 4 + (gate c).m = c * c + 2 * c + 11 := sorry

/-- the counts in closed form: N(c, L) = 1 + Σ_{i=1}^{c-1} min(i, L) -/
theorem sweepCalls_formula (c L : Nat) : sweepCalls c L 0 = 1 + ((List.range' 1 (c - 1)).map (fun i => min i L)).sum := sorry

/-- the first three observable events of Γ_c: the start at step 0, the outputs s q t at step 7 and s g q t at step 7 + D1 -/
theorem gate_first_events (c k : Nat) (hc : 1 ≤ c) (hk : 6 ≤ k) : ∃ rest, obsSteps (bsdfs (gate c) (gS c) (gT c) k) = [0, 7, 7 + gateD1 c k] ++ rest :=
  sorry

/-- worst case, lower bound: for c ≥ k², two consecutive observable events are at least (2k - 6)(n + m) steps apart -/
theorem worst_case_lower (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) :
    ∃ x ∈ (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).zip (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).tail, (2 * k - 6) * (c + 4 + (gate c).m) ≤ x.2 - x.1 :=
  sorry

/-- the factor 2 of the worst-case bound is optimal: for every p/q < 2 some interval takes at least (p/q) k (n + m) steps -/
theorem worst_case_tight (p q : Nat) (hpq : p < 2 * q) :
    ∃ c k, 0 < k ∧ ∃ x ∈ (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).zip (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).tail, p * k * (c + 4 + (gate c).m) ≤ q * (x.2 - x.1) :=
  sorry

/-- amortized, lower bound: for c ≥ k², the second output comes after at least (2k - 6)(n + m) steps -/
theorem amortized_lower (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) :
    ∃ h : 2 < (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).length, (2 * k - 6) * (c + 4 + (gate c).m) ≤ (obsSteps (bsdfs (gate c) (gS c) (gT c) k))[2] :=
  sorry

/-- the amortized bound is optimal up to lower-order terms: for every p/q < 1 the second output comes after at least
    (p/q) · 2(k + 2)(n + m) steps -/
theorem amortized_tight (p q : Nat) (hpq : p < q) :
    ∃ c k, ∃ h : 2 < (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).length, p * (2 * (k + 2) * (c + 4 + (gate c).m)) ≤ q * (obsSteps (bsdfs (gate c) (gS c) (gT c) k))[2] :=
  sorry

/-! ## The clique trap G_c -/

/-- G_c is a valid input of the upper bounds -/
theorem clique_valid (c : Nat) : (clique c).WF := sorry

/-- n + m of G_c -/
theorem clique_n_plus_m (c : Nat) (hc : 1 ≤ c) : c + 1 + (clique c).m = c * c + 1 := sorry

/-- the run on G_c: no output, the termination after c · N(c, k) steps -/
theorem clique_events (c k : Nat) (hc : 1 ≤ c) : obsSteps (bsdfs (clique c) (cS c) (cT c) k) = [0, c * sweepCalls c k 0] := sorry

/-- for c ≥ k², the first observable event after the start takes at least (k - 1)(n + m) steps -/
theorem clique_lower_bound (k c : Nat) (hk : 2 ≤ k) (hc : k * k ≤ c) :
    ∃ h : 1 < (obsSteps (bsdfs (clique c) (cS c) (cT c) k)).length, (k - 1) * (c + 1 + (clique c).m) ≤ (obsSteps (bsdfs (clique c) (cS c) (cT c) k))[1] :=
  sorry

end BSDFS
