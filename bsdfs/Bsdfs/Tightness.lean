/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Clique
import Bsdfs.WorstCase
import Bsdfs.Amortized

/-!
  Lower bounds, part 4: tightness of the delay bounds.  On the gate trap Γ_c with c ≥ k², the interval (o_1, o_2] costs at least
  (2k - 6)(n + m) steps, against the worst-case bound 2k(n + m) of `bsdfs_worst_case_delay`, and o_2 ≥ (2k - 6)(n + m), against
  the amortized bound 2(k + 2)(n + m) of `bsdfs_amortized_delay` at τ = 2.  So neither factor can be lowered: for every p/q < 2
  some interval exceeds (p/q) k (n + m), and for every p/q < 1 some o_2 exceeds (p/q) 2(k + 2)(n + m).  On the clique trap G_c with
  c ≥ k², the only interval costs at least (k - 1)(n + m), against (k + 2)(n + m) at τ = 1.
-/

/-! ## N(c, L) -/

theorem sum_range'_sub (c : Nat) : ∀ L, L ≤ c → 2 * ((List.range' 1 L).map (fun d => c - d)).sum + L * (L + 1) = 2 * L * c
  | 0, _ => by simp
  | L + 1, hL => by
    have ih := sum_range'_sub c L (by omega)
    rw [List.range'_concat, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    nat_poly

/-- N(c, L) = 1 + L c - L(L + 1)/2 for L < c -/
theorem sweepCalls_closed {c L : Nat} (hL : L ≤ c - 1) : 2 * sweepCalls c L 0 + L * (L + 1) = 2 + 2 * L * c := by
  unfold sweepCalls
  rw [show min L (c - 1) - 0 = L by omega, Nat.zero_add]
  have := sum_range'_sub c L (by omega)
  omega

theorem sum_shift (a : Nat) : ∀ n, n ≤ a → ((List.range' 1 n).map (fun d => a + 1 - d)).sum = ((List.range' 1 n).map (fun d => a - d)).sum + n
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := sum_shift a n (by omega)
    rw [List.range'_concat, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem sum_min (L : Nat) : ∀ m, ((List.range' 1 (min L m)).map (fun d => m + 1 - d)).sum = ((List.range' 1 m).map (fun i => min i L)).sum
  | 0 => by simp
  | m + 1 => by
    have ih := sum_min L m
    rw [List.range'_concat, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases hL : L ≤ m
    · rw [show min L (m + 1) = L by omega, sum_shift (m + 1) L (by omega)]
      rw [show min L m = L by omega] at ih
      omega
    · rw [show min L (m + 1) = m + 1 by omega, List.range'_concat, List.map_append, List.sum_append, sum_shift (m + 1) m (by omega)]
      rw [show min L m = m by omega] at ih
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-- the paper's form (gate_family.tex): N(c, L) = 1 + Σ_{i=1}^{c-1} min(i, L) -/
theorem sweepCalls_eq (c L : Nat) : sweepCalls c L 0 = 1 + ((List.range' 1 (c - 1)).map (fun i => min i L)).sum := by
  unfold sweepCalls
  rw [Nat.sub_zero, Nat.zero_add]
  rcases c with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [← sum_min L m]

/-! ## The gate trap -/

theorem gate_tight_aux (j c N1 N2 : Nat) (H1 : 2 * N1 + (j + 3) * (j + 3 + 1) = 2 + 2 * (j + 3) * c) (H2 : 2 * N2 + (j + 1) * (j + 1 + 1) = 2 + 2 * (j + 1) * c)
    (Hc : (j + 6) * (j + 6) ≤ c) : (2 * (j + 6) - 6) * (c * c + 2 * c + 11) ≤ (c + 1) * (N1 + N2) + 3 * c * c + 4 * c + 21 := by
  have H1c := congrArg (· * c) H1
  have H2c := congrArg (· * c) H2
  have Hcc := Nat.mul_le_mul_right c Hc
  rw [show 2 * (j + 6) - 6 = 2 * j + 6 by omega]
  nat_poly

/-- on Γ_c with c ≥ k², the interval (o_1, o_2] costs at least (2k - 6)(n + m) steps -/
theorem gateD1_ge (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) : (2 * k - 6) * (c + 4 + (gate c).m) ≤ gateD1 c k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
  have h6 : 6 * (j + 6) ≤ (j + 6) * (j + 6) := Nat.mul_le_mul_right _ (by omega)
  rw [gate_size c (by omega)]
  unfold gateD1
  rw [show j + 6 - 3 = j + 3 by omega, show j + 6 - 5 = j + 1 by omega]
  exact gate_tight_aux j c _ _ (sweepCalls_closed (by omega)) (sweepCalls_closed (by omega)) hc

/-- worst case (gate_family.tex): on Γ_c with c ≥ k², two consecutive observable events are at least (2k - 6)(n + m) steps apart -/
theorem gate_worst_case_lower (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) :
    ∃ x ∈ (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).zip (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).tail, (2 * k - 6) * (c + 4 + (gate c).m) ≤ x.2 - x.1 := by
  have h36 : 36 ≤ k * k := Nat.mul_le_mul hk hk
  obtain ⟨rest, h⟩ := gate_interval1 c k (by omega) hk
  refine ⟨(7, 7 + gateD1 c k), by rw [h]; simp, ?_⟩
  have := gateD1_ge k c hk hc
  simp only
  omega

/-- the factor 2 of the worst-case bound 2k(n + m) is optimal: for every p/q < 2 some interval costs at least (p/q) k (n + m) -/
theorem worst_case_ratio (p q : Nat) (hpq : p < 2 * q) :
    ∃ c k, 0 < k ∧ ∃ x ∈ (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).zip (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).tail, p * k * (c + 4 + (gate c).m) ≤ q * (x.2 - x.1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x, hx, hle⟩ := gate_worst_case_lower (6 * (r + 1)) (6 * (r + 1) * (6 * (r + 1))) (by omega) (Nat.le_refl _)
  refine ⟨_, 6 * (r + 1), by omega, x, hx, ?_⟩
  have h1 : p * (6 * (r + 1)) ≤ (r + 1) * (2 * (6 * (r + 1)) - 6) := by
    have h2 : p * (6 * (r + 1)) ≤ (2 * r + 1) * (6 * (r + 1)) := Nat.mul_le_mul_right _ (by omega)
    rw [show 2 * (6 * (r + 1)) - 6 = 12 * r + 6 by omega]
    nat_poly
  calc p * (6 * (r + 1)) * _ ≤ (r + 1) * (2 * (6 * (r + 1)) - 6) * _ := Nat.mul_le_mul_right _ h1
    _ = (r + 1) * ((2 * (6 * (r + 1)) - 6) * _) := Nat.mul_assoc _ _ _
    _ ≤ (r + 1) * (x.2 - x.1) := Nat.mul_le_mul_left _ hle

/-- amortized: on Γ_c with c ≥ k², the second output o_2 comes after at least (2k - 6)(n + m) steps -/
theorem gate_amortized_lower (k c : Nat) (hk : 6 ≤ k) (hc : k * k ≤ c) :
    ∃ h : 2 < (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).length, (2 * k - 6) * (c + 4 + (gate c).m) ≤ (obsSteps (bsdfs (gate c) (gS c) (gT c) k))[2] := by
  have h36 : 36 ≤ k * k := Nat.mul_le_mul hk hk
  obtain ⟨rest, h⟩ := gate_interval1 c k (by omega) hk
  have := gateD1_ge k c hk hc
  refine ⟨by rw [h]; simp, ?_⟩
  simp only [h, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
  omega

/-- the amortized bound τ(k + 2)(n + m) is optimal up to lower-order terms: for every p/q < 1 some o_2 comes after at least
    (p/q) · 2(k + 2)(n + m) steps -/
theorem amortized_ratio (p q : Nat) (hpq : p < q) :
    ∃ c k, ∃ h : 2 < (obsSteps (bsdfs (gate c) (gS c) (gT c) k)).length, p * (2 * (k + 2) * (c + 4 + (gate c).m)) ≤ q * (obsSteps (bsdfs (gate c) (gS c) (gT c) k))[2] := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨h, hle⟩ := gate_amortized_lower (6 * (r + 1)) (6 * (r + 1) * (6 * (r + 1))) (by omega) (Nat.le_refl _)
  refine ⟨_, 6 * (r + 1), h, ?_⟩
  have h1 : p * (2 * (6 * (r + 1) + 2)) ≤ (r + 1) * (2 * (6 * (r + 1)) - 6) := by
    have h2 : p * (2 * (6 * (r + 1) + 2)) ≤ r * (2 * (6 * (r + 1) + 2)) := Nat.mul_le_mul_right _ (by omega)
    rw [show 2 * (6 * (r + 1)) - 6 = 12 * r + 6 by omega]
    nat_poly
  calc p * (2 * (6 * (r + 1) + 2) * _) = p * (2 * (6 * (r + 1) + 2)) * _ := (Nat.mul_assoc _ _ _).symm
    _ ≤ (r + 1) * (2 * (6 * (r + 1)) - 6) * _ := Nat.mul_le_mul_right _ h1
    _ = (r + 1) * ((2 * (6 * (r + 1)) - 6) * _) := Nat.mul_assoc _ _ _
    _ ≤ (r + 1) * _ := Nat.mul_le_mul_left _ hle

/-! ## The clique trap -/

theorem clique_tight_aux (i c N : Nat) (H : 2 * N + (i + 2) * (i + 2 + 1) = 2 + 2 * (i + 2) * c) (Hc0 : (i + 2) * (i + 2) ≤ c) : (i + 1) * (c * c + 1) ≤ c * N := by
  have Hc := congrArg (· * c) H
  have Hcc := Nat.mul_le_mul_right c Hc0
  nat_poly

/-- on G_c with c ≥ k² (k ≥ 2), the only interval costs at least (k - 1)(n + m) steps -/
theorem clique_lower (k c : Nat) (hk : 2 ≤ k) (hc : k * k ≤ c) : (k - 1) * (c + 1 + (clique c).m) ≤ c * sweepCalls c k 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  have h2 : 2 * (i + 2) ≤ (i + 2) * (i + 2) := Nat.mul_le_mul_right _ (by omega)
  rw [clique_size c (by omega), show i + 2 - 1 = i + 1 by omega]
  exact clique_tight_aux i c _ (sweepCalls_closed (by omega)) hc

/-- the clique trap of bsdfs.tex: o_1 = term comes after at least (k - 1)(n + m) steps, against (k + 2)(n + m) at τ = 1 -/
theorem clique_amortized_lower (k c : Nat) (hk : 2 ≤ k) (hc : k * k ≤ c) :
    ∃ h : 1 < (obsSteps (bsdfs (clique c) (cS c) (cT c) k)).length, (k - 1) * (c + 1 + (clique c).m) ≤ (obsSteps (bsdfs (clique c) (cS c) (cT c) k))[1] := by
  have h4 : 4 ≤ k * k := Nat.mul_le_mul hk hk
  have hrun := clique_run c k (by omega)
  refine ⟨by rw [hrun]; simp, ?_⟩
  simp only [hrun, List.getElem_cons_succ, List.getElem_cons_zero]
  exact clique_lower k c hk hc
