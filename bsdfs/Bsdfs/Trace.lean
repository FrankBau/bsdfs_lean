import Bsdfs.Tally

/-!
  The run as a trace: the stack and the barriers before each position, frames, and counting of events over position ranges.
  Positions are indices into the event list; `stk tr p` and `bar tr p z` describe the state just before the event at p.
-/

variable {n : Nat}

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

/-- the barrier of z before position p -/
def bar : Nat → Fin n → Nat
  | 0, _ => 0
  | p + 1, z =>
    match tr[p]? with
    | some (.write _ x _ nw _) => if x = z then nw else bar p z
    | _ => bar p z

/-- the frame entered at e (an enter event) is open at the positions e+1 .. x and its exit event is at x -/
def Frame (e x : Nat) : Prop :=
  e < x ∧ (∃ σ v h, tr[e]? = some (.enter σ v h)) ∧ (∃ σ v h sd f, tr[x]? = some (.exit σ v h sd f)) ∧
    (stk tr (x + 1)).length = (stk tr e).length ∧ ∀ q, e < q → q ≤ x → (stk tr e).length < (stk tr q).length

/-- number of positions q with lo < q ≤ hi and P q -/
def cnt (P : Nat → Prop) [DecidablePred P] (lo hi : Nat) : Nat :=
  (List.range' (lo + 1) (hi - lo)).countP (fun q => decide (P q))

end Trace

open Trace

section lemmas
variable {tr : List (Ev n)}

theorem Trace.stk_succ (p : Nat) : stk tr (p + 1) = match tr[p]? with
    | some (.enter _ v _) => stk tr p ++ [v]
    | some (.exit ..) => (stk tr p).dropLast
    | _ => stk tr p := rfl

theorem Trace.bar_succ (p : Nat) (z : Fin n) : bar tr (p + 1) z = match tr[p]? with
    | some (.write _ x _ nw _) => if x = z then nw else bar tr p z
    | _ => bar tr p z := rfl

theorem Trace.stk_succ_enter {p : Nat} {σ : Nat} {v : Fin n} {h : Nat} (hp : tr[p]? = some (.enter σ v h)) : stk tr (p + 1) = stk tr p ++ [v] := by
  simp [stk, hp]

theorem Trace.stk_succ_exit {p : Nat} {σ : Nat} {v : Fin n} {h sd : Nat} {f : Bool} (hp : tr[p]? = some (.exit σ v h sd f)) : stk tr (p + 1) = (stk tr p).dropLast := by
  simp [stk, hp]

theorem Trace.stk_succ_other {p : Nat} (h1 : ∀ σ v h, tr[p]? ≠ some (.enter σ v h)) (h2 : ∀ σ v h sd f, tr[p]? ≠ some (.exit σ v h sd f)) : stk tr (p + 1) = stk tr p := by
  rw [Trace.stk_succ]
  split
  · next heq => exact absurd heq (h1 _ _ _)
  · next heq => exact absurd heq (h2 _ _ _ _ _)
  · rfl

theorem Trace.bar_succ_write {p : Nat} {σ : Nat} {x : Fin n} {o nw : Nat} {kd : Kind} (hp : tr[p]? = some (.write σ x o nw kd)) (z : Fin n) : bar tr (p + 1) z = if x = z then nw else bar tr p z := by
  simp [bar, hp]

theorem Trace.bar_succ_other {p : Nat} (h1 : ∀ σ x o nw kd, tr[p]? ≠ some (.write σ x o nw kd)) (z : Fin n) : bar tr (p + 1) z = bar tr p z := by
  rw [Trace.bar_succ]
  split
  · next heq => exact absurd heq (h1 _ _ _ _ _)
  · rfl

/-- the stack size changes by at most one per position -/
theorem Trace.stk_length_succ (p : Nat) : (stk tr (p + 1)).length ≤ (stk tr p).length + 1 ∧ (stk tr p).length ≤ (stk tr (p + 1)).length + 1 := by
  rw [Trace.stk_succ]
  split <;> simp <;> omega

/-- while the stack never gets shorter than r, its bottom r entries stay put -/
theorem Trace.stk_take_persist {p q r : Nat} (hpq : p ≤ q) (hr : ∀ i, p ≤ i → i ≤ q → r ≤ (stk tr i).length) : (stk tr q).take r = (stk tr p).take r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  clear hpq
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← ih (fun i h1 h2 => hr i h1 (by omega))]
    have hq := hr (p + d) (by omega) (by omega)
    have hq1 := hr (p + d + 1) (by omega) (by omega)
    rw [show p + (d + 1) = p + d + 1 by omega, Trace.stk_succ]
    rw [Trace.stk_succ] at hq1
    split
    · simp [List.take_append_of_le_length hq]
    · next heq =>
      simp only [heq] at hq1
      rw [List.dropLast_eq_take, List.take_take]
      congr 1
      simp at hq1
      omega
    · rfl

end lemmas

namespace Trace
variable (tr : List (Ev n))

/-- events at position q, as Booleans for counting -/
def enterAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.enter _ v _) => v == z | _ => false
def deqAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.dequeue _ v _) => v == z | _ => false
def dropAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.write _ x _ _ .drop) => x == z | _ => false
def fruitAt (z : Fin n) (q : Nat) : Bool := match tr[q]? with | some (.write _ x _ _ .fruitful) => x == z | _ => false

/-- some position q with lo < q ≤ hi satisfies P -/
def anyIn (P : Nat → Bool) (lo hi : Nat) : Bool := (List.range' (lo + 1) (hi - lo)).any P

end Trace

section lemmas2
variable {tr : List (Ev n)}

theorem Trace.enterAt_iff {z : Fin n} {q : Nat} : enterAt tr z q = true ↔ ∃ σ h, tr[q]? = some (.enter σ z h) := by
  unfold enterAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e <;> simp

theorem Trace.deqAt_iff {z : Fin n} {q : Nat} : deqAt tr z q = true ↔ ∃ σ d, tr[q]? = some (.dequeue σ z d) := by
  unfold deqAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e <;> simp

theorem Trace.dropAt_iff {z : Fin n} {q : Nat} : dropAt tr z q = true ↔ ∃ σ o nw, tr[q]? = some (.write σ z o nw .drop) := by
  unfold dropAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e with
    | write σ x o nw kd => cases kd <;> simp
    | _ => simp

theorem Trace.fruitAt_iff {z : Fin n} {q : Nat} : fruitAt tr z q = true ↔ ∃ σ o nw, tr[q]? = some (.write σ z o nw .fruitful) := by
  unfold fruitAt
  cases h : tr[q]? with
  | none => simp
  | some e => cases e with
    | write σ x o nw kd => cases kd <;> simp
    | _ => simp

theorem Trace.anyIn_iff {P : Nat → Bool} {lo hi : Nat} : anyIn P lo hi = true ↔ ∃ q, lo < q ∧ q ≤ hi ∧ P q = true := by
  unfold anyIn
  simp only [List.any_eq_true, List.mem_range'_1]
  constructor
  · rintro ⟨q, ⟨h1, h2⟩, h3⟩; exact ⟨q, by omega, by omega, h3⟩
  · rintro ⟨q, h1, h2, h3⟩; exact ⟨q, ⟨by omega, by omega⟩, h3⟩

theorem Trace.cnt_split (P : Nat → Prop) [DecidablePred P] {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) : cnt P lo hi = cnt P lo mid + cnt P mid hi := by
  unfold cnt
  have : List.range' (lo + 1) (hi - lo) = List.range' (lo + 1) (mid - lo) ++ List.range' (mid + 1) (hi - mid) := by
    rw [show mid + 1 = lo + 1 + (mid - lo) by omega, List.range'_append_1]; congr 1; omega
  rw [this, List.countP_append]

theorem Trace.cnt_zero (P : Nat → Prop) [DecidablePred P] {lo hi : Nat} (h : ∀ q, lo < q → q ≤ hi → ¬ P q) : cnt P lo hi = 0 := by
  unfold cnt
  rw [List.countP_eq_zero]
  intro q hq
  simp only [List.mem_range'_1] at hq
  simpa using h q (by omega) (by omega)

theorem Trace.cnt_mono {P Q : Nat → Prop} [DecidablePred P] [DecidablePred Q] {lo hi : Nat} (h : ∀ q, lo < q → q ≤ hi → P q → Q q) : cnt P lo hi ≤ cnt Q lo hi := by
  unfold cnt
  apply List.countP_mono_left
  intro q hq hP
  simp only [List.mem_range'_1] at hq
  simpa using h q (by omega) (by omega) (by simpa using hP)

theorem nodup_map_of_inj {α β : Type} {l : List α} {f : α → β} (hl : l.Nodup) (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun a ha b hb => hf a (by simp [ha]) b (by simp [hb]))⟩
    intro hx
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hx
    exact hl.1 (by rw [hf x (by simp) y (by simp [hy]) hfy.symm]; exact hy)

/-- positions with pairwise distinct depths in [A, B] number at most B + 1 - A -/
theorem Trace.cnt_le_of_depth (P : Nat → Prop) [DecidablePred P] (d : Nat → Nat) {lo hi A B : Nat} (hrange : ∀ q, lo < q → q ≤ hi → P q → A ≤ d q ∧ d q ≤ B) (hinj : ∀ q₁ q₂, lo < q₁ → q₁ ≤ hi → lo < q₂ → q₂ ≤ hi → P q₁ → P q₂ → d q₁ = d q₂ → q₁ = q₂) : cnt P lo hi ≤ B + 1 - A := by
  unfold cnt
  rw [List.countP_eq_length_filter]
  have hmem : ∀ q ∈ (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q)), lo < q ∧ q ≤ hi ∧ P q := by
    intro q hq
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hq
    exact ⟨by omega, by omega, hq.2⟩
  have hnd : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).Nodup := (List.nodup_range' (step := 1)).filter _
  have hnd' := nodup_map_of_inj (f := d) hnd (fun q₁ hq₁ q₂ hq₂ heq => by
    obtain ⟨a1, b1, c1⟩ := hmem q₁ hq₁
    obtain ⟨a2, b2, c2⟩ := hmem q₂ hq₂
    exact hinj q₁ q₂ a1 b1 a2 b2 c1 c2 heq)
  have hsub : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).map d ⊆ List.range' A (B + 1 - A) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a1, b1, c1⟩ := hmem q hq
    have := hrange q a1 b1 c1
    simp only [List.mem_range'_1]; omega
  have := hnd'.length_le_of_subset hsub
  simpa using this

end lemmas2

section lemmas3
variable {tr : List (Ev n)}

theorem Trace.bar_succ_cases (q : Nat) (z : Fin n) : bar tr (q + 1) z = bar tr q z ∨ ∃ σ o nw kd, tr[q]? = some (.write σ z o nw kd) ∧ bar tr (q + 1) z = nw := by
  rw [Trace.bar_succ]
  split
  · next σ x o nw kd heq =>
    by_cases hxz : x = z
    · subst hxz; right; exact ⟨σ, o, nw, kd, heq, by simp⟩
    · left; simp [hxz]
  · left; rfl

/-- if no write to z in [p₁, p₂) raises it, the barrier does not grow -/
theorem Trace.bar_le_of_lowering {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (h : ∀ q σ o nw kd, p₁ ≤ q → q < p₂ → tr[q]? = some (.write σ z o nw kd) → nw ≤ bar tr q z) : bar tr p₂ z ≤ bar tr p₁ z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have ih' := ih (fun q σ o nw kd h1 h2 hq => h q σ o nw kd h1 (by omega) hq)
    rw [show p₁ + (d + 1) = p₁ + d + 1 by omega]
    rcases Trace.bar_succ_cases (tr := tr) (p₁ + d) z with he | ⟨σ, o, nw, kd, hq, he⟩
    · rw [he]; exact ih'
    · rw [he]; exact Nat.le_trans (h _ σ o nw kd (by omega) (by omega) hq) ih'

/-- if no write to z in [p₁, p₂) lowers it, the barrier does not shrink -/
theorem Trace.bar_ge_of_raising {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (h : ∀ q σ o nw kd, p₁ ≤ q → q < p₂ → tr[q]? = some (.write σ z o nw kd) → bar tr q z ≤ nw) : bar tr p₁ z ≤ bar tr p₂ z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have ih' := ih (fun q σ o nw kd h1 h2 hq => h q σ o nw kd h1 (by omega) hq)
    rw [show p₁ + (d + 1) = p₁ + d + 1 by omega]
    rcases Trace.bar_succ_cases (tr := tr) (p₁ + d) z with he | ⟨σ, o, nw, kd, hq, he⟩
    · rw [he]; exact ih'
    · rw [he]; exact Nat.le_trans ih' (h _ σ o nw kd (by omega) (by omega) hq)

theorem Trace.bar_succ_of_write {q : Nat} {σ : Nat} {z : Fin n} {o nw : Nat} {kd : Kind} (hq : tr[q]? = some (.write σ z o nw kd)) : bar tr (q + 1) z = nw := by
  rw [Trace.bar_succ_write hq]; simp

/-- a node off the stack stays off until it is entered -/
theorem Trace.not_mem_stk_of_no_enter {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (hz : z ∉ stk tr p₁) (h : ∀ q, p₁ ≤ q → q < p₂ → enterAt tr z q = false) : z ∉ stk tr p₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => exact hz
  | succ d ih =>
    have ih' := ih (fun q h1 h2 => h q h1 (by omega))
    have hq := h (p₁ + d) (by omega) (by omega)
    rw [show p₁ + (d + 1) = p₁ + d + 1 by omega, Trace.stk_succ]
    split
    · next σ v hh heq =>
      have hvz : v ≠ z := by
        intro hvz; subst hvz
        have : enterAt tr v (p₁ + d) = true := Trace.enterAt_iff.mpr ⟨σ, hh, heq⟩
        rw [hq] at this; exact Bool.false_ne_true this
      simp [ih', hvz.symm]
    · exact fun hm => ih' ((List.dropLast_sublist _).subset hm)
    · exact ih'

/-- if enters only push nodes off the stack, the stack has no repetitions -/
theorem Trace.stk_nodup (h : ∀ q σ v hh, tr[q]? = some (.enter σ v hh) → v ∉ stk tr q) : ∀ p, (stk tr p).Nodup := by
  intro p
  induction p with
  | zero => simp [stk]
  | succ p ih =>
    rw [Trace.stk_succ]
    split
    · next σ v hh heq => exact List.nodup_append.mpr ⟨ih, by simp, fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact h _ _ _ _ heq ha⟩
    · exact ih.sublist (List.dropLast_sublist _)
    · exact ih

end lemmas3

section lemmas4
variable {tr : List (Ev n)}

/-- without writes to z in [p₁, p₂), the barrier of z is unchanged -/
theorem Trace.bar_eq_of_no_write {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (h : ∀ q σ o nw kd, p₁ ≤ q → q < p₂ → tr[q]? ≠ some (.write σ z o nw kd)) : bar tr p₂ z = bar tr p₁ z :=
  Nat.le_antisymm (Trace.bar_le_of_lowering hp (fun q σ o nw kd h1 h2 hq => absurd hq (h q σ o nw kd h1 h2)))
    (Trace.bar_ge_of_raising hp (fun q σ o nw kd h1 h2 hq => absurd hq (h q σ o nw kd h1 h2)))

/-- if every write to z in [p₁, p₂) lowers it or writes at most C, the barrier stays at most max(start, C) -/
theorem Trace.bar_le_max {z : Fin n} {p₁ p₂ C : Nat} (hp : p₁ ≤ p₂) (h : ∀ q σ o nw kd, p₁ ≤ q → q < p₂ → tr[q]? = some (.write σ z o nw kd) → nw ≤ bar tr q z ∨ nw ≤ C) : bar tr p₂ z ≤ max (bar tr p₁ z) C := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => exact Nat.le_max_left _ _
  | succ d ih =>
    have ih' := ih (fun q σ o nw kd h1 h2 hq => h q σ o nw kd h1 (by omega) hq)
    rw [show p₁ + (d + 1) = p₁ + d + 1 by omega]
    rcases Trace.bar_succ_cases (tr := tr) (p₁ + d) z with he | ⟨σ, o, nw, kd, hq, he⟩
    · rw [he]; exact ih'
    · rw [he]
      rcases h _ σ o nw kd (by omega) (by omega) hq with h1 | h1
      · exact Nat.le_trans h1 ih'
      · exact Nat.le_trans h1 (Nat.le_max_right _ _)

/-- the event at q is not a write when it is an exit -/
theorem Trace.not_write_of_exit {q σ : Nat} {v : Fin n} {h sd : Nat} {f : Bool} (hq : tr[q]? = some (.exit σ v h sd f)) (z : Fin n) : bar tr (q + 1) z = bar tr q z :=
  Trace.bar_succ_other (fun σ' x o nw kd hw => by rw [hq] at hw; cases hw) z

end lemmas4

section lemmas5
variable {tr : List (Ev n)}

/-- the first position in (lo, q] with P -/
theorem Trace.exists_first {P : Nat → Prop} {lo : Nat} : ∀ q, lo < q → P q → ∃ q₀, lo < q₀ ∧ q₀ ≤ q ∧ P q₀ ∧ ∀ q', lo < q' → q' < q₀ → ¬ P q'
  | q, h1, h2 => by
    by_cases hex : ∃ q', lo < q' ∧ q' < q ∧ P q'
    · obtain ⟨q', a1, a2, a3⟩ := hex
      obtain ⟨q₀, b1, b2, b3, b4⟩ := Trace.exists_first q' a1 a3
      exact ⟨q₀, b1, by omega, b3, b4⟩
    · exact ⟨q, h1, Nat.le_refl _, h2, fun q' a1 a2 a3 => hex ⟨q', a1, a2, a3⟩⟩
termination_by q => q

/-- the last position in [q, hi] with P -/
theorem Trace.exists_last {P : Nat → Prop} {hi : Nat} : ∀ q, q ≤ hi → P q → ∃ q₀, q ≤ q₀ ∧ q₀ ≤ hi ∧ P q₀ ∧ ∀ q', q₀ < q' → q' ≤ hi → ¬ P q'
  | q, h1, h2 => by
    by_cases hex : ∃ q', q < q' ∧ q' ≤ hi ∧ P q'
    · obtain ⟨q', a1, a2, a3⟩ := hex
      obtain ⟨q₀, b1, b2, b3, b4⟩ := Trace.exists_last q' a2 a3
      exact ⟨q₀, by omega, b2, b3, b4⟩
    · exact ⟨q, Nat.le_refl _, h1, h2, fun q' a1 a2 a3 => hex ⟨q', a1, a2, a3⟩⟩
termination_by q => hi - q

/-- a position with P minimizing d -/
theorem Trace.exists_min {P : Nat → Prop} (d : Nat → Nat) : ∀ q, P q → ∃ q₀, P q₀ ∧ ∀ q', P q' → d q₀ ≤ d q'
  | q, h => by
    by_cases hex : ∃ q', P q' ∧ d q' < d q
    · obtain ⟨q', a1, a2⟩ := hex
      exact Trace.exists_min d q' a1
    · exact ⟨q, h, fun q' hq' => Nat.le_of_not_lt fun hlt => hex ⟨q', hq', hlt⟩⟩
termination_by q => d q

/-- an empty stack stays empty without entries, if exits never happen on an empty stack -/
theorem Trace.stk_nil_of_no_enter {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (h0 : stk tr p₁ = []) (hexit : ∀ q σ v h sd f, tr[q]? = some (.exit σ v h sd f) → stk tr q ≠ []) (h : ∀ q, p₁ ≤ q → q < p₂ → ∀ σ v h, tr[q]? ≠ some (.enter σ v h)) : stk tr p₂ = [] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction d with
  | zero => exact h0
  | succ d ih =>
    have ih' := ih (fun q h1 h2 => h q h1 (by omega))
    rw [show p₁ + (d + 1) = p₁ + d + 1 by omega, Trace.stk_succ]
    split
    · next σ v hh heq => exact absurd heq (h _ (by omega) (by omega) σ v hh)
    · next σ v hh sd f heq => exact absurd ih' (hexit _ σ v hh sd f heq)
    · exact ih'

end lemmas5

section frames
variable {tr : List (Ev n)}

theorem Trace.Frame.push {e x : Nat} (h : Frame tr e x) : (stk tr (e + 1)).length = (stk tr e).length + 1 := by
  obtain ⟨-, ⟨σ, v, hh, he⟩, -⟩ := h
  rw [Trace.stk_succ_enter he]; simp

theorem Trace.Frame.isOpen {e x q : Nat} (h : Frame tr e x) (h1 : e < q) (h2 : q ≤ x) : (stk tr e).length + 1 ≤ (stk tr q).length :=
  h.2.2.2.2 q h1 h2

theorem Trace.Frame.prefix {e x q : Nat} (h : Frame tr e x) (h1 : e < q) (h2 : q ≤ x) : (stk tr q).take ((stk tr e).length + 1) = stk tr (e + 1) := by
  rw [Trace.stk_take_persist (p := e + 1) h1 (fun i hi1 hi2 => h.isOpen (by omega) (by omega)), ← h.push, List.take_length]

/-- at its exit event the frame's own stack is back on top -/
theorem Trace.Frame.at_exit {e x : Nat} (h : Frame tr e x) : stk tr x = stk tr (e + 1) := by
  have hex := h.1
  obtain ⟨σ, v, hh, sd, f, hx⟩ := h.2.2.1
  have hsz := h.2.2.2.1
  have h1 := Trace.stk_succ_exit hx
  have h2 := h.isOpen hex (Nat.le_refl x)
  have hlen : (stk tr x).length = (stk tr e).length + 1 := by
    rw [h1, List.length_dropLast] at hsz; omega
  have := h.prefix hex (Nat.le_refl x)
  rw [← hlen, List.take_length] at this
  exact this

/-- frames are nested: a frame entered inside another one exits before it -/
theorem Trace.Frame.nest {e₁ x₁ e₂ x₂ : Nat} (h₁ : Frame tr e₁ x₁) (h₂ : Frame tr e₂ x₂) (h12 : e₁ < e₂) (h21 : e₂ ≤ x₁) : x₂ < x₁ ∧ (stk tr e₁).length < (stk tr e₂).length := by
  have hlt : (stk tr e₁).length < (stk tr e₂).length := by have := h₁.isOpen h12 h21; omega
  refine ⟨?_, hlt⟩
  refine Nat.lt_of_not_le fun hle => ?_
  have hne : e₂ ≠ x₁ := by
    intro heq; subst heq
    obtain ⟨-, ⟨σ, v, hh, he⟩, -⟩ := h₂
    obtain ⟨-, -, ⟨σ', v', hh', sd, f, hx⟩, -⟩ := h₁
    rw [he] at hx; cases hx
  have hx1 := h₁.2.2.2.1
  rcases Nat.lt_or_ge (x₁ + 1) (x₂ + 1) with h | h
  · have := h₂.isOpen (q := x₁ + 1) (by omega) (by omega); omega
  · have : x₁ = x₂ := by omega
    subst this
    have := h₂.2.2.2.1
    omega

/-- a frame is determined by its exit -/
theorem Trace.Frame.unique {e e' x : Nat} (h : Frame tr e x) (h' : Frame tr e' x) : e = e' := by
  have hs := h.2.2.2.1
  have hs' := h'.2.2.2.1
  rcases Nat.lt_trichotomy e e' with hlt | heq | hgt
  · have := h.isOpen hlt (Nat.le_of_lt h'.1); omega
  · exact heq
  · have := h'.isOpen hgt (Nat.le_of_lt h.1); omega

end frames
