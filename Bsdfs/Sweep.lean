/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Basic
import Bsdfs.Traps

/-!
  Lower bounds, part 1: specs of `search` that compute exact step counts.  Generic facts (the trace only grows; a call whose
  successors are all pruned or on the stack costs 1 + |succ v| and raises b[v]), and the Sweep lemma of gate_family.tex
  (the clique-trap run of bsdfs.tex, shifted in depth and barrier): a block of c nodes, each scanning the other block nodes
  in index order and then nodes X that stay on the stack, swept from B_0 with bound L, costs (c + |X|) · N(c, L) steps.
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

theorem obsSteps_append (A B : List (Ev n)) : obsSteps (A ++ B) = obsSteps A ++ obsSteps B := by
  simp [obsSteps, List.filterMap_append]

theorem ext_push {T0 L : List (Ev n)} {e : Ev n} (h : ∃ E, L = T0 ++ E) : ∃ E, L ++ [e] = T0 ++ E := by
  obtain ⟨E, rfl⟩ := h; exact ⟨E ++ [e], by simp⟩

theorem ext_obs_push {T0 L : List (Ev n)} {e : Ev n} (h : ∃ E, L = T0 ++ E ∧ obsSteps E = []) (he : obsSteps [e] = []) : ∃ E, L ++ [e] = T0 ++ E ∧ obsSteps E = [] := by
  obtain ⟨E, rfl, hE⟩ := h; exact ⟨E ++ [e], by simp, by rw [obsSteps_append, hE, he]; rfl⟩

theorem ext_trans {T0 L M : List (Ev n)} (h1 : ∃ E, L = M ++ E) (h2 : ∃ E, M = T0 ++ E) : ∃ E, L = T0 ++ E := by
  obtain ⟨E1, rfl⟩ := h1; obtain ⟨E2, rfl⟩ := h2; exact ⟨E2 ++ E1, by simp⟩

theorem vset_fin (b : Vector Nat n) (p : Fin n) (c : Nat) (z : Fin n) : (b.set p.1 c p.2)[z] = if p = z then c else b[z] := by
  simp only [Fin.getElem_fin]
  rw [Vector.getElem_set]
  simp [Fin.val_inj]

/-! ## The trace only grows -/

theorem fruitful_ext (G : Graph n) (v : Fin n) (sd : Nat) (T0 : List (Ev n)) :
    ⦃fun st => ⌜st.trace.toList = T0⌝⦄ fruitful G v sd ⦃⇓ _ st => ⌜∃ E, st.trace.toList = T0 ++ E⌝⦄ := by
  mvcgen [fruitful, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack] invariants
  · ⇓⟨_, _⟩ st => ⌜∃ E, st.trace.toList = T0 ++ E⌝
  · ⇓⟨_, _⟩ st => ⌜∃ E, st.trace.toList = T0 ++ E⌝
  all_goals
    simp +zetaDelta only [Array.toList_push] at *
    repeat apply ext_push
    first | assumption | (refine ⟨[], ?_⟩; simp_all; done)

theorem search_ext (G : Graph n) (t : Fin n) (k h : Nat) (v : Fin n) (T0 : List (Ev n)) :
    ⦃fun st => ⌜st.trace.toList = T0⌝⦄ search G t k v h ⦃⇓ _ st => ⌜∃ E, st.trace.toList = T0 ++ E⌝⦄ := by
  have ih : ∀ w (T1 : List (Ev n)), ⦃fun st => ⌜st.trace.toList = T1 ∧ h < k⌝⦄ search G t k w (h + 1) ⦃⇓ _ st => ⌜∃ E, st.trace.toList = T1 ++ E⌝⦄ := by
    intro w T1
    by_cases hk : h < k
    · intro st hst; exact search_ext G t k (h + 1) w T1 st hst.1
    · intro st hst; exact absurd hst.2 hk
  have hcasc := fruitful_ext G v
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, ih, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜∃ E, st.trace.toList = T0 ++ E⌝
  case vc2.step.isTrue.isFalse.isTrue.pre =>
    have := ‹_ + h < k›
    simp +zetaDelta only at this
    exact ⟨trivial, by omega⟩
  all_goals
    simp +zetaDelta only [Array.toList_push] at *
    repeat apply ext_push
    first | assumption | (apply ext_trans <;> assumption) | (refine ⟨[], ?_⟩; simp_all; done)
termination_by k - h

/-! ## Leaf calls -/

/-- a call whose successors are all pruned or on the stack (and not t): 1 + |succ v| steps, the raise, no observable event -/
theorem search_leaf (G : Graph n) (t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n))
    (hleaf : ∀ w ∈ G.succ v, k ≤ b0[w] + h ∨ (w ≠ t ∧ w ∈ (S0.push v).toList)) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.steps = σ0 ∧ st.trace.toList = T0⌝⦄
    search G t k v h
    ⦃⇓ r st => ⌜r = k + 1 ∧ st.S = S0 ∧ st.b = b0.set v.1 (k - h + 1) v.2 ∧ st.steps = σ0 + 1 + (G.succ v).length ∧ ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []⌝⦄ := by
  have hrec : ∀ w, ⦃fun _ => ⌜False⌝⦄ search G t k w (h + 1) ⦃⇓ _ _ => ⌜True⌝⦄ := fun w s hs => hs.elim
  have hcasc := fruitful_ext G v
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hrec, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜st.S = S0.push v ∧ st.b = b0 ∧ sd = k + 1 ∧ st.steps = σ0 + 1 + xs.prefix.length ∧ ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []⌝
  case vc1.step.isTrue.isTrue =>
    obtain ⟨hS, hb, -, -, -⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have htest := ‹_ + h < k›
    have hcur := ‹_ = t›
    simp +zetaDelta only at htest
    rw [hb] at htest
    rcases hleaf _ hmem with h1 | ⟨h1, -⟩
    · omega
    · exact absurd hcur h1
  case vc2.step.isTrue.isFalse.isTrue.pre =>
    obtain ⟨hS, hb, -, -, -⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have htest := ‹_ + h < k›
    have hnS := ‹¬_ ∈ _›
    simp +zetaDelta only at htest hnS
    rw [hb] at htest
    rw [hS] at hnS
    rcases hleaf _ hmem with h1 | ⟨-, h2⟩
    · omega
    · exact hnS (by simpa using h2)
  case vc3.step.isTrue.isFalse.isTrue.post.success =>
    obtain ⟨hS, hb, -, -, -⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have htest := ‹_ + h < k›
    have hnS := ‹¬_ ∈ _›
    simp +zetaDelta only at htest hnS
    rw [hb] at htest
    rw [hS] at hnS
    exfalso
    rcases hleaf _ hmem with h1 | ⟨-, h2⟩
    · omega
    · exact hnS (by simpa using h2)
  case vc4.step.isTrue.isFalse.isFalse =>
    obtain ⟨hS, hb, hsd, hσ, E, hE, hobs⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    simp +zetaDelta only
    refine ⟨hS, hb, hsd, ?_, E, hE, hobs⟩
    simp only [List.length_append, List.length_singleton]; omega
  case vc5.step.isFalse =>
    obtain ⟨hS, hb, hsd, hσ, E, hE, hobs⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    simp +zetaDelta only
    refine ⟨hS, hb, hsd, ?_, E, hE, hobs⟩
    simp only [List.length_append, List.length_singleton]; omega
  case vc6.pre =>
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = σ0 ∧ _ = T0›
    simp +zetaDelta only
    refine ⟨by rw [hS], hb, trivial, by simp [hσ], _, by rw [Array.toList_push, hT], by simp [obsSteps]⟩
  case vc7.post.success.isTrue.post.success =>
    obtain ⟨-, -, hsd, -, -⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    have hc := ‹_ ≤ k ∧ h > 0›
    omega
  case vc8.post.success.isFalse =>
    obtain ⟨hS, hb, hsd, hσ, E, hE, hobs⟩ := ‹_ = S0.push v ∧ _ = b0 ∧ _ ∧ _ ∧ _›
    simp +zetaDelta only
    refine ⟨hsd, by rw [hS]; simp, by rw [hb], hσ, ?_⟩
    simp only [Array.toList_push]
    refine ext_obs_push (ext_obs_push ⟨E, hE, hobs⟩ ?_) ?_ <;> simp [obsSteps]

/-! ## Lists without duplicates: positions -/

section lists
variable {α : Type}

theorem List.Nodup.getElem_mem_take {l : List α} (hnd : l.Nodup) {i j : Nat} (hj : j < l.length) : l[j] ∈ l.take i ↔ j < i := by
  constructor
  · intro hm
    obtain ⟨m, hm1, hm2⟩ := List.mem_iff_getElem.mp hm
    simp only [List.length_take] at hm1
    rw [List.getElem_take] at hm2
    have := (hnd.getElem_inj (hi := by omega) (hj := hj)).mp hm2
    omega
  · intro hji
    exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by rw [List.getElem_take]⟩

theorem List.Nodup.getElem_mem_drop {l : List α} (hnd : l.Nodup) {i j : Nat} (hj : j < l.length) : l[j] ∈ l.drop i ↔ i ≤ j := by
  constructor
  · intro hm
    obtain ⟨m, hm1, hm2⟩ := List.mem_iff_getElem.mp hm
    simp only [List.length_drop] at hm1
    rw [List.getElem_drop] at hm2
    have := (hnd.getElem_inj (hi := by omega) (hj := hj)).mp hm2
    omega
  · intro hij
    exact List.mem_iff_getElem.mpr ⟨j - i, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩

theorem List.exists_of_mem_take {l : List α} {i : Nat} {u : α} (hu : u ∈ l.take i) : ∃ m, ∃ hm : m < l.length, m < i ∧ l[m] = u := by
  obtain ⟨m, hm1, hm2⟩ := List.mem_iff_getElem.mp hu
  simp only [List.length_take] at hm1
  exact ⟨m, by omega, by omega, by rw [← hm2, List.getElem_take]⟩

theorem List.exists_of_mem_drop {l : List α} {i : Nat} {u : α} (hu : u ∈ l.drop i) : ∃ m, ∃ hm : m < l.length, i ≤ m ∧ l[m] = u := by
  obtain ⟨m, hm1, hm2⟩ := List.mem_iff_getElem.mp hu
  simp only [List.length_drop] at hm1
  exact ⟨i + m, by omega, by omega, by rw [← hm2, List.getElem_drop]⟩

/-- the successor list of B_h, read by position -/
theorem succ_list_idx (l X : List α) {h : Nat} (hh : h < l.length) (p : Nat) :
    (l.take h ++ l.drop (h + 1) ++ X)[p]? = if p < h then l[p]? else if p + 1 < l.length then l[p + 1]? else X[p + 1 - l.length]? := by
  have h1 : (l.take h).length = h := by simp; omega
  have h2 : (l.drop (h + 1)).length = l.length - (h + 1) := by simp
  split
  · rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take_of_lt (by omega)]
  · rw [List.append_assoc, List.getElem?_append_right (by omega), h1]
    split
    · rw [List.getElem?_append_left (by omega), List.getElem?_drop]; congr 1; omega
    · rw [List.getElem?_append_right (by omega), h2]; congr 1; omega

theorem getElem_ne_of_not_mem {l : List α} {x : α} (hx : x ∉ l) (j : Nat) (hj : j < l.length) : l[j] ≠ x :=
  fun he => hx (he ▸ List.getElem_mem hj)

end lists

/-! ## The sweep -/

/-- the block structure of a sweep: B_0 .. B_{c-1} = blk without duplicates, avoiding t; B_i scans the other block nodes in
    index order, then X; X avoids t and the block; the stack prefix P (at depth h0) avoids the block; β + h0 + L = k -/
structure SweepCtx (G : Graph n) (t : Fin n) (k : Nat) (blk X P : List (Fin n)) (h0 β L : Nat) : Prop where
  nodup : blk.Nodup
  t_blk : t ∉ blk
  t_X : t ∉ X
  succ : ∀ i (hi : i < blk.length), G.succ blk[i] = blk.take i ++ blk.drop (i + 1) ++ X
  X_blk : ∀ x ∈ X, x ∉ blk
  P_blk : ∀ x ∈ P, x ∉ blk
  P_len : P.length = h0
  bound : β + h0 + L = k

-- `sweepCalls c L h`, the calls of a sweep from the first call at relative depth h, is defined in Bsdfs/Traps.lean

theorem sweepCalls_last (c L : Nat) : sweepCalls c L (min L (c - 1)) = 1 := by simp [sweepCalls]

theorem sweepCalls_step {c L h : Nat} (hh : h < min L (c - 1)) : sweepCalls c L h = sweepCalls c L (h + 1) + (c - (h + 1)) := by
  unfold sweepCalls
  rw [show min L (c - 1) - h = (min L (c - 1) - (h + 1)) + 1 by omega, List.range'_succ]
  simp only [List.map_cons, List.sum_cons]
  omega

/-- the loop invariant of the first call at relative depth h (node vh = B_h), after its first p successors -/
def sweepInv (blk X : List (Fin n)) (k β L h : Nat) (vh : Fin n) (S1 : Array (Fin n)) (b1 : Vector Nat n) (σ1 : Nat) (T1 : List (Ev n)) (p sd : Nat) (st : St n) : Prop :=
  st.S = S1.push vh ∧ sd = k + 1 ∧
  st.steps = σ1 + 1 + p + (blk.length + X.length) * (if p ≤ h then 0 else sweepCalls blk.length L (h + 1) + (min p (blk.length - 1) - (h + 1))) ∧
  (∀ j (hj : j < blk.length), st.b[blk[j]] = if p ≤ h then b1[blk[j]] else if h < j ∧ j ≤ min p (blk.length - 1) then β + L - h else if min p (blk.length - 1) < j then β + L - h - 1 else b1[blk[j]]) ∧
  (∀ z, z ∉ blk → st.b[z] = b1[z]) ∧
  ∃ E, st.trace.toList = T1 ++ E ∧ obsSteps E = []

/-- the successor of B_h scanned at position p: a block node on the stack, a later block node, or a node of X -/
theorem sweep_pos {blk X : List (Fin n)} {h : Nat} (hlt : h < blk.length) {pref suff : List (Fin n)} {cur : Fin n}
    (hsplit : blk.take h ++ blk.drop (h + 1) ++ X = pref ++ cur :: suff) :
    (∃ hp : pref.length < blk.length, pref.length < h ∧ cur = blk[pref.length]) ∨
      (∃ hp : pref.length + 1 < blk.length, h ≤ pref.length ∧ cur = blk[pref.length + 1]) ∨ (blk.length ≤ pref.length + 1 ∧ cur ∈ X) := by
  have hR : (pref ++ cur :: suff)[pref.length]? = some cur := by simp
  have := congrArg (·[pref.length]?) hsplit
  rw [hR, succ_list_idx blk X hlt] at this
  split at this
  · next h1 =>
    left
    have hp : pref.length < blk.length := by omega
    rw [List.getElem?_eq_getElem hp] at this
    exact ⟨hp, h1, (Option.some.inj this).symm⟩
  · next h1 =>
    split at this
    · next h2 =>
      right; left
      rw [List.getElem?_eq_getElem h2] at this
      exact ⟨h2, by omega, (Option.some.inj this).symm⟩
    · next h2 =>
      right; right
      exact ⟨by omega, List.mem_of_getElem? this⟩

theorem trace_obs_trans {T1 L M : List (Ev n)} {os : List Nat} (h1 : ∃ E, M = T1 ++ E ∧ obsSteps E = os) (h2 : ∃ E, L = M ++ E ∧ obsSteps E = []) : ∃ E, L = T1 ++ E ∧ obsSteps E = os := by
  obtain ⟨E1, rfl, h1⟩ := h1
  obtain ⟨E2, rfl, h2⟩ := h2
  exact ⟨E1 ++ E2, by simp, by rw [obsSteps_append, h1, h2, List.append_nil]⟩

section sweepinv
variable {blk X : List (Fin n)} {k β L h : Nat} {vh : Fin n} {S1 : Array (Fin n)} {b1 : Vector Nat n} {σ1 : Nat} {T1 : List (Ev n)}

/-- a successor on the stack: one more scan -/
theorem sweepInv_skip {p sd : Nat} {st st' : St n} (hinv : sweepInv blk X k β L h vh S1 b1 σ1 T1 p sd st) (hp : p < h ∨ (blk.length ≤ p + 1 ∧ h < p))
    (hS : st'.S = st.S) (hb : st'.b = st.b) (hσ : st'.steps = st.steps + 1) (hT : st'.trace = st.trace) :
    sweepInv blk X k β L h vh S1 b1 σ1 T1 (p + 1) sd st' := by
  obtain ⟨hS0, hsd, hσ0, hbb, hbz, hE⟩ := hinv
  refine ⟨by rw [hS, hS0], hsd, ?_, ?_, fun z hz => by rw [hb, hbz z hz], by rw [hT]; exact hE⟩
  · rw [hσ]
    rcases hp with hp | ⟨hp1, hp2⟩
    · rw [ite_eq_left (show p ≤ h by omega)] at hσ0; rw [ite_eq_left (show p + 1 ≤ h by omega)]; omega
    · rw [ite_eq_right (show ¬ p ≤ h by omega)] at hσ0
      rw [ite_eq_right (show ¬ p + 1 ≤ h by omega), show min (p + 1) (blk.length - 1) = min p (blk.length - 1) by omega]
      omega
  · intro j hj
    rw [hb, hbb j hj]
    rcases hp with hp | ⟨hp1, hp2⟩
    · rw [ite_eq_left (show p ≤ h by omega), ite_eq_left (show p + 1 ≤ h by omega)]
    · rw [ite_eq_right (show ¬ p ≤ h by omega), ite_eq_right (show ¬ p + 1 ≤ h by omega), show min (p + 1) (blk.length - 1) = min p (blk.length - 1) by omega]

/-- the first child B_{h+1}: the sweep one level deeper -/
theorem sweepInv_fresh {sd r : Nat} {st st' : St n} (hinv : sweepInv blk X k β L h vh S1 b1 σ1 T1 h sd st)
    (hhL : h + 1 ≤ L) (hhc : h + 1 < blk.length)
    (hr : r = k + 1) (hS : st'.S = st.S)
    (hb : ∀ j (hj : j < blk.length), st'.b[blk[j]] = if j = h + 1 then β + L - (h + 1) + 1 else if h + 1 < j then β + L - (h + 1) else st.b[blk[j]])
    (hbz : ∀ z, z ∉ blk → st'.b[z] = st.b[z]) (hσ : st'.steps = st.steps + 1 + (blk.length + X.length) * sweepCalls blk.length L (h + 1))
    (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    sweepInv blk X k β L h vh S1 b1 σ1 T1 (h + 1) (min sd (r + 1)) st' := by
  obtain ⟨hS0, hsd, hσ0, hbb, hbz0, hE⟩ := hinv
  refine ⟨by rw [hS, hS0], by omega, ?_, ?_, fun z hz => by rw [hbz z hz, hbz0 z hz], trace_obs_trans hE hT⟩
  · rw [ite_eq_left (Nat.le_refl h), Nat.mul_zero, Nat.add_zero] at hσ0
    rw [hσ, ite_eq_right (show ¬ h + 1 ≤ h by omega), show min (h + 1) (blk.length - 1) - (h + 1) = 0 by omega]
    simp only [Nat.add_zero]
    omega
  · intro j hj
    rw [hb j hj, hbb j hj, ite_eq_left (Nat.le_refl h), ite_eq_right (show ¬ h + 1 ≤ h by omega), show min (h + 1) (blk.length - 1) = h + 1 by omega]
    by_cases h1 : j = h + 1
    · rw [ite_eq_left h1, ite_eq_left (show h < j ∧ j ≤ h + 1 by omega)]; omega
    · rw [ite_eq_right h1]
      by_cases h2 : h + 1 < j
      · rw [ite_eq_left h2, ite_eq_right (show ¬ (h < j ∧ j ≤ h + 1) by omega), ite_eq_left h2]; omega
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (h < j ∧ j ≤ h + 1) by omega), ite_eq_right h2]

/-- a later block node B_{p+1}: a leaf -/
theorem sweepInv_leaf {p sd r : Nat} {st st' : St n} (hinv : sweepInv blk X k β L h vh S1 b1 σ1 T1 p sd st)
    (hhp : h < p) (hpc : p + 1 < blk.length) (hnd : blk.Nodup)
    (hr : r = k + 1) (hS : st'.S = st.S) (hb : st'.b = st.b.set (blk[p + 1]).1 (β + L - h) (blk[p + 1]).2)
    (hσ : st'.steps = st.steps + 1 + 1 + (blk.length - 1 + X.length))
    (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    sweepInv blk X k β L h vh S1 b1 σ1 T1 (p + 1) (min sd (r + 1)) st' := by
  obtain ⟨hS0, hsd, hσ0, hbb, hbz0, hE⟩ := hinv
  refine ⟨by rw [hS, hS0], by omega, ?_, ?_, ?_, trace_obs_trans hE hT⟩
  · rw [ite_eq_right (show ¬ p ≤ h by omega), show min p (blk.length - 1) = p by omega] at hσ0
    rw [hσ, ite_eq_right (show ¬ p + 1 ≤ h by omega), show min (p + 1) (blk.length - 1) = p + 1 by omega,
      show sweepCalls blk.length L (h + 1) + (p + 1 - (h + 1)) = (sweepCalls blk.length L (h + 1) + (p - (h + 1))) + 1 by omega, Nat.mul_succ]
    omega
  · intro j hj
    rw [hb, vset_fin, hbb j hj, ite_eq_right (show ¬ p ≤ h by omega), ite_eq_right (show ¬ p + 1 ≤ h by omega),
      show min p (blk.length - 1) = p by omega, show min (p + 1) (blk.length - 1) = p + 1 by omega]
    by_cases h1 : j = p + 1
    · subst h1
      rw [ite_eq_left rfl, ite_eq_left (show h < p + 1 ∧ p + 1 ≤ p + 1 by omega)]
    · have hne : blk[p + 1] ≠ blk[j] := fun he => h1 ((hnd.getElem_inj (hi := hpc) (hj := hj)).mp he).symm
      rw [ite_eq_right hne]
      by_cases h2 : h < j ∧ j ≤ p
      · rw [ite_eq_left h2, ite_eq_left (show h < j ∧ j ≤ p + 1 by omega)]
      · rw [ite_eq_right h2]
        by_cases h3 : p < j
        · rw [ite_eq_left h3, ite_eq_right (show ¬ (h < j ∧ j ≤ p + 1) by omega), ite_eq_left (show p + 1 < j by omega)]
        · rw [ite_eq_right h3, ite_eq_right (show ¬ (h < j ∧ j ≤ p + 1) by omega), ite_eq_right (show ¬ p + 1 < j by omega)]
  · intro z hz
    rw [hb, vset_fin, ite_eq_right (getElem_ne_of_not_mem hz _ _), hbz0 z hz]

end sweepinv

/-- the stack while B_h scans: P, then B_0 .. B_h -/
theorem stack_blk_mem {blk P : List (Fin n)} {S1 : Array (Fin n)} {h j : Nat} (hnd : blk.Nodup) (hPb : ∀ x ∈ P, x ∉ blk) (hSP : S1.toList = P ++ blk.take h)
    (hh : h < blk.length) (hj : j < blk.length) : blk[j] ∈ S1.push blk[h] ↔ j ≤ h := by
  rw [Array.mem_def, Array.toList_push, hSP]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ((h1 | h1) | h1)
    · exact absurd (List.getElem_mem _) (hPb _ h1)
    · have := (hnd.getElem_mem_take hj).mp h1; omega
    · have := (hnd.getElem_inj (hi := hj) (hj := hh)).mp h1; omega
  · intro hjh
    rcases Nat.eq_or_lt_of_le hjh with h1 | h1
    · subst h1; exact Or.inr rfl
    · exact Or.inl (Or.inr ((hnd.getElem_mem_take hj).mpr h1))

theorem stack_P_mem {P : List (Fin n)} {blk : List (Fin n)} {S1 : Array (Fin n)} {h : Nat} (hSP : S1.toList = P ++ blk.take h) (vh : Fin n) {x : Fin n} (hx : x ∈ P) : x ∈ S1.push vh := by
  rw [Array.mem_def, Array.toList_push, hSP]
  simp only [List.mem_append]
  exact Or.inl (Or.inl hx)


/-- a later block node B_{p+1} scanned by B_h: every successor is on the stack or pruned -/
theorem sweep_leaf_cond {G : Graph n} {t : Fin n} {k : Nat} {blk X P : List (Fin n)} {h0 β L h : Nat} (ctx : SweepCtx G t k blk X P h0 β L)
    (hhL : h < L) (hlt : h < blk.length) {S1 : Array (Fin n)} {b1 : Vector Nat n} {σ1 : Nat} {T1 : List (Ev n)} (hSP : S1.toList = P ++ blk.take h)
    (hXpre : ∀ x ∈ X, x ∈ P ∨ k ≤ b1[x] + h0) {p sd : Nat} {st : St n} (hinv : sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 p sd st) (hhp : h < p) (hp : p + 1 < blk.length) :
    ∀ u ∈ G.succ blk[p + 1], k ≤ st.b[u] + (h0 + h + 1) ∨ (u ≠ t ∧ u ∈ (st.S.push blk[p + 1]).toList) := by
  obtain ⟨hS, -, -, hbb, hbz, -⟩ := hinv
  have hbound := ctx.bound
  intro u hu
  rw [ctx.succ _ hp] at hu
  simp only [List.mem_append] at hu
  rcases hu with (hu | hu) | hu
  · obtain ⟨m, hm, hm1, rfl⟩ := List.exists_of_mem_take hu
    by_cases hmh : m ≤ h
    · right
      refine ⟨getElem_ne_of_not_mem ctx.t_blk _ _, ?_⟩
      rw [Array.toList_push, hS]
      exact List.mem_append_left _ (Array.mem_def.mp ((stack_blk_mem ctx.nodup ctx.P_blk hSP hlt hm).mpr hmh))
    · left
      rw [hbb m hm, ite_eq_right (show ¬ p ≤ h by omega), ite_eq_left (show h < m ∧ m ≤ min p (blk.length - 1) by omega)]
      omega
  · obtain ⟨m, hm, hm1, rfl⟩ := List.exists_of_mem_drop hu
    left
    rw [hbb m hm, ite_eq_right (show ¬ p ≤ h by omega), ite_eq_right (show ¬ (h < m ∧ m ≤ min p (blk.length - 1)) by omega), ite_eq_left (show min p (blk.length - 1) < m by omega)]
    omega
  · rcases hXpre u hu with hP | hpr
    · right
      refine ⟨fun hut => ctx.t_X (hut ▸ hu), ?_⟩
      rw [Array.toList_push, hS]
      exact List.mem_append_left _ (Array.mem_def.mp (stack_P_mem hSP blk[h] hP))
    · left
      rw [hbz u (ctx.X_blk u hu)]
      omega

section sweepvc
variable {G : Graph n} {t : Fin n} {k : Nat} {blk X P : List (Fin n)} {h0 β L h : Nat} {S1 : Array (Fin n)} {b1 : Vector Nat n} {σ1 : Nat} {T1 : List (Ev n)}

/-- the loop of an inner call, at a successor on the stack (scanned, or pruned) -/
theorem sweepVC_skip (ctx : SweepCtx G t k blk X P h0 β L) (hle : h ≤ min L (blk.length - 1)) (hlt : h < blk.length) (hlast : ¬h = min L (blk.length - 1))
    {pref suff : List (Fin n)} {cur : Fin n} (hsplit : G.succ blk[h] = pref ++ cur :: suff) {sd : Nat} {st st' : St n}
    (hinv : sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 pref.length sd st) (hSP : S1.toList = P ++ blk.take h) (hβ : ∀ j (hj : j < blk.length), h < j → b1[blk[j]] = β)
    (hskip : cur ∈ st.S ∨ ¬st.b[cur] + (h0 + h) < k) (hS : st'.S = st.S) (hb : st'.b = st.b) (hσ : st'.steps = st.steps + 1) (hT : st'.trace = st.trace) :
    sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 (pref ++ [cur]).length sd st' := by
  have hbound := ctx.bound
  rw [ctx.succ h hlt] at hsplit
  simp only [List.length_append, List.length_singleton]
  rcases sweep_pos hlt hsplit with ⟨hp, hph, rfl⟩ | ⟨hp, hph, rfl⟩ | ⟨hp, hX⟩
  · exact sweepInv_skip hinv (Or.inl hph) hS hb hσ hT
  · exfalso
    rcases hskip with hin | hng
    · rw [hinv.1] at hin
      have := (stack_blk_mem ctx.nodup ctx.P_blk hSP hlt hp).mp hin
      omega
    · apply hng
      rw [hinv.2.2.2.1 _ hp]
      rcases Nat.eq_or_lt_of_le hph with heq | hlt'
      · rw [ite_eq_left (show pref.length ≤ h by omega), hβ _ hp (by omega)]; omega
      · rw [ite_eq_right (show ¬ pref.length ≤ h by omega), ite_eq_right (show ¬ (h < pref.length + 1 ∧ pref.length + 1 ≤ min pref.length (blk.length - 1)) by omega),
          ite_eq_left (show min pref.length (blk.length - 1) < pref.length + 1 by omega)]
        omega
  · exact sweepInv_skip hinv (Or.inr ⟨hp, by omega⟩) hS hb hσ hT

/-- the loop of an inner call, at a call: the first child B_{h+1} (the sweep one level deeper), or a later block node (a leaf) -/
theorem sweepVC_call (ctx : SweepCtx G t k blk X P h0 β L) (hle : h ≤ min L (blk.length - 1)) (hlt : h < blk.length) (hlast : ¬h = min L (blk.length - 1))
    {pref suff : List (Fin n)} {cur : Fin n} (hsplit : G.succ blk[h] = pref ++ cur :: suff) {sd r : Nat} {st st' : St n}
    (hinv : sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 pref.length sd st) (hSP : S1.toList = P ++ blk.take h) (hβ : ∀ j (hj : j < blk.length), h < j → b1[blk[j]] = β)
    (hXpre : ∀ x ∈ X, x ∈ P ∨ k ≤ b1[x] + h0) (hg : st.b[cur] + (h0 + h) < k) (hnS : ¬cur ∈ st.S)
    (hpost : (cur = blk[h + 1]'(by omega) → st.S.toList = P ++ blk.take (h + 1) → (∀ j (hj : j < blk.length), h + 1 < j → st.b[blk[j]] = β) →
        (∀ x ∈ X, x ∈ P ∨ k ≤ st.b[x] + h0) →
        r = k + 1 ∧ st'.S = st.S ∧ (∀ j (hj : j < blk.length), st'.b[blk[j]] = if j = h + 1 then β + L - (h + 1) + 1 else if h + 1 < j then β + L - (h + 1) else st.b[blk[j]]) ∧
          (∀ z, ¬z ∈ blk → st'.b[z] = st.b[z]) ∧ st'.steps = st.steps + 1 + (blk.length + X.length) * sweepCalls blk.length L (h + 1) ∧ ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) ∧
      ((∀ u ∈ G.succ cur, k ≤ st.b[u] + (h0 + h + 1) ∨ (u ≠ t ∧ u ∈ (st.S.push cur).toList)) →
        r = k + 1 ∧ st'.S = st.S ∧ st'.b = st.b.set cur.1 (k - (h0 + h + 1) + 1) cur.2 ∧ st'.steps = st.steps + 1 + 1 + (G.succ cur).length ∧ ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = [])) :
    sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 (pref ++ [cur]).length (min sd (r + 1)) st' := by
  have hbound := ctx.bound
  have hlt1 : h + 1 < blk.length := by omega
  rw [ctx.succ h hlt] at hsplit
  simp only [List.length_append, List.length_singleton]
  rw [hinv.1] at hnS
  rcases sweep_pos hlt hsplit with ⟨hp, hph, rfl⟩ | ⟨hp, hph, rfl⟩ | ⟨hp, hX⟩
  · exact absurd ((stack_blk_mem ctx.nodup ctx.P_blk hSP hlt hp).mpr (by omega)) hnS
  · rcases Nat.eq_or_lt_of_le hph with heq | hlt'
    · have hc : blk[pref.length + 1] = blk[h + 1] := by congr 1; omega
      have hS2 : (S1.push blk[h]).toList = P ++ blk.take (h + 1) := by
        rw [Array.toList_push, hSP, List.take_add_one, List.getElem?_eq_getElem hlt]; simp
      have hb2 : ∀ j (hj : j < blk.length), h + 1 < j → st.b[blk[j]] = β := fun j hj hj1 => by
        rw [hinv.2.2.2.1 j hj, ite_eq_left (show pref.length ≤ h by omega)]; exact hβ j hj (by omega)
      have hX2 : ∀ x ∈ X, x ∈ P ∨ k ≤ st.b[x] + h0 := fun x hx => by rw [hinv.2.2.2.2.1 x (ctx.X_blk x hx)]; exact hXpre x hx
      obtain ⟨hr, hS', hb', hbz', hσ', hT'⟩ := hpost.1 hc (by rw [hinv.1]; exact hS2) hb2 hX2
      rw [← heq] at hinv ⊢
      exact sweepInv_fresh hinv (by omega) hlt1 hr hS' hb' hbz' hσ' hT'
    · obtain ⟨hr, hS', hb', hσ', hT'⟩ := hpost.2 (sweep_leaf_cond ctx (by omega) hlt hSP hXpre hinv hlt' hp)
      have hlen : (G.succ blk[pref.length + 1]).length = blk.length - 1 + X.length := by rw [ctx.succ _ hp]; simp; omega
      exact sweepInv_leaf hinv hlt' hp ctx.nodup hr hS' (by rw [hb', show k - (h0 + h + 1) + 1 = β + L - h by omega]) (by rw [hσ', hlen]) hT'
  · rcases hXpre cur hX with hP | hpr
    · exact absurd (stack_P_mem hSP blk[h] hP) hnS
    · rw [hinv.2.2.2.2.1 cur (ctx.X_blk cur hX)] at hg
      omega

end sweepvc

/-- Sweep (gate_family.tex, lem:sweep; the clique-trap run of bsdfs.tex): the first call at relative depth h, at B_h with the
    block nodes B_0 .. B_{h-1} on the stack above P and every later block node at barrier β, returns fruitless after
    (c + |X|) · sweepCalls c L h steps; afterwards B_h carries β + L - h + 1 and every B_j, j > h, carries β + L - h -/
theorem sweep_spec (G : Graph n) (t : Fin n) (k : Nat) (blk X P : List (Fin n)) (h0 β L : Nat) (ctx : SweepCtx G t k blk X P h0 β L)
    (h : Nat) (hle : h ≤ min L (blk.length - 1)) (hlt : h < blk.length) (S1 : Array (Fin n)) (b1 : Vector Nat n) (σ1 : Nat) (T1 : List (Ev n)) :
    ⦃fun st => ⌜st.S = S1 ∧ st.b = b1 ∧ st.steps = σ1 ∧ st.trace.toList = T1 ∧ S1.toList = P ++ blk.take h ∧ (∀ j (hj : j < blk.length), h < j → b1[blk[j]] = β) ∧
      ∀ x ∈ X, x ∈ P ∨ k ≤ b1[x] + h0⌝⦄
    search G t k blk[h] (h0 + h)
    ⦃⇓ r st => ⌜r = k + 1 ∧ st.S = S1 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = h then β + L - h + 1 else if h < j then β + L - h else b1[blk[j]]) ∧
      (∀ z, z ∉ blk → st.b[z] = b1[z]) ∧ st.steps = σ1 + (blk.length + X.length) * sweepCalls blk.length L h ∧ ∃ E, st.trace.toList = T1 ++ E ∧ obsSteps E = []⌝⦄ := by
  have hbound := ctx.bound
  have hsucc := ctx.succ h hlt
  by_cases hlast : h = min L (blk.length - 1)
  · -- the last call of the chain: a leaf
    refine (StateM.triple_iff _ _ _).mpr fun st hst => ?_
    obtain ⟨hS, hb, hσ, hT, hSP, hβ, hXpre⟩ := hst
    have hcond : ∀ w ∈ G.succ blk[h], k ≤ b1[w] + (h0 + h) ∨ (w ≠ t ∧ w ∈ (S1.push blk[h]).toList) := by
      intro w hw
      rw [hsucc] at hw
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · right
        exact ⟨fun hwt => ctx.t_blk (hwt ▸ List.mem_of_mem_take hw), by simp only [Array.toList_push, hSP, List.mem_append]; exact Or.inl (Or.inr hw)⟩
      · left
        obtain ⟨m, hm, hm1, rfl⟩ := List.exists_of_mem_drop hw
        rw [hβ m hm (by omega)]
        omega
      · rcases hXpre w hw with hP | hpr
        · right
          exact ⟨fun hwt => ctx.t_X (hwt ▸ hw), by simp only [Array.toList_push, hSP, List.mem_append]; exact Or.inl (Or.inl hP)⟩
        · left; omega
    obtain ⟨hr, hS', hb', hσ', E, hE, hobs⟩ := (StateM.triple_iff _ _ _).mp (search_leaf G t k (h0 + h) blk[h] S1 b1 σ1 T1 hcond) st ⟨hS, hb, hσ, hT⟩
    refine ⟨hr, hS', ?_, ?_, ?_, E, hE, hobs⟩
    · intro j hj
      rw [hb', vset_fin]
      by_cases hjh : j = h
      · subst hjh; simp; omega
      · have hne : blk[h] ≠ blk[j] := fun he => hjh ((ctx.nodup.getElem_inj (hi := hlt) (hj := hj)).mp he).symm
        rw [ite_eq_right hne, ite_eq_right hjh]
        split
        · rw [hβ j hj (by omega)]; omega
        · rfl
    · intro z hz
      rw [hb', vset_fin, ite_eq_right (getElem_ne_of_not_mem hz _ _)]
    · rw [hσ', show sweepCalls blk.length L h = 1 by rw [hlast]; exact sweepCalls_last _ _, hsucc]
      simp
      omega
  · -- an inner call: B_{h+1} recursively, then the later block nodes as leaves
    have hlt1 : h + 1 < blk.length := by omega
    have ih := fun S2 b2 σ2 T2 => sweep_spec G t k blk X P h0 β L ctx (h + 1) (by omega) hlt1 S2 b2 σ2 T2
    have hcall : ∀ (w : Fin n) (S2 : Array (Fin n)) (b2 : Vector Nat n) (σ2 : Nat) (T2 : List (Ev n)),
        ⦃fun st => ⌜st.S = S2 ∧ st.b = b2 ∧ st.steps = σ2 ∧ st.trace.toList = T2⌝⦄ search G t k w (h0 + h + 1)
        ⦃⇓ r st => ⌜(w = blk[h + 1] → S2.toList = P ++ blk.take (h + 1) → (∀ j (hj : j < blk.length), h + 1 < j → b2[blk[j]] = β) → (∀ x ∈ X, x ∈ P ∨ k ≤ b2[x] + h0) →
            r = k + 1 ∧ st.S = S2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = h + 1 then β + L - (h + 1) + 1 else if h + 1 < j then β + L - (h + 1) else b2[blk[j]]) ∧
            (∀ z, z ∉ blk → st.b[z] = b2[z]) ∧ st.steps = σ2 + (blk.length + X.length) * sweepCalls blk.length L (h + 1) ∧ ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = []) ∧
          ((∀ u ∈ G.succ w, k ≤ b2[u] + (h0 + h + 1) ∨ (u ≠ t ∧ u ∈ (S2.push w).toList)) →
            r = k + 1 ∧ st.S = S2 ∧ st.b = b2.set w.1 (k - (h0 + h + 1) + 1) w.2 ∧ st.steps = σ2 + 1 + (G.succ w).length ∧ ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = [])⌝⦄ := by
      intro w S2 b2 σ2 T2
      refine (StateM.triple_iff _ _ _).mpr fun st hst => ⟨fun hw hS2 hb2 hX2 => ?_, fun hleaf => ?_⟩
      · subst hw
        exact (StateM.triple_iff _ _ _).mp (ih S2 b2 σ2 T2) st ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2, hS2, hb2, hX2⟩
      · exact (StateM.triple_iff _ _ _).mp (search_leaf G t k (h0 + h + 1) w S2 b2 σ2 T2 hleaf) st hst
    have hcasc := fruitful_ext G blk[h]
    rw [search]
    mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hcall, hcasc] invariants
    · ⇓⟨xs, sd⟩ st => ⌜sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 xs.prefix.length sd st⌝
    case vc1.step.isTrue.isTrue =>
      -- t is not among the successors of a block node
      have hsplit := ‹G.succ blk[h] = _ ++ _ :: _›
      have hcur := ‹_ = t›
      rw [hsucc] at hsplit
      exfalso
      rcases sweep_pos hlt hsplit with ⟨hp, -, hc⟩ | ⟨hp, -, hc⟩ | ⟨-, hX⟩
      · exact ctx.t_blk (by rw [← hcur, hc]; exact List.getElem_mem _)
      · exact ctx.t_blk (by rw [← hcur, hc]; exact List.getElem_mem _)
      · exact ctx.t_X (by rw [← hcur]; exact hX)
    case vc2.step.isTrue.isFalse.isTrue.post.success =>
      -- a call: the first child B_{h+1}, or a later block node as a leaf
      have hpre := ‹_ = S1 ∧ _ = b1 ∧ _ = σ1 ∧ _ = T1 ∧ S1.toList = P ++ List.take h blk ∧ _›
      have hnS := ‹¬_ ∈ _›
      have hpost := ‹(_ = blk[h + 1] → _) ∧ _›
      have hg := ‹_ + (h0 + h) < k›
      simp +zetaDelta only at hnS hpost hg ⊢
      exact sweepVC_call ctx hle hlt hlast ‹G.succ blk[h] = _ ++ _ :: _› ‹sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 _ _ _› hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2 hg hnS hpost
    case vc3.step.isTrue.isFalse.isFalse =>
      -- a successor on the stack
      have hpre := ‹_ = S1 ∧ _ = b1 ∧ _ = σ1 ∧ _ = T1 ∧ S1.toList = P ++ List.take h blk ∧ _›
      have hin := ‹¬¬_ ∈ _›
      simp +zetaDelta only at hin ⊢
      exact sweepVC_skip ctx hle hlt hlast ‹G.succ blk[h] = _ ++ _ :: _› ‹sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 _ _ _› hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 (Or.inl (Classical.not_not.mp hin)) rfl rfl rfl rfl
    case vc4.step.isFalse =>
      -- a pruned successor: only nodes on the stack can be pruned here
      have hpre := ‹_ = S1 ∧ _ = b1 ∧ _ = σ1 ∧ _ = T1 ∧ S1.toList = P ++ List.take h blk ∧ _›
      have hng := ‹¬_ + (h0 + h) < k›
      simp +zetaDelta only at hng ⊢
      exact sweepVC_skip ctx hle hlt hlast ‹G.succ blk[h] = _ ++ _ :: _› ‹sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 _ _ _› hpre.2.2.2.2.1 hpre.2.2.2.2.2.1 (Or.inr hng) rfl rfl rfl rfl
    case vc5.neg.pre =>
      -- the entry
      obtain ⟨hS, hb, hσ, hT, hSP, hβ, -⟩ := ‹_ = S1 ∧ _ = b1 ∧ _ = σ1 ∧ _ = T1 ∧ S1.toList = P ++ List.take h blk ∧ _›
      simp +zetaDelta only
      refine ⟨by rw [hS], rfl, by simp [hσ], fun j hj => by simp [hb], fun z hz => by rw [hb], _, by rw [Array.toList_push, hT], by simp [obsSteps]⟩
    case vc6.neg.post.success.isTrue.post.success =>
      -- no cascade: sd = k + 1
      have hinv := ‹sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 _ _ _›
      have hc := ‹_ ≤ k ∧ _›
      have := hinv.2.1
      omega
    case vc7.neg.post.success.isFalse =>
      -- the raise
      obtain ⟨hS, hsd, hσ, hbb, hbz, E, hE, hobs⟩ := ‹sweepInv blk X k β L h blk[h] S1 b1 σ1 T1 _ _ _›
      simp +zetaDelta only
      have hlen : (G.succ blk[h]).length = blk.length - 1 + X.length := by rw [hsucc]; simp; omega
      rw [hlen, ite_eq_right (show ¬ blk.length - 1 + X.length ≤ h by omega), show min (blk.length - 1 + X.length) (blk.length - 1) = blk.length - 1 by omega] at hσ
      refine ⟨hsd, by rw [hS]; simp, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [vset_fin, hbb j hj, hlen, ite_eq_right (show ¬ blk.length - 1 + X.length ≤ h by omega), show min (blk.length - 1 + X.length) (blk.length - 1) = blk.length - 1 by omega]
        by_cases hjh : j = h
        · subst hjh
          rw [ite_eq_left rfl, ite_eq_left rfl]
          omega
        · have hne : blk[h] ≠ blk[j] := fun he => hjh ((ctx.nodup.getElem_inj (hi := hlt) (hj := hj)).mp he).symm
          rw [ite_eq_right hne, ite_eq_right hjh]
          by_cases h2 : h < j
          · rw [ite_eq_left (show h < j ∧ j ≤ blk.length - 1 by omega), ite_eq_left h2]
          · rw [ite_eq_right (show ¬ (h < j ∧ j ≤ blk.length - 1) by omega), ite_eq_right (show ¬ blk.length - 1 < j by omega), ite_eq_right h2]
      · intro z hz
        rw [vset_fin, ite_eq_right (getElem_ne_of_not_mem hz _ _), hbz z hz]
      · rw [hσ, sweepCalls_step (show h < min L (blk.length - 1) by omega),
          show sweepCalls blk.length L (h + 1) + (blk.length - (h + 1)) = (sweepCalls blk.length L (h + 1) + (blk.length - 1 - (h + 1))) + 1 by omega, Nat.mul_succ]
        omega
      · simp only [Array.toList_push]
        refine ext_obs_push (ext_obs_push ⟨E, hE, hobs⟩ ?_) ?_ <;> simp [obsSteps]
termination_by min L (blk.length - 1) - h
