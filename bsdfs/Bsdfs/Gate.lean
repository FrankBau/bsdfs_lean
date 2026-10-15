/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.GateRun

/-!
  Lower bounds, part 2: the gate trap Γ_c of gate_family.tex (a clique trap behind a gate node g).  Nodes s, q, t, g = 0 .. 3
  and the block B_0 .. B_{c-1} = 4 .. c + 3; successors in scan order: s: q, g; q: t, g, B_0, …; g: B_0, q, s; B_i: the other
  block nodes in index order, then g.  The interval between the outputs s q t and s g q t sweeps the block twice, re-armed in
  between by one cascade drop per node.
-/

open Std.Do

set_option mvcgen.warning false

/-! ## The graph -/

section graph
variable (c : Nat)

def gS : Fin (c + 4) := ⟨0, by omega⟩
def gQ : Fin (c + 4) := ⟨1, by omega⟩
def gT : Fin (c + 4) := ⟨2, by omega⟩
def gG : Fin (c + 4) := ⟨3, by omega⟩

/-- the block B_0 .. B_{c-1}: nodes 4 .. c + 3 -/
def gBlk : List (Fin (c + 4)) := (List.finRange c).map (fun i => i.addNat 4)

def gateSucc (v : Fin (c + 4)) : List (Fin (c + 4)) :=
  if v.val = 0 then [gQ c, gG c]
  else if v.val = 1 then gT c :: gG c :: gBlk c
  else if v.val = 2 then []
  else if v.val = 3 then (gBlk c).take 1 ++ [gQ c, gS c]
  else (gBlk c).filter (· ≠ v) ++ [gG c]

def gatePred (v : Fin (c + 4)) : List (Fin (c + 4)) := (List.finRange (c + 4)).filter (fun u => v ∈ gateSucc c u)

/-- the gate trap Γ_c -/
def gate : Graph (c + 4) := ⟨gateSucc c, gatePred c⟩

theorem gBlk_length : (gBlk c).length = c := by simp [gBlk]

theorem gBlk_val (i : Nat) (hi : i < (gBlk c).length) : ((gBlk c)[i]).val = i + 4 := by simp [gBlk]

theorem gBlk_nodup : (gBlk c).Nodup :=
  List.Pairwise.map (fun i : Fin c => i.addNat 4) (fun a b hab he => hab (by simpa [Fin.ext_iff] using he)) (List.nodup_finRange c)

theorem mem_gBlk (z : Fin (c + 4)) : z ∈ gBlk c ↔ 4 ≤ z.val := by
  simp only [gBlk, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩; simp
  · intro h; exact ⟨⟨z.val - 4, by omega⟩, by ext; simp; omega⟩

theorem gS_not_blk : gS c ∉ gBlk c := by simp [mem_gBlk, gS]
theorem gQ_not_blk : gQ c ∉ gBlk c := by simp [mem_gBlk, gQ]
theorem gT_not_blk : gT c ∉ gBlk c := by simp [mem_gBlk, gT]
theorem gG_not_blk : gG c ∉ gBlk c := by simp [mem_gBlk, gG]

theorem finRange_gate : List.finRange (c + 4) = [gS c, gQ c, gT c, gG c] ++ gBlk c := by
  apply List.ext_getElem (by simp [gBlk_length])
  intro i h1 h2
  rw [List.getElem_finRange]
  by_cases hi : i < 4
  · rw [List.getElem_append_left (by simp; omega)]
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals rfl
  · rw [List.getElem_append_right (by simp; omega)]
    ext; simp [gBlk]; omega

end graph

section lists
variable {α : Type} [DecidableEq α]

theorem filter_ne_of_split {l A B : List α} {a : α} (hl : l = A ++ a :: B) (hA : a ∉ A) (hB : a ∉ B) : l.filter (fun x => decide (x ≠ a)) = A ++ B := by
  subst hl
  rw [List.filter_append, List.filter_cons]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [List.filter_eq_self.mpr, List.filter_eq_self.mpr]
  · intro x hx; simp only [decide_eq_true_eq]; intro he; subst he; exact hB hx
  · intro x hx; simp only [decide_eq_true_eq]; intro he; subst he; exact hA hx

theorem List.Nodup.filter_ne_getElem {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) : l.filter (fun x => decide (x ≠ l[i])) = l.take i ++ l.drop (i + 1) := by
  apply filter_ne_of_split
  · rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  · intro h; have := (hnd.getElem_mem_take hi).mp h; omega
  · intro h; have := (hnd.getElem_mem_drop hi).mp h; omega

end lists

section succ
variable (c : Nat)

theorem gate_succ_s : (gate c).succ (gS c) = [gQ c, gG c] := by simp [gate, gateSucc, gS]
theorem gate_succ_q : (gate c).succ (gQ c) = gT c :: gG c :: gBlk c := by simp [gate, gateSucc, gQ]
theorem gate_succ_t : (gate c).succ (gT c) = [] := by simp [gate, gateSucc, gT]
theorem gate_succ_g : (gate c).succ (gG c) = (gBlk c).take 1 ++ [gQ c, gS c] := by simp [gate, gateSucc, gG]

theorem gS_ne_gQ : gS c ≠ gQ c := by simp [gS, gQ, Fin.ext_iff]
theorem gS_ne_gG : gS c ≠ gG c := by simp [gS, gG, Fin.ext_iff]
theorem gQ_ne_gT : gQ c ≠ gT c := by simp [gQ, gT, Fin.ext_iff]
theorem gQ_ne_gG : gQ c ≠ gG c := by simp [gQ, gG, Fin.ext_iff]
theorem gT_ne_gG : gT c ≠ gG c := by simp [gT, gG, Fin.ext_iff]

theorem gate_succ_B (i : Nat) (hi : i < (gBlk c).length) : (gate c).succ (gBlk c)[i] = (gBlk c).take i ++ (gBlk c).drop (i + 1) ++ [gG c] := by
  have hv := gBlk_val c i hi
  simp only [gate, gateSucc, hv]
  simp only [show i + 4 ≠ 0 by omega, show i + 4 ≠ 1 by omega, show i + 4 ≠ 2 by omega, show i + 4 ≠ 3 by omega, ↓reduceIte]
  rw [(gBlk_nodup c).filter_ne_getElem hi]

end succ

section pred
variable (c : Nat)

theorem gate_pred_eq (v : Fin (c + 4)) : (gate c).pred v = ([gS c, gQ c, gT c, gG c] ++ gBlk c).filter (fun u => v ∈ (gate c).succ u) := by
  show gatePred c v = _
  unfold gatePred
  rw [finRange_gate]
  rfl

theorem gate_pred_q : (gate c).pred (gQ c) = [gS c, gG c] := by
  rw [gate_pred_eq, List.filter_append]
  have h1 : (gBlk c).filter (fun u => decide (gQ c ∈ (gate c).succ u)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    rw [gate_succ_B c i hi]
    simp only [List.mem_append, List.mem_singleton, decide_eq_true_eq, not_or]
    exact ⟨⟨fun h => gQ_not_blk c (List.mem_of_mem_take h), fun h => gQ_not_blk c (List.mem_of_mem_drop h)⟩, by simp [gQ, gG, Fin.ext_iff]⟩
  rw [h1]
  have hgq : gQ c ∉ (gBlk c).take 1 := fun h => gQ_not_blk c (List.mem_of_mem_take h)
  simp [gate_succ_s, gate_succ_q, gate_succ_t, gate_succ_g, gQ_ne_gT c, gQ_ne_gG c, (gS_ne_gQ c).symm, gQ_not_blk c, hgq]

theorem gate_pred_g : (gate c).pred (gG c) = [gS c, gQ c] ++ gBlk c := by
  rw [gate_pred_eq, List.filter_append]
  have h1 : (gBlk c).filter (fun u => decide (gG c ∈ (gate c).succ u)) = gBlk c := by
    rw [List.filter_eq_self]
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    rw [gate_succ_B c i hi]
    simp
  rw [h1]
  have hg : gG c ∉ (gBlk c).take 1 := fun h => gG_not_blk c (List.mem_of_mem_take h)
  simp [gate_succ_s, gate_succ_q, gate_succ_t, gate_succ_g, (gT_ne_gG c).symm, (gQ_ne_gG c).symm, (gS_ne_gG c).symm, hg]

theorem gate_pred_B_mem (j : Nat) (hj : j < (gBlk c).length) (u : Fin (c + 4)) (hu : u ∈ (gate c).pred (gBlk c)[j]) : u = gQ c ∨ u = gG c ∨ u ∈ gBlk c := by
  rw [gate_pred_eq, List.mem_filter] at hu
  obtain ⟨hu1, hu2⟩ := hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu1
  rcases hu1 with (rfl | rfl | rfl | rfl) | hu1
  · exfalso
    rw [gate_succ_s] at hu2
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hu2
    rcases hu2 with h | h
    · exact getElem_ne_of_not_mem (gQ_not_blk c) _ _ h
    · exact getElem_ne_of_not_mem (gG_not_blk c) _ _ h
  · exact Or.inl rfl
  · exfalso
    rw [gate_succ_t] at hu2
    simp at hu2
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr hu1)

theorem sum_map_const {α : Type} (l : List α) (f : α → Nat) (m : Nat) (h : ∀ x ∈ l, f x = m) : (l.map f).sum = m * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy])), Nat.mul_succ]
    omega

theorem gate_pred_B_length (j : Nat) (hj : j < (gBlk c).length) : ((gate c).pred (gBlk c)[j]).length = c + (if j = 0 then 1 else 0) := by
  rw [gate_pred_eq, List.filter_append, List.length_append]
  have h1 : (gBlk c).filter (fun u => decide ((gBlk c)[j] ∈ (gate c).succ u)) = (gBlk c).filter (fun u => decide (u ≠ (gBlk c)[j])) := by
    apply List.filter_congr
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    rw [gate_succ_B c i hi]
    simp only [List.mem_append, List.mem_singleton, decide_eq_decide]
    rw [(gBlk_nodup c).getElem_mem_take hj, (gBlk_nodup c).getElem_mem_drop hj, ne_eq, (gBlk_nodup c).getElem_inj]
    constructor
    · rintro ((h | h) | h)
      · omega
      · omega
      · exact absurd h (getElem_ne_of_not_mem (gG_not_blk c) _ _)
    · intro h
      left
      omega
  rw [h1, (gBlk_nodup c).filter_ne_getElem hj]
  have hv := gBlk_val c j hj
  have h4 : ([gS c, gQ c, gT c, gG c].filter fun u => decide ((gBlk c)[j] ∈ (gate c).succ u)).length = 1 + (if j = 0 then 1 else 0) := by
    have hq : (gBlk c)[j] ∈ (gate c).succ (gQ c) := by rw [gate_succ_q]; simp
    have hs : (gBlk c)[j] ∉ (gate c).succ (gS c) := by
      rw [gate_succ_s]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨getElem_ne_of_not_mem (gQ_not_blk c) _ _, getElem_ne_of_not_mem (gG_not_blk c) _ _⟩
    have ht : (gBlk c)[j] ∉ (gate c).succ (gT c) := by rw [gate_succ_t]; simp
    have hg : (gBlk c)[j] ∈ (gate c).succ (gG c) ↔ j = 0 := by
      rw [gate_succ_g]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rw [(gBlk_nodup c).getElem_mem_take hj]
      constructor
      · rintro (h | h | h)
        · omega
        · simp [Fin.ext_iff, gQ, hv] at h
        · simp [Fin.ext_iff, gS, hv] at h
      · intro h; exact Or.inl (by omega)
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, hq, hs, ht, ↓reduceIte]
    by_cases hj0 : j = 0
    · subst hj0
      have := hg.mpr rfl
      simp [this]
    · simp [show ¬ (gBlk c)[j] ∈ (gate c).succ (gG c) from fun h => hj0 (hg.mp h), hj0]
  rw [h4]
  simp [gBlk_length]
  omega

theorem gate_wf : (gate c).WF where
  succ_nodup := by
    intro u
    simp only [gate, gateSucc]
    split
    · simp [gQ, gG, Fin.ext_iff]
    split
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨gG_not_blk c, gBlk_nodup c⟩⟩
      simp only [List.mem_cons, not_or]
      exact ⟨by simp [gT, gG, Fin.ext_iff], gT_not_blk c⟩
    split
    · exact List.nodup_nil
    split
    · refine List.nodup_append.mpr ⟨(gBlk_nodup c).sublist (List.take_sublist _ _), by simp [gQ, gS, Fin.ext_iff], ?_⟩
      intro a ha b hb hab
      subst hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact gQ_not_blk c (List.mem_of_mem_take ha)
      · exact gS_not_blk c (List.mem_of_mem_take ha)
    · refine List.nodup_append.mpr ⟨(gBlk_nodup c).filter _, by simp, ?_⟩
      intro a ha b hb hab
      subst hab
      simp only [List.mem_singleton] at hb
      subst hb
      exact gG_not_blk c (List.mem_filter.mp ha).1
  pred_nodup := fun v => (List.nodup_finRange _).filter _
  rev := by intro u v; simp [gate, gatePred]

theorem gate_m (hc : 1 ≤ c) : (gate c).m = c * c + c + 7 := by
  unfold Graph.m
  rw [finRange_gate]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [gate_succ_s, gate_succ_q, gate_succ_t, gate_succ_g]
  have hb : ((gBlk c).map fun v => ((gate c).succ v).length).sum = c * c := by
    rw [sum_map_const _ _ c, gBlk_length]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    rw [gate_succ_B c i hi]
    simp [gBlk_length] at hi ⊢
    omega
  rw [hb]
  simp [gBlk_length]
  omega

end pred

/-! ## The first interval -/

section run
variable (c : Nat)

theorem gS_ne_gT : gS c ≠ gT c := by simp [gS, gT, Fin.ext_iff]

/-- Γ_c has the successor and predecessor lists of a gate trap -/
theorem gate_ctx (hc : 1 ≤ c) : GateCtx (gate c) (gS c) (gQ c) (gT c) (gG c) (gBlk c) where
  nodup := gBlk_nodup c
  pos := by rw [gBlk_length]; omega
  size := by rw [gBlk_length]; omega
  s_q := gS_ne_gQ c
  s_t := gS_ne_gT c
  s_g := gS_ne_gG c
  q_t := gQ_ne_gT c
  q_g := gQ_ne_gG c
  t_g := gT_ne_gG c
  s_blk := gS_not_blk c
  q_blk := gQ_not_blk c
  t_blk := gT_not_blk c
  g_blk := gG_not_blk c
  succ_s := gate_succ_s c
  succ_q := gate_succ_q c
  succ_g := gate_succ_g c
  succ_B := gate_succ_B c
  pred_q := gate_pred_q c
  pred_g := by rw [gate_pred_g]; rfl
  pred_B := gate_pred_B_mem c
  pred_B_len := fun j hj => by rw [gate_pred_B_length c j hj, gBlk_length]

/-- gate_family.tex, interval 1 (with the early exit at s): on Γ_c with k ≥ 6, the first three observable events are the start at
    step 0 and the outputs s q t at step 7 and s g q t at step 7 + D1, D1 = (c + 1)(N(c, k - 3) + N(c, k - 5)) + 3c² + 4c + 21 -/
theorem gate_interval1 (k : Nat) (hc : 1 ≤ c) (hk : 6 ≤ k) : ∃ rest, obsSteps (bsdfs (gate c) (gS c) (gT c) k) = [0, 7, 7 + gateD1 c k] ++ rest := by
  have := gate_run (gate_ctx c hc) k hk
  rwa [gBlk_length] at this

/-- n + m of Γ_c -/
theorem gate_size (hc : 1 ≤ c) : c + 4 + (gate c).m = c * c + 2 * c + 11 := by
  rw [gate_m c hc]; omega

end run
