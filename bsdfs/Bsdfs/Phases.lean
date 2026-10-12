import Bsdfs.DelaySum
import Bsdfs.Complete

/-!
  Stage 3b of the delay proof: the v2 phase lemmas of bsdfs.tex (Ascent Purity, Call--Phase Correspondence, Descent Origins,
  Dequeue Count, Descent Seal, One Entry per Pair per Phase) derived from `RunFacts`, facts about single events and single frames
  of the run.  Stage 3c proves `RunFacts` for the actual run from the program.
-/

open Trace

variable {n : Nat}

/-- events that occur only inside a cascade -/
def Trace.isCasc (tr : List (Ev n)) (q : Nat) : Bool := match tr[q]? with
  | some (.cascade ..) => true
  | some (.dequeue ..) => true
  | some (.write _ _ _ _ .drop) => true
  | some (.write _ _ _ _ .fruitful) => true
  | _ => false

/-- facts about single events and single frames of the run -/
structure RunFacts (G : Graph n) (s t : Fin n) (k : Nat) (tr : List (Ev n)) : Prop where
  /-- an entry at depth h = |S|, of a node off the stack and ≠ t, under the pruning guard, extending the stack path; depth 0 only for the initial call -/
  enter : ∀ q σ z h, tr[q]? = some (.enter σ z h) → h = (stk tr q).length ∧ z ∉ stk tr q ∧ z ≠ t ∧ bar tr q z + h ≤ k ∧ (h = 0 → q = 1) ∧ (stk tr q ++ [z]).head? = some s ∧ G.Edges (stk tr q ++ [z])
  exit : ∀ q σ v h sd f, tr[q]? = some (.exit σ v h sd f) → (stk tr q).getLast? = some v ∧ h + 1 = (stk tr q).length
  output : ∀ q σ P, tr[q]? = some (.output σ P) → P = stk tr q ++ [t] ∧ (stk tr q).length ≤ k
  write_old : ∀ q σ x o nw kd, tr[q]? = some (.write σ x o nw kd) → o = bar tr q x
  raise : ∀ q σ x o nw, tr[q]? = some (.write σ x o nw .raise) → (stk tr q).getLast? = some x ∧ nw + (stk tr q).length = k + 2 ∧ o < nw
  fruitful : ∀ q σ x o nw, tr[q]? = some (.write σ x o nw .fruitful) → (stk tr q).getLast? = some x ∧ nw + (stk tr q).length ≤ k + 1 ∧ o ≤ nw ∧ 1 ≤ nw ∧ 2 ≤ (stk tr q).length
  drop : ∀ q σ x o nw, tr[q]? = some (.write σ x o nw .drop) → x ∉ stk tr q ∧ nw < o ∧ 2 ≤ nw ∧ 2 ≤ (stk tr q).length
  bar_t : ∀ q, bar tr q t = 0
  /-- every entry has its frame -/
  frame : ∀ e σ v h, tr[e]? = some (.enter σ v h) → ∃ x, Frame tr e x
  /-- Return Value: a frame is fruitful iff it contains an output -/
  ret : ∀ e x σ v h sd f, Frame tr e x → tr[x]? = some (.exit σ v h sd f) → (f = true ↔ ∃ q σ' P, e < q ∧ q < x ∧ tr[q]? = some (.output σ' P))
  /-- a fruitless frame ends with its raise -/
  fruitless_end : ∀ e x σe ve he σ v h sd, Frame tr e x → tr[e]? = some (.enter σe ve he) → tr[x]? = some (.exit σ v h sd false) → ∃ σ' o, tr[x - 1]? = some (.write σ' ve o (k + 1 - he) .raise)
  /-- cascade events belong to the cascade of the top frame, a fruitful frame, which runs to its exit -/
  casc : ∀ q, isCasc tr q = true → ∃ e x σ v h sd, Frame tr e x ∧ e < q ∧ q < x ∧ (stk tr (e + 1)).length = (stk tr q).length ∧ tr[x]? = some (.exit σ v h sd true) ∧ ∀ r, q ≤ r → r < x → isCasc tr r = true
  /-- a dropped node is not written again in the same cascade -/
  drop_last : ∀ θ y, dropAt tr y θ = true → ∀ r σ o nw kd, θ < r → (∀ r', θ ≤ r' → r' ≤ r → isCasc tr r' = true) → tr[r]? ≠ some (.write σ y o nw kd)
  /-- a dequeue of a node other than the origin follows its drop in the same cascade -/
  deq_drop : ∀ q z, deqAt tr z q = true → (stk tr q).getLast? ≠ some z → ∃ q', q' < q ∧ dropAt tr z q' = true ∧ ∀ r, q' ≤ r → r ≤ q → isCasc tr r = true
  /-- the origin's dequeue follows its fruitful write in the same cascade -/
  deq_origin : ∀ q z, deqAt tr z q = true → (stk tr q).getLast? = some z → ∃ q', q' < q ∧ fruitAt tr z q' = true ∧ ∀ r, q' ≤ r → r ≤ q → isCasc tr r = true
  /-- a node is dequeued at most once per cascade -/
  deq_once : ∀ q₁ q₂ z, q₁ < q₂ → deqAt tr z q₁ = true → deqAt tr z q₂ = true → ∃ r, q₁ < r ∧ r < q₂ ∧ isCasc tr r = false
  /-- Per-Call Global Monotonicity -/
  mono : ∀ e x, Frame tr e x → ∀ z, bar tr e z ≤ bar tr (x + 1) z
  /-- a call at u scans every successor y while it is the top frame: t, on the stack, entered as a child, or pruned -/
  scan : ∀ e x σ u h, Frame tr e x → tr[e]? = some (.enter σ u h) → ∀ y ∈ G.succ u, ∃ q, e < q ∧ q < x ∧ stk tr q = stk tr (e + 1) ∧ (y = t ∨ y ∈ stk tr q ∨ enterAt tr y q = true ∨ k ≤ bar tr q y + h)
  /-- Call Completeness: a call outputs every bounded path extending its search path -/
  complete : ∀ e x, Frame tr e x → ∀ p, G.BoundedPath k s t p → (stk tr (e + 1)) <+: p → ∃ q σ, e < q ∧ q < x ∧ tr[q]? = some (.output σ p)
  /-- Cascade Witness Path: a drop writes the length of a walk to t avoiding the stack below the origin -/
  witness : ∀ θ σ y o nw, tr[θ]? = some (.write σ y o nw .drop) → G.WalkLE (stk tr θ).dropLast t y nw

/-! ## Helpers: counting, frames, paths -/

section helpers
variable {tr : List (Ev n)}

/-- an injection from the P-positions into the Q-positions of (lo, hi] -/
theorem Trace.cnt_le_of_inj (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] (f : Nat → Nat) {lo hi : Nat} (hmap : ∀ q, lo < q → q ≤ hi → P q → lo < f q ∧ f q ≤ hi ∧ Q (f q)) (hinj : ∀ q₁ q₂, lo < q₁ → q₁ ≤ hi → lo < q₂ → q₂ ≤ hi → P q₁ → P q₂ → f q₁ = f q₂ → q₁ = q₂) : cnt P lo hi ≤ cnt Q lo hi := by
  unfold cnt
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hmem : ∀ q ∈ (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q)), lo < q ∧ q ≤ hi ∧ P q := by
    intro q hq
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hq
    exact ⟨by omega, by omega, hq.2⟩
  have hnd : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).Nodup := (List.nodup_range' (step := 1)).filter _
  have hnd' := nodup_map_of_inj (f := f) hnd (fun q₁ hq₁ q₂ hq₂ heq => by
    obtain ⟨a1, b1, c1⟩ := hmem q₁ hq₁
    obtain ⟨a2, b2, c2⟩ := hmem q₂ hq₂
    exact hinj q₁ q₂ a1 b1 a2 b2 c1 c2 heq)
  have hsub : ((List.range' (lo + 1) (hi - lo)).filter (fun q => decide (P q))).map f ⊆ (List.range' (lo + 1) (hi - lo)).filter (fun q => decide (Q q)) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    obtain ⟨a1, b1, c1⟩ := hmem q hq
    obtain ⟨h1, h2, h3⟩ := hmap q a1 b1 c1
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
    exact ⟨by omega, h3⟩
  have := hnd'.length_le_of_subset hsub
  simpa using this

/-- the same with a relation: every P-position has a related Q-position, and no Q-position is related to two P-positions -/
theorem Trace.cnt_le_of_rel (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] (R : Nat → Nat → Prop) {lo hi : Nat} (hex : ∀ q, lo < q → q ≤ hi → P q → ∃ q', lo < q' ∧ q' ≤ hi ∧ Q q' ∧ R q q') (hinj : ∀ q₁ q₂ q', lo < q₁ → q₁ ≤ hi → lo < q₂ → q₂ ≤ hi → P q₁ → P q₂ → R q₁ q' → R q₂ q' → q₁ = q₂) : cnt P lo hi ≤ cnt Q lo hi := by
  let f : Nat → Nat := fun q => if h : lo < q ∧ q ≤ hi ∧ P q then Classical.choose (hex q h.1 h.2.1 h.2.2) else 0
  have hf : ∀ q (h : lo < q ∧ q ≤ hi ∧ P q), lo < f q ∧ f q ≤ hi ∧ Q (f q) ∧ R q (f q) := by
    intro q h
    simp only [f, dite_eq_left h]
    exact Classical.choose_spec (hex q h.1 h.2.1 h.2.2)
  refine Trace.cnt_le_of_inj P Q f (fun q h1 h2 h3 => ?_) (fun q₁ q₂ a1 b1 a2 b2 c1 c2 heq => ?_)
  · obtain ⟨a, b, c, -⟩ := hf q ⟨h1, h2, h3⟩; exact ⟨a, b, c⟩
  · have r1 := (hf q₁ ⟨a1, b1, c1⟩).2.2.2
    have r2 := (hf q₂ ⟨a2, b2, c2⟩).2.2.2
    rw [heq] at r1
    exact hinj q₁ q₂ (f q₂) a1 b1 a2 b2 c1 c2 r1 r2

/-- split the P-positions by a predicate R -/
theorem List.countP_le_split {α : Type} (p r : α → Bool) (L : List α) : L.countP p ≤ L.countP (fun q => p q && r q) + L.countP (fun q => p q && !r q) := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.countP_cons]
    cases hp : p q <;> cases hr : r q <;> simp <;> omega

theorem Trace.cnt_le_split (P R : Nat → Prop) [DecidablePred P] [DecidablePred R] (lo hi : Nat) : cnt P lo hi ≤ cnt (fun q => P q ∧ R q) lo hi + cnt (fun q => P q ∧ ¬ R q) lo hi := by
  unfold cnt
  simp only [Bool.decide_and, decide_not]
  exact List.countP_le_split (fun q => decide (P q)) (fun q => decide (R q)) _

/-- at most one P-position -/
theorem Trace.cnt_le_one (P : Nat → Prop) [DecidablePred P] {lo hi : Nat} (h : ∀ q₁ q₂, lo < q₁ → q₁ ≤ hi → lo < q₂ → q₂ ≤ hi → P q₁ → P q₂ → q₁ = q₂) : cnt P lo hi ≤ 1 := by
  have := Trace.cnt_le_of_depth P (fun _ => 0) (A := 0) (B := 0) (fun _ _ _ _ => ⟨Nat.le_refl 0, Nat.le_refl 0⟩) (fun q₁ q₂ a1 b1 a2 b2 c1 c2 _ => h q₁ q₂ a1 b1 a2 b2 c1 c2)
  simpa using this

/-- the stack grows only at an entry -/
theorem Trace.enter_of_length_lt {p : Nat} (h : (stk tr p).length < (stk tr (p + 1)).length) : ∃ σ v hh, tr[p]? = some (.enter σ v hh) := by
  rw [Trace.stk_succ] at h
  split at h
  · next σ v hh heq => exact ⟨σ, v, hh, heq⟩
  · simp at h; omega
  · omega

/-- a node on the stack at p₂ but not at p₁ was entered in between -/
theorem Trace.exists_enter_of_mem {z : Fin n} {p₁ p₂ : Nat} (hp : p₁ ≤ p₂) (h1 : z ∉ stk tr p₁) (h2 : z ∈ stk tr p₂) : ∃ q, p₁ ≤ q ∧ q < p₂ ∧ enterAt tr z q = true :=
  Classical.byContradiction fun hne => Trace.not_mem_stk_of_no_enter hp h1 (fun q hq1 hq2 => by
    cases hq : enterAt tr z q
    · rfl
    · exact absurd ⟨q, hq1, hq2, hq⟩ hne) h2

/-- a frame is determined by its entry -/
theorem Trace.Frame.exit_unique {e x x' : Nat} (h : Frame tr e x) (h' : Frame tr e x') : x = x' := by
  rcases Nat.lt_trichotomy x x' with hlt | heq | hgt
  · have := h'.isOpen (q := x + 1) (by have := h.1; omega) (by omega); have := h.2.2.2.1; omega
  · exact heq
  · have := h.isOpen (q := x' + 1) (by have := h'.1; omega) (by omega); have := h'.2.2.2.1; omega

/-- while the frame is the top frame, the stack is the frame's own stack -/
theorem Trace.Frame.top {e x q : Nat} (h : Frame tr e x) (h1 : e < q) (h2 : q ≤ x) (hlen : (stk tr (e + 1)).length = (stk tr q).length) : stk tr q = stk tr (e + 1) := by
  have := h.prefix h1 h2
  rw [← h.push, hlen, List.take_length] at this
  exact this

/-- two frames open at q that entered the same node are the same frame (the stack at q has no duplicates) -/
theorem Trace.Frame.eq_of_node {e₁ x₁ e₂ x₂ q σ₁ σ₂ h₁ h₂ : Nat} {v : Fin n} (hnd : (stk tr q).Nodup) (hf₁ : Frame tr e₁ x₁) (hf₂ : Frame tr e₂ x₂) (he₁ : tr[e₁]? = some (.enter σ₁ v h₁)) (he₂ : tr[e₂]? = some (.enter σ₂ v h₂)) (hq₁ : e₁ < q) (hq₁' : q ≤ x₁) (hq₂ : e₂ < q) (hq₂' : q ≤ x₂) : e₁ = e₂ := by
  have hidx : ∀ {e x σ h}, Frame tr e x → tr[e]? = some (.enter σ v h) → e < q → q ≤ x → (stk tr q)[(stk tr e).length]? = some v := by
    intro e x σ h hf he h1 h2
    have hp : ((stk tr q).take ((stk tr e).length + 1))[(stk tr e).length]? = (stk tr (e + 1))[(stk tr e).length]? := by rw [hf.prefix h1 h2]
    rw [Trace.stk_succ_enter he, List.getElem?_concat_length, List.getElem?_take] at hp
    simpa using hp
  have hd : (stk tr e₁).length = (stk tr e₂).length :=
    hnd.eq_of_getElem?_eq (by have := hf₁.isOpen hq₁ hq₁'; omega) (by rw [hidx hf₁ he₁ hq₁ hq₁', hidx hf₂ he₂ hq₂ hq₂'])
  rcases Nat.lt_trichotomy e₁ e₂ with h | h | h
  · have := (hf₁.nest hf₂ h (by omega)).2; omega
  · exact h
  · have := (hf₂.nest hf₁ h (by omega)).2; omega

end helpers

theorem Graph.Edges.of_append_left {G : Graph n} {A B : List (Fin n)} (h : G.Edges (A ++ B)) : G.Edges A := by
  induction A with
  | nil => trivial
  | cons a A ih =>
    cases A with
    | nil => trivial
    | cons a' A => exact ⟨h.1, ih h.2⟩

/-- Descent Seal's path: a stack path P ++ M from s ending in x, followed by a walk from x to t that avoids X ⊇ P, contains a
    bounded s-t path that extends P ++ M.take 1 -/
theorem Graph.bounded_of_stack_walk {G : Graph n} {k : Nat} {s t x : Fin n} {P M X : List (Fin n)} {d : Nat} (hPX : ∀ z ∈ P, z ∈ X) (hhead : (P ++ M).head? = some s) (hE : G.Edges (P ++ M)) (hnd : (P ++ M).Nodup) (hM : M.getLast? = some x) (hW : G.WalkLE X t x d) (hlen : (P ++ M).length + d ≤ k + 1) : ∃ R, G.BoundedPath k s t R ∧ (P ++ M.take 1) <+: R := by
  obtain ⟨l, hl, hw⟩ := hW
  obtain ⟨RW, hRW1, hRW2, hRWe, hRWnd, hRWX, hRWlen⟩ := hw.path
  obtain ⟨A, rfl⟩ := List.getLast?_eq_some_iff.mp hM
  cases RW with
  | nil => simp at hRW1
  | cons x' RW₀ =>
  simp only [List.head?_cons, Option.some.injEq] at hRW1
  subst hRW1
  obtain ⟨q₁, rest, hrest⟩ : ∃ q₁ rest, A ++ [x'] = q₁ :: rest := by cases A <;> simp
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hoffP : ∀ z ∈ A ++ x' :: RW₀, z ∉ P := by
    intro z hz hzP
    rw [List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact hdisj z hzP z (by simp [hz]) rfl
    · exact hdisj z hzP z (by simp) rfl
    · exact hRWX z (by simpa using hz) (hPX z hzP)
  -- the walk A ++ x' :: RW₀ from q₁ to t, avoiding P after q₁
  have hEA : G.Edges (A ++ [x']) := Graph.Edges.of_append_right (A := P) hE
  have hEN : G.Edges (A ++ x' :: RW₀) := Graph.Edges.append_cons hEA hRWe
  have hNh : (A ++ x' :: RW₀).head? = some q₁ := by rw [head_append_cons, hrest]; rfl
  have hNl : (A ++ x' :: RW₀).getLast? = some t := by
    rw [List.getLast?_append, hRW2]; rfl
  have hwN := Graph.walk_of_list (X := P) (A ++ x' :: RW₀) q₁ hNh hNl hEN (fun z hz => hoffP z (List.mem_of_mem_tail hz))
  obtain ⟨Q, hQ1, hQ2, hQe, hQnd, hQX, hQlen⟩ := hwN.path
  cases Q with
  | nil => simp at hQ1
  | cons q₁' Q₀ =>
  simp only [List.head?_cons, Option.some.injEq] at hQ1
  subst hQ1
  have hq₁P : q₁' ∉ P := by
    have hmem : q₁' ∈ A ++ [x'] := by rw [hrest]; simp
    rw [List.mem_append, List.mem_singleton] at hmem
    refine hoffP q₁' ?_
    rcases hmem with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (by simp [h])
  have hPM : P ++ (A ++ [x']) = (P ++ [q₁']) ++ rest := by rw [hrest]; simp
  refine ⟨P ++ q₁' :: Q₀, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hrest] at hhead
    rw [head_append_cons] at hhead
    rw [head_append_cons]
    exact hhead
  · rw [List.getLast?_append, hQ2]; rfl
  · refine List.nodup_append.mpr ⟨(List.nodup_append.mp hnd).1, hQnd, ?_⟩
    intro a ha b hb hab
    subst hab
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hq₁P ha
    · exact hQX a (by simpa using hb) ha
  · have h1 : (A ++ [x']).length = A.length + 1 := by simp
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen hQlen hRWlen ⊢
    omega
  · rw [hPM] at hE
    exact (Graph.edges_iff_zip G _).mp (Graph.Edges.append_cons (Graph.Edges.of_append_left hE) hQe)
  · exact ⟨Q₀, by rw [hrest]; simp⟩

namespace RunFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hR : RunFacts G s t k tr)
include hR

theorem stk_nodup (q : Nat) : (stk tr q).Nodup :=
  Trace.stk_nodup (fun p σ v hh he => (hR.enter p σ v hh he).2.1) q

omit hR in
theorem isCasc_of_obs {q : Nat} (h : isObs tr q = true) : isCasc tr q = false := by
  unfold isObs at h; unfold isCasc
  cases hq : tr[q]? with
  | none => simp [hq] at h
  | some e => cases e with
    | write σ x o nw kd => cases kd <;> simp [hq, Ev.obs] at h ⊢
    | _ => simp [hq, Ev.obs] at h ⊢

omit hR in
theorem isCasc_of_drop {q : Nat} {y : Fin n} (h : dropAt tr y q = true) : isCasc tr q = true := by
  obtain ⟨σ, o, nw, he⟩ := Trace.dropAt_iff.mp h; simp [isCasc, he]

omit hR in
theorem isCasc_of_deq {q : Nat} {y : Fin n} (h : deqAt tr y q = true) : isCasc tr q = true := by
  obtain ⟨σ, d, he⟩ := Trace.deqAt_iff.mp h; simp [isCasc, he]

omit hR in
theorem isCasc_of_fruit {q : Nat} {y : Fin n} (h : fruitAt tr y q = true) : isCasc tr q = true := by
  obtain ⟨σ, o, nw, he⟩ := Trace.fruitAt_iff.mp h; simp [isCasc, he]

omit hR in
theorem not_isCasc_of_exit {q σ : Nat} {v : Fin n} {h sd : Nat} {f : Bool} (he : tr[q]? = some (.exit σ v h sd f)) : isCasc tr q = false := by
  simp [isCasc, he]

omit hR in
theorem not_isCasc_of_output {q σ : Nat} {P : List (Fin n)} (he : tr[q]? = some (.output σ P)) : isCasc tr q = false := by
  simp [isCasc, he]

omit hR in
theorem isObs_of_output {q σ : Nat} {P : List (Fin n)} (he : tr[q]? = some (.output σ P)) : isObs tr q = true := by
  simp [isObs, he, Ev.obs]

/-- the frame of a cascade event is open at a, when no output lies between a and the cascade -/
theorem casc_open {a q : Nat} (hq : isCasc tr q = true) (hno : ∀ r, a < r → r < q → isObs tr r = false) : ∃ e x σ v h sd, Frame tr e x ∧ e < q ∧ q < x ∧ (stk tr (e + 1)).length = (stk tr q).length ∧ tr[x]? = some (.exit σ v h sd true) ∧ (∀ r, q ≤ r → r < x → isCasc tr r = true) ∧ e < a := by
  obtain ⟨e, x, σ, v, h, sd, hfr, heq, hqx, hlen, hex, hall⟩ := hR.casc q hq
  obtain ⟨o, σo, P, h1, h2, ho⟩ := (hR.ret e x σ v h sd true hfr hex).mp rfl
  have hoq : o < q := by
    refine Nat.lt_of_not_le fun hle => ?_
    have := hall o hle h2
    rw [not_isCasc_of_output ho] at this; cases this
  have hoa : o ≤ a := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := hno o hlt hoq
    rw [isObs_of_output ho] at this; cases this
  exact ⟨e, x, σ, v, h, sd, hfr, heq, hqx, hlen, hex, hall, by omega⟩

section interval
variable {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β)
include hC hS

/-- Ascent Purity (lem:phase-a-purity) -/
theorem asc_pure {q : Nat} (h1 : β < q) (h2 : q ≤ c) (hq : isCasc tr q = true) : False := by
  obtain ⟨e, x, σ, v, h, sd, hfr, heq, hqx, hlen, hex, hall, hea⟩ := hR.casc_open (a := a) hq (fun r h1' h2' => hC.between r h1' (by omega))
  have hxc : x < c := by
    refine Nat.lt_of_not_le fun hle => ?_
    rcases Nat.eq_or_lt_of_le hle with hxc | hxc
    · subst hxc; have := hC.obs_c; simp [isObs, hex, Ev.obs] at this
    · have := hall c (by omega) hxc
      rw [isCasc_of_obs hC.obs_c] at this; cases this
  have hsz := hfr.2.2.2.1
  have hmin := hS.min (x + 1) (by have := hS.le; omega) (by omega)
  have hopen := hfr.isOpen (q := β + 1) (by have := hS.le; omega) (by omega)
  have := hS.at_beta
  omega

/-- Call--Phase Correspondence (1): a call entered in the descent returns within it, fruitless, with its raise -/
theorem desc_call {q σ : Nat} {z : Fin n} {h : Nat} (h1 : a < q) (h2 : q ≤ β) (he : tr[q]? = some (.enter σ z h)) : ∃ x, Frame tr q x ∧ x ≤ β ∧ ∃ σ' o, tr[x - 1]? = some (.write σ' z o (k + 1 - h) .raise) := by
  obtain ⟨x, hfr⟩ := hR.frame q σ z h he
  have hxβ : x ≤ β := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := hfr.isOpen (q := β + 1) (by omega) (by omega)
    have := hS.desc q h1 h2
    have := hS.at_beta
    omega
  obtain ⟨σx, vx, hx, sdx, fx, hex⟩ := hfr.2.2.1
  have hf : fx = false := by
    cases hfx : fx
    · rfl
    · obtain ⟨o, σo, P, ho1, ho2, ho⟩ := (hR.ret q x σx vx hx sdx fx hfr hex).mp hfx
      have := hC.between o (by omega) (by have := hS.lt; omega)
      rw [isObs_of_output ho] at this; cases this
  subst hf
  exact ⟨x, hfr, hxβ, hR.fruitless_end q x σ z h σx vx hx sdx hfr he hex⟩

/-- Descent Origins (lem:spine-tail-origins): the cascade of a drop in the descent belongs to a frame open since a -/
theorem desc_origin {θ : Nat} {y : Fin n} (h1 : a < θ) (h2 : θ ≤ β) (hd : dropAt tr y θ = true) : m + 1 ≤ (stk tr θ).length ∧ ∀ q, a < q → q ≤ θ → (stk tr θ).length ≤ (stk tr q).length := by
  refine ⟨hS.desc θ h1 h2, ?_⟩
  obtain ⟨e, x, σ, v, h, sd, hfr, heq, hqx, hlen, hex, hall, hea⟩ := hR.casc_open (a := a) (isCasc_of_drop hd) (fun r h1' h2' => hC.between r h1' (by have := hS.lt; omega))
  intro q hq1 hq2
  have := hfr.isOpen (q := q) (by omega) (by omega)
  have := hfr.push
  omega

/-- two origin dequeues of one node in the descent are impossible: both cascades belong to the frame of z open at a -/
theorem origin_once {q₁ q₂ : Nat} {z : Fin n} (h1 : a < q₁) (h2 : q₂ ≤ β) (hlt : q₁ < q₂) (hd1 : deqAt tr z q₁ = true) (ht1 : (stk tr q₁).getLast? = some z) (hd2 : deqAt tr z q₂ = true) (ht2 : (stk tr q₂).getLast? = some z) : False := by
  have hno : ∀ q, q ≤ β → ∀ r, a < r → r < q → isObs tr r = false := fun q hq r h1' h2' => hC.between r h1' (by have := hS.lt; omega)
  obtain ⟨e₁, x₁, σ₁, v₁, hh₁, sd₁, hf₁, he₁q, hqx₁, hlen₁, hex₁, hall₁, he₁a⟩ := hR.casc_open (a := a) (isCasc_of_deq hd1) (hno q₁ (by omega))
  obtain ⟨e₂, x₂, σ₂, v₂, hh₂, sd₂, hf₂, he₂q, hqx₂, hlen₂, hex₂, hall₂, he₂a⟩ := hR.casc_open (a := a) (isCasc_of_deq hd2) (hno q₂ h2)
  obtain ⟨σe₁, u₁, k₁, hen₁⟩ := hf₁.2.1
  obtain ⟨σe₂, u₂, k₂, hen₂⟩ := hf₂.2.1
  have hu₁ : u₁ = z := by
    have := hf₁.top he₁q (by omega) hlen₁
    rw [Trace.stk_succ_enter hen₁] at this
    rw [this] at ht1; simpa using ht1
  have hu₂ : u₂ = z := by
    have := hf₂.top he₂q (by omega) hlen₂
    rw [Trace.stk_succ_enter hen₂] at this
    rw [this] at ht2; simpa using ht2
  rw [hu₁] at hen₁
  rw [hu₂] at hen₂
  have heq : e₁ = e₂ := Trace.Frame.eq_of_node (q := a) (hR.stk_nodup a) hf₁ hf₂ hen₁ hen₂ he₁a (by omega) he₂a (by omega)
  subst heq
  have hx := hf₁.exit_unique hf₂
  subst hx
  obtain ⟨r, hr1, hr2, hr⟩ := hR.deq_once q₁ q₂ z hlt hd1 hd2
  rw [hall₁ r (by omega) (by omega)] at hr
  cases hr

/-- Dequeue Count: one dequeue per drop, plus at most one as an origin -/
theorem deq_count' (z : Fin n) : cnt (fun q => deqAt tr z q = true) a β ≤ cnt (fun q => dropAt tr z q = true) a β + (if anyIn (fruitAt tr z) a β then 1 else 0) := by
  have hcasc_a : ∀ q q', q' ≤ a → a ≤ q → ¬ ∀ r, q' ≤ r → r ≤ q → isCasc tr r = true := fun q q' h1 h2 hall => by
    have := hall a h1 h2
    rw [isCasc_of_obs hC.obs_a] at this; cases this
  have hsplit : cnt (fun q => deqAt tr z q = true) a β ≤ cnt (fun q => deqAt tr z q = true ∧ (stk tr q).getLast? = some z) a β + cnt (fun q => deqAt tr z q = true ∧ ¬ (stk tr q).getLast? = some z) a β :=
    Trace.cnt_le_split _ _ a β
  have hno : cnt (fun q => deqAt tr z q = true ∧ ¬ (stk tr q).getLast? = some z) a β ≤ cnt (fun q => dropAt tr z q = true) a β := by
    refine Trace.cnt_le_of_rel _ _ (fun q q' => q' < q ∧ ∀ r, q' ≤ r → r ≤ q → isCasc tr r = true) (fun q h1 h2 hq => ?_) (fun q₁ q₂ q' a1 b1 a2 b2 c1 c2 r1 r2 => ?_)
    · obtain ⟨q', hq'q, hd', hall⟩ := hR.deq_drop q z hq.1 hq.2
      have : a < q' := Nat.lt_of_not_le fun hle => hcasc_a q q' hle (by omega) hall
      exact ⟨q', this, by omega, hd', hq'q, hall⟩
    · rcases Nat.lt_trichotomy q₁ q₂ with h | h | h
      · obtain ⟨r, hr1, hr2, hr⟩ := hR.deq_once q₁ q₂ z h c1.1 c2.1
        rw [r2.2 r (by omega) (by omega)] at hr; cases hr
      · exact h
      · obtain ⟨r, hr1, hr2, hr⟩ := hR.deq_once q₂ q₁ z h c2.1 c1.1
        rw [r1.2 r (by omega) (by omega)] at hr; cases hr
  have hor : cnt (fun q => deqAt tr z q = true ∧ (stk tr q).getLast? = some z) a β ≤ (if anyIn (fruitAt tr z) a β then 1 else 0) := by
    split
    · refine Trace.cnt_le_one _ (fun q₁ q₂ a1 b1 a2 b2 c1 c2 => ?_)
      rcases Nat.lt_trichotomy q₁ q₂ with h | h | h
      · exact (hR.origin_once hC hS a1 b2 h c1.1 c1.2 c2.1 c2.2).elim
      · exact h
      · exact (hR.origin_once hC hS a2 b1 h c2.1 c2.2 c1.1 c1.2).elim
    · next hany =>
      refine Nat.le_of_eq (Trace.cnt_zero _ (fun q h1 h2 hq => ?_))
      obtain ⟨q', hq'q, hf', hall⟩ := hR.deq_origin q z hq.1 hq.2
      have : a < q' := Nat.lt_of_not_le fun hle => hcasc_a q q' hle (by omega) hall
      exact hany (Trace.anyIn_iff.mpr ⟨q', this, by omega, hf'⟩)
  omega

/-- the core of Descent Seal: the first entry of the descent at a node x after a drop at x leads to a contradiction -/
theorem seal_core {q σ : Nat} {x : Fin n} {h θ : Nat} (h2 : q ≤ β) (he : tr[q]? = some (.enter σ x h)) (hθ1 : a < θ) (hθ2 : θ < q) (hd : dropAt tr x θ = true) (hlast : ∀ r, θ < r → r < q → dropAt tr x r = false) (hfirst : ∀ q' σ' h', θ < q' → q' < q → tr[q']? = some (.enter σ' x h') → False) : False := by
  obtain ⟨σd, o, d, hdw⟩ := Trace.dropAt_iff.mp hd
  -- the origin frame of the drop's cascade, open since a and closed before q
  obtain ⟨e₀, x₀, σ₀, v₀, h₀, sd₀, hf₀, he₀θ, hθx₀, hlen₀, hex₀, hall₀, he₀a⟩ := hR.casc_open (a := a) (isCasc_of_drop hd) (fun r h1' h2' => hC.between r h1' (by have := hS.lt; omega))
  have hx₀q : x₀ < q := by
    refine Nat.lt_of_not_le fun hle => ?_
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [← heq, he] at hex₀; cases hex₀
    · have := hall₀ q (by omega) hlt
      simp [isCasc, he] at this
  obtain ⟨σe, u, hu, hen₀⟩ := hf₀.2.1
  have hstkθ : stk tr θ = stk tr e₀ ++ [u] := by rw [hf₀.top he₀θ (by omega) hlen₀, Trace.stk_succ_enter hen₀]
  have hx₀1 : stk tr (x₀ + 1) = stk tr e₀ := by rw [Trace.stk_succ_exit hex₀, hf₀.at_exit, Trace.stk_succ_enter hen₀, List.dropLast_concat]
  -- x stays off the stack between the drop and q: an entry in between would be an earlier violation
  have hxθ : x ∉ stk tr θ := (hR.drop θ σd x o d hdw).1
  have hoff : ∀ r, θ < r → r < q → x ∉ stk tr r := by
    intro r hr1 hr2 hxr
    obtain ⟨q', hq'1, hq'2, hq'⟩ := Trace.exists_enter_of_mem (by omega) hxθ hxr
    obtain ⟨σ', h', he'⟩ := Trace.enterAt_iff.mp hq'
    rcases Nat.eq_or_lt_of_le hq'1 with heq | hlt
    · rw [← heq, hdw] at he'; cases he'
    · exact hfirst q' σ' h' hlt (by omega) he'
  -- hence no write to x in (θ, q): drops by the choice of θ, raises and fruitful writes need x on the stack
  have hnw : ∀ r σ' o' nw' kd', θ + 1 ≤ r → r < q → tr[r]? ≠ some (.write σ' x o' nw' kd') := by
    intro r σ' o' nw' kd' hr1 hr2 hw
    cases kd' with
    | drop => have := hlast r (by omega) hr2; simp [dropAt, hw] at this
    | raise => exact hoff r (by omega) hr2 (List.mem_of_getLast? (hR.raise r σ' x o' nw' hw).1)
    | fruitful => exact hoff r (by omega) hr2 (List.mem_of_getLast? (hR.fruitful r σ' x o' nw' hw).1)
  have hbar : bar tr q x = d := by rw [Trace.bar_eq_of_no_write (p₁ := θ + 1) (by omega) hnw, Trace.bar_succ_of_write hdw]
  obtain ⟨hh, hxq, hxt, hguard, -, hhead, hedges⟩ := hR.enter q σ x h he
  have hwit := hR.witness θ σd x o d hdw
  rw [hstkθ, List.dropLast_concat] at hwit
  -- μ: the least stack size on (x₀, q]; r: its last position in (x₀, q + 1]
  obtain ⟨r₀, ⟨hr₀1, hr₀2⟩, hmin'⟩ := Trace.exists_min (P := fun r => x₀ < r ∧ r ≤ q) (fun r => (stk tr r).length) q ⟨hx₀q, Nat.le_refl q⟩
  have hmin : ∀ r', x₀ < r' → r' ≤ q → (stk tr r₀).length ≤ (stk tr r').length := fun r' h1' h2' => hmin' r' ⟨h1', h2'⟩
  have hq1 : stk tr (q + 1) = stk tr q ++ [x] := Trace.stk_succ_enter he
  have hμh : (stk tr r₀).length ≤ h := by have := hmin q hx₀q (Nat.le_refl q); omega
  obtain ⟨r, hr₀r, hrq, ⟨hr1, hr2⟩, hafter⟩ := Trace.exists_last (P := fun r => x₀ < r ∧ (stk tr r).length = (stk tr r₀).length) (hi := q + 1) r₀ (by omega) ⟨hr₀1, rfl⟩
  have habove : ∀ r', r < r' → r' ≤ q + 1 → (stk tr r₀).length < (stk tr r').length := by
    intro r' h1' h2'
    rcases Nat.lt_or_ge r' (q + 1) with hlt | hge
    · have := hmin r' (by omega) (by omega)
      have hna := hafter r' h1' h2'
      simp only [not_and] at hna
      have := hna (by omega)
      omega
    · have : r' = q + 1 := by omega
      subst this
      rw [hq1]; simp; omega
  have hrq' : r ≤ q := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have : r = q + 1 := by omega
    subst this
    rw [hq1] at hr2; simp at hr2; omega
  obtain ⟨σ₁, q₁, h₁, he₁⟩ := Trace.enter_of_length_lt (tr := tr) (p := r) (by have := habove (r + 1) (by omega) (by omega); omega)
  -- the frame entered at r is a call of the descent, so it returns within it (Call--Phase Correspondence)
  obtain ⟨x₁, hf₁, hx₁β, -⟩ := hR.desc_call hC hS (q := r) (by omega) (by omega) he₁
  have hqx₁ : q < x₁ := by
    refine Nat.lt_of_not_le fun hle => ?_
    have := habove (x₁ + 1) (by have := hf₁.1; omega) (by omega)
    have := hf₁.2.2.2.1
    omega
  -- the bounded path R: the stack at q + 1 up to depth μ, then shortcut to t via x and the witness walk
  have hpre : (stk tr (q + 1)).take ((stk tr r).length + 1) = stk tr (r + 1) := hf₁.prefix (by omega) (by omega)
  have hpers : (stk tr (q + 1)).take (stk tr r).length = (stk tr (x₀ + 1)).take (stk tr r).length := Trace.stk_take_persist (by omega) (fun i hi1 hi2 => by
    rcases Nat.lt_or_ge i (q + 1) with hlt | hge
    · rw [hr2]; exact hmin i (by omega) (by omega)
    · have : i = q + 1 := by omega
      subst this; rw [hq1, hr2]; simp; omega)
  rw [hx₀1] at hpers
  have hnd := hR.stk_nodup (q + 1)
  obtain ⟨R, hRb, hRpre⟩ := Graph.bounded_of_stack_walk (k := k) (P := (stk tr (q + 1)).take (stk tr r).length) (M := (stk tr (q + 1)).drop (stk tr r).length) (X := stk tr e₀) (d := d)
    (fun z hz => by rw [hpers] at hz; exact List.mem_of_mem_take hz)
    (by rw [List.take_append_drop, hq1]; exact hhead)
    (by rw [List.take_append_drop, hq1]; exact hedges)
    (by rw [List.take_append_drop]; exact hnd)
    (by rw [hq1, List.drop_append_of_le_length (by rw [hr2]; omega)]; simp)
    hwit
    (by rw [List.take_append_drop, hq1]; simp; omega)
  rw [← List.take_add, hpre] at hRpre
  obtain ⟨o', σo, ho1, ho2, hout⟩ := hR.complete r x₁ hf₁ R hRb hRpre
  have := hC.between o' (by omega) (by have := hS.lt; omega)
  rw [isObs_of_output hout] at this
  cases this

/-- Descent Seal (lem:period-seal): no call of the descent is entered at a node that received a drop earlier in the descent -/
theorem seal_enter {q σ : Nat} {x : Fin n} {h : Nat} (h1 : a < q) (h2 : q ≤ β) (he : tr[q]? = some (.enter σ x h)) {θ : Nat} (hθ1 : a < θ) (hθ2 : θ < q) (hd : dropAt tr x θ = true) : False := by
  obtain ⟨q₀, hq01, hq0q, ⟨hq02, σ₀, x₀, h₀, θ₀, he₀, hθ01, hθ02, hd₀⟩, hfirst⟩ := Trace.exists_first (P := fun q => q ≤ β ∧ ∃ σ x h θ, tr[q]? = some (.enter σ x h) ∧ a < θ ∧ θ < q ∧ dropAt tr x θ = true) (lo := a) q h1 ⟨h2, σ, x, h, θ, he, hθ1, hθ2, hd⟩
  obtain ⟨θ₁, hθ01', hθ1q, hd₁, hlast⟩ := Trace.exists_last (P := fun r => dropAt tr x₀ r = true) (hi := q₀ - 1) θ₀ (by omega) hd₀
  refine hR.seal_core hC hS (q := q₀) hq02 he₀ (θ := θ₁) (by omega) (by omega) hd₁ (fun r hr1 hr2 => ?_) (fun q' σ' h' hq'1 hq'2 he' => hfirst q' (by omega) hq'2 ⟨by omega, σ', x₀, h', θ₁, he', by omega, hq'1, hd₁⟩)
  have := hlast r hr1 (by omega)
  simpa using this

/-- after a drop at z in the descent, only drops write z there -/
theorem seal_write {θ : Nat} {z : Fin n} (h1 : a < θ) (hd : dropAt tr z θ = true) {q σ o nw : Nat} {kd : Kind} (hq1 : θ < q) (hq2 : q ≤ β) (hw : tr[q]? = some (.write σ z o nw kd)) : kd = .drop := by
  obtain ⟨σd, od, nwd, hdw⟩ := Trace.dropAt_iff.mp hd
  have hzθ : z ∉ stk tr θ := (hR.drop θ σd z od nwd hdw).1
  have hoff : z ∈ stk tr q → False := fun hzq => by
    obtain ⟨q', hq'1, hq'2, hq'⟩ := Trace.exists_enter_of_mem (by omega) hzθ hzq
    obtain ⟨σ', h', he'⟩ := Trace.enterAt_iff.mp hq'
    rcases Nat.eq_or_lt_of_le hq'1 with heq | hlt
    · rw [← heq, hdw] at he'; cases he'
    · exact hR.seal_enter hC hS (q := q') (by omega) (by omega) he' (θ := θ) h1 hlt hd
  cases kd with
  | drop => rfl
  | raise => exact (hoff (List.mem_of_getLast? (hR.raise q σ z o nw hw).1)).elim
  | fruitful => exact (hoff (List.mem_of_getLast? (hR.fruitful q σ z o nw hw).1)).elim

/-- One Entry per Pair per Phase (lem:one-entry): a node is not entered twice at the same depth in one phase.  The first call
    returns fruitless before the second entry and raises b[z] to k + 1 - h; the guard of the second entry needs b[z] ≤ k - h, so
    a drop at z lies in between, which Descent Seal resp. Ascent Purity excludes. -/
theorem one_entry' {q₁ q₂ σ₁ σ₂ : Nat} {z : Fin n} {h : Nat} (hlt : q₁ < q₂) (hph : (a < q₁ ∧ q₂ ≤ β) ∨ (β < q₁ ∧ q₂ ≤ c)) (he₁ : tr[q₁]? = some (.enter σ₁ z h)) (he₂ : tr[q₂]? = some (.enter σ₂ z h)) : False := by
  have ha1 : a < q₁ := by
    rcases hph with hp | hp
    · exact hp.1
    · have := hS.le; omega
  have hc2 : q₂ ≤ c := by
    rcases hph with hp | hp
    · have := hS.lt; omega
    · exact hp.2
  obtain ⟨x₁, hfr⟩ := hR.frame q₁ σ₁ z h he₁
  have hq₁x₁ := hfr.1
  -- z stays on the stack while its frame is open, so the frame exits before q₂
  have hx₁ : x₁ < q₂ := by
    refine Nat.lt_of_not_le fun hle => ?_
    have hp := hfr.prefix hlt hle
    rw [Trace.stk_succ_enter he₁] at hp
    have hz : z ∈ (stk tr q₂).take ((stk tr q₁).length + 1) := by rw [hp]; simp
    exact (hR.enter q₂ σ₂ z h he₂).2.1 (List.mem_of_mem_take hz)
  -- the frame is fruitless: an output inside would lie strictly between a and c
  obtain ⟨σx, vx, hx, sdx, fx, hex⟩ := hfr.2.2.1
  have hf : fx = false := by
    cases hfx : fx
    · rfl
    · obtain ⟨o, σo, P, ho1, ho2, ho⟩ := (hR.ret q₁ x₁ σx vx hx sdx fx hfr hex).mp hfx
      have := hC.between o (by omega) (by omega)
      rw [isObs_of_output ho] at this; cases this
  subst hf
  obtain ⟨σr, o, hraise⟩ := hR.fruitless_end q₁ x₁ σ₁ z h σx vx hx sdx hfr he₁ hex
  have hbx : bar tr (x₁ + 1) z = k + 1 - h := by
    have hb := Trace.bar_succ_of_write hraise
    rw [show x₁ - 1 + 1 = x₁ by have := hfr.1; omega] at hb
    rw [Trace.not_write_of_exit hex, hb]
  have hguard := (hR.enter q₂ σ₂ z h he₂).2.2.2.1
  have hdrop : ∃ θ, x₁ + 1 ≤ θ ∧ θ < q₂ ∧ dropAt tr z θ = true := by
    refine Classical.byContradiction fun hne => ?_
    have hup : ∀ r σ o nw kd, x₁ + 1 ≤ r → r < q₂ → tr[r]? = some (.write σ z o nw kd) → bar tr r z ≤ nw := by
      intro r σ o nw kd hr1 hr2 hw
      have hold := hR.write_old r σ z o nw kd hw
      cases kd with
      | drop => exact absurd ⟨r, hr1, hr2, by simp [dropAt, hw]⟩ hne
      | raise => have := (hR.raise r σ z o nw hw).2.2; omega
      | fruitful => have := (hR.fruitful r σ z o nw hw).2.2.1; omega
    have := Trace.bar_ge_of_raising (by omega) hup
    omega
  obtain ⟨θ, hθ1, hθ2, hd⟩ := hdrop
  rcases hph with ⟨-, hβ⟩ | ⟨hβ, -⟩
  · exact hR.seal_enter hC hS (q := q₂) (by omega) hβ he₂ (θ := θ) (by omega) hθ2 hd
  · exact hR.asc_pure hC hS (q := θ) (by omega) (by omega) (isCasc_of_drop hd)

/-- the v2 phase lemmas for one interval -/
theorem intervalFacts : IntervalFacts tr k a c m β where
  asc_pure q h1 h2 := ⟨fun σ x o nw hw => hR.asc_pure hC hS h1 h2 (by simp [isCasc, hw]), fun σ x o nw hw => hR.asc_pure hC hS h1 h2 (by simp [isCasc, hw]), fun σ v d hw => hR.asc_pure hC hS h1 h2 (by simp [isCasc, hw])⟩
  desc_call q σ z h h1 h2 he := hR.desc_call hC hS h1 h2 he
  desc_origin θ y h1 h2 hd := hR.desc_origin hC hS h1 h2 hd
  deq_count z := hR.deq_count' hC hS z
  desc_seal θ z h1 h2 hd q hq1 hq2 := by
    refine ⟨?_, fun σ o nw kd hw => hR.seal_write hC hS h1 hd hq1 hq2 hw⟩
    cases he : enterAt tr z q
    · rfl
    · obtain ⟨σ, h, he'⟩ := Trace.enterAt_iff.mp he
      exact (hR.seal_enter hC hS (q := q) (by omega) hq2 he' (θ := θ) h1 hq1 hd).elim
  one_entry q₁ q₂ σ₁ σ₂ z h hne hph he₁ he₂ := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · refine hR.one_entry' hC hS hlt ?_ he₁ he₂
      rcases hph with hp | hp
      · exact Or.inl ⟨hp.1, hp.2.2.2⟩
      · exact Or.inr ⟨hp.1, hp.2.2.2⟩
    · refine hR.one_entry' hC hS hlt ?_ he₂ he₁
      rcases hph with hp | hp
      · exact Or.inl ⟨hp.2.2.1, hp.2.1⟩
      · exact Or.inr ⟨hp.2.2.1, hp.2.1⟩

end interval

/-- Stage 3b result: the facts of the v3 counting follow from the run facts -/
theorem toDelayFacts : DelayFacts G s t k tr where
  enter q σ z h he := by obtain ⟨a1, a2, a3, a4, a5, -, -⟩ := hR.enter q σ z h he; exact ⟨a1, a2, a3, a4, a5⟩
  exit q σ v h sd f he := (hR.exit q σ v h sd f he).1
  output := hR.output
  write_old := hR.write_old
  raise := hR.raise
  fruitful := hR.fruitful
  drop := hR.drop
  mono := hR.mono
  cascade θ σ y o nw hd := by
    obtain ⟨e, x, σ', v, h, sd, hfr, h1, h2, hlen, hex, hall⟩ := hR.casc θ (by simp [isCasc, hd])
    exact ⟨e, x, hfr, h1, h2, hlen, fun q σ'' o' nw' kd' hq1 hq2 hw => hR.drop_last θ y (by simp [dropAt, hd]) q σ'' o' nw' kd' hq1 (fun r' hr1 hr2 => hall r' hr1 (by omega)) hw⟩
  onedrop θ₁ θ₂ y hlt hd1 hd2 := by
    obtain ⟨e, x, σ, v, h, sd, hfr, h1, h2, hlen, hex, hall⟩ := hR.casc θ₁ (isCasc_of_drop hd1)
    obtain ⟨σ', o, nw, hw⟩ := Trace.dropAt_iff.mp hd2
    have hxθ : x < θ₂ := by
      refine Nat.lt_of_not_le fun hle => ?_
      rcases Nat.eq_or_lt_of_le hle with heq | hlt'
      · rw [heq, hex] at hw; cases hw
      · exact hR.drop_last θ₁ y hd1 θ₂ σ' o nw .drop hlt (fun r' hr1 hr2 => hall r' hr1 (by omega)) hw
    refine ⟨x + 1, by omega, by omega, ?_⟩
    have := hfr.2.2.2.1; have := hfr.push; omega
  scan e x σ u h hfr he y hy := by
    obtain ⟨q, h1, h2, hst, hcase⟩ := hR.scan e x σ u h hfr he y hy
    refine ⟨q, h1, h2, ?_⟩
    rcases hcase with hc | hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · refine Or.inr (Or.inr (Or.inl ⟨hc, ?_⟩))
      rw [hst, hfr.push, (hR.enter e σ u h he).1]
    · exact Or.inr (Or.inr (Or.inr hc))
  bar_t := hR.bar_t
  interval a c m β hC hS := hR.intervalFacts hC hS

end RunFacts

/-- Stage 3b: the worst-case delay 2k(n+m) (v3) follows from `RunFacts` for the run -/
theorem worst_case_of_run (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hk : 0 < k) (hR : RunFacts G s t k (bsdfs G s t k)) : ∀ x ∈ (obsSteps (bsdfs G s t k)).zip (obsSteps (bsdfs G s t k)).tail, x.2 - x.1 ≤ 2 * k * (n + G.m) :=
  worst_case_of_facts G s t k hG hk hR.toDelayFacts
