import Bsdfs.Basic

/-!
  Proof of `bsdfs_sound`: in path mode, every output of `bsdfs` is a simple s-t path with at most k edges.

  Hoare triples over `M n = StateM (St n)`, discharged by `mvcgen` (Std.Do).  The argument uses the explicit
  `w ∉ S` test of `search` only, no barrier semantics:
  - stack invariant: inside `search v h`, S ++ [v] is a simple path from s with edges in G that avoids t, |S| = h;
  - `fruitful` leaves S and the outputs of the trace unchanged (`fruitful_frame`);
  - `search` returns with S unchanged; induction on k - h, the termination measure of `search`.
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

@[simp] theorem outputs_nil : outputs ([] : List (Ev n)) = [] := rfl

@[simp] theorem outputs_cons (e : Ev n) (l : List (Ev n)) : outputs (e :: l) = (match e with | .output _ p => [p] | _ => []) ++ outputs l := by
  cases e <;> rfl

@[simp] theorem outputs_append (l₁ l₂ : List (Ev n)) : outputs (l₁ ++ l₂) = outputs l₁ ++ outputs l₂ := List.filterMap_append

/-- `fruitful` changes neither the stack nor the outputs of the trace -/
theorem fruitful_frame (G : Graph n) (v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (O0 : List (List (Fin n))) :
    ⦃fun st => ⌜st.S = S0 ∧ outputs st.trace.toList = O0⌝⦄ fruitful G v sd ⦃⇓ _ st => ⌜st.S = S0 ∧ outputs st.trace.toList = O0⌝⦄ := by
  mvcgen [fruitful, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack] invariants
  · ⇓⟨_, _⟩ st => ⌜st.S = S0 ∧ outputs st.trace.toList = O0⌝
  · ⇓⟨_, _⟩ st => ⌜st.S = S0 ∧ outputs st.trace.toList = O0⌝
  all_goals simp_all +zetaDelta

/-! ## Paths as node lists -/

/-- an edge of l ++ [b] is an edge of l or the new last edge -/
theorem mem_zip_tail_snoc {α : Type} {l : List α} {b : α} {e : α × α} (he : e ∈ (l ++ [b]).zip (l ++ [b]).tail) : e ∈ l.zip l.tail ∨ (l.getLast? = some e.1 ∧ e.2 = b) := by
  induction l with
  | nil => simp at he
  | cons x l ih =>
    cases l with
    | nil => simp at he; simp [he]
    | cons y l =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he ih ⊢
      rcases he with he | he
      · exact Or.inl (Or.inl he)
      · rcases ih he with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (by simpa [List.getLast?_cons_cons] using h)

/-- L is a simple path from s with edges in G that avoids t (the stack invariant) -/
def StackPath (G : Graph n) (s t : Fin n) (L : List (Fin n)) : Prop :=
  L.head? = some s ∧ L.Nodup ∧ t ∉ L ∧ ∀ e ∈ L.zip L.tail, e.2 ∈ G.succ e.1

/-- every output in the trace is a simple s-t path with at most k edges -/
def OutputsSound (G : Graph n) (s t : Fin n) (k : Nat) (tr : Array (Ev n)) : Prop :=
  ∀ p ∈ outputs tr.toList, G.BoundedPath k s t p

theorem nodup_snoc {α : Type} {L : List α} {w : α} (hnd : L.Nodup) (hw : w ∉ L) : (L ++ [w]).Nodup :=
  List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact hw ha⟩

/-- the edges of L ++ [v] ++ [w]: those of L ++ [v] and (v, w) -/
theorem edges_snoc {G : Graph n} {L : List (Fin n)} {v w : Fin n} (hedge : ∀ e ∈ (L ++ [v]).zip (L ++ [v]).tail, e.2 ∈ G.succ e.1) (hw : w ∈ G.succ v) :
    ∀ e ∈ (L ++ [v] ++ [w]).zip (L ++ [v] ++ [w]).tail, e.2 ∈ G.succ e.1 := by
  intro e he
  rcases mem_zip_tail_snoc he with h | ⟨h1, h2⟩
  · exact hedge e h
  · simp at h1; subst h1; rw [h2]; exact hw

theorem StackPath.snoc {G : Graph n} {s t v w : Fin n} {L : List (Fin n)} (hL : StackPath G s t (L ++ [v])) (hw : w ∈ G.succ v) (hwL : w ∉ L ++ [v]) (hwt : w ≠ t) : StackPath G s t (L ++ [v] ++ [w]) := by
  obtain ⟨hhead, hnd, hts, hedge⟩ := hL
  refine ⟨?_, nodup_snoc hnd hwL, ?_, edges_snoc hedge hw⟩
  · cases L <;> simp_all
  · simp only [List.mem_append, List.mem_singleton, not_or] at hts ⊢; exact ⟨⟨hts.1, hts.2⟩, fun h => hwt h.symm⟩

theorem StackPath.bounded {G : Graph n} {s t v : Fin n} {k : Nat} {L : List (Fin n)} (hL : StackPath G s t (L ++ [v])) (ht : t ∈ G.succ v) (hlen : L.length < k) : G.BoundedPath k s t (L ++ [v] ++ [t]) := by
  obtain ⟨hhead, hnd, hts, hedge⟩ := hL
  refine ⟨?_, by simp, nodup_snoc hnd hts, by simp; omega, edges_snoc hedge ht⟩
  cases L <;> simp_all

theorem OutputsSound.push_iff {G : Graph n} {s t : Fin n} {k : Nat} {tr : Array (Ev n)} {e : Ev n} : OutputsSound G s t k (tr.push e) ↔ OutputsSound G s t k tr ∧ ∀ p ∈ outputs [e], G.BoundedPath k s t p := by
  simp only [OutputsSound, Array.toList_push, outputs_append, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

/-! ## Search -/

/-- `search v h` returns with the stack unchanged and keeps the outputs sound; induction on k - h -/
theorem search_sound (G : Graph n) (s t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) :
    ⦃fun st => ⌜st.S = S0 ∧ StackPath G s t (S0.toList ++ [v]) ∧ S0.size = h ∧ h ≤ k ∧ OutputsSound G s t k st.trace⌝⦄
    search G t k v h
    ⦃⇓ _ st => ⌜st.S = S0 ∧ OutputsSound G s t k st.trace⌝⦄ := by
  -- spec of the recursive call; vacuous unless h < k
  have ih : ∀ w (S1 : Array (Fin n)), ⦃fun st => ⌜st.S = S1 ∧ StackPath G s t (S1.toList ++ [w]) ∧ S1.size = h + 1 ∧ h + 1 ≤ k ∧ OutputsSound G s t k st.trace⌝⦄ search G t k w (h + 1) ⦃⇓ _ st => ⌜st.S = S1 ∧ OutputsSound G s t k st.trace⌝⦄ := by
    intro w S1
    by_cases hk : h < k
    · exact search_sound G s t k (h + 1) w S1
    · intro st hP
      exact absurd hP.2.2.2.1 (by omega)
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, ih, fruitful_frame] invariants
  · ⇓⟨_, _⟩ st => ⌜st.S = S0.push v ∧ OutputsSound G s t k st.trace⌝
  case vc1.step.isTrue.isTrue =>
    -- output event: the stack S0 ++ [v] plus t is a bounded path
    obtain ⟨-, hstk, hsz, -, -⟩ := ‹_ = S0 ∧ StackPath G s t (S0.toList ++ [v]) ∧ _›
    obtain ⟨hS, htr⟩ := ‹_ = S0.push v ∧ OutputsSound G s t k _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have hlt := ‹_ + h < k›
    have hcur := ‹_ = t›
    rw [hcur] at hmem
    simp +zetaDelta [OutputsSound.push_iff, hS, htr]
    simpa using StackPath.bounded hstk hmem (by simp [hsz]; omega)
  case vc2.step.isTrue.isFalse.isTrue.pre =>
    -- recursive call: the stack extended by w is a stack path again
    obtain ⟨-, hstk, hsz, -, -⟩ := ‹_ = S0 ∧ StackPath G s t (S0.toList ++ [v]) ∧ _›
    obtain ⟨hS, htr⟩ := ‹_ = S0.push v ∧ OutputsSound G s t k _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have hlt := ‹_ + h < k›
    have hnt := ‹¬_ = t›
    have hnS := ‹¬_ ∈ _›
    simp +zetaDelta [hS, htr, hsz] at hnS ⊢
    exact ⟨by simpa using StackPath.snoc hstk hmem (by simpa using hnS) hnt, by omega⟩
  case vc7.post.success.isTrue.post.success =>
    -- after fruitful: same outputs as before
    obtain ⟨hS, htr⟩ := ‹_ = S0.push v ∧ OutputsSound G s t k _›
    obtain ⟨hS', hout⟩ := ‹_ = _ ∧ outputs _ = outputs _›
    simp +zetaDelta [OutputsSound.push_iff, hS', hS]
    unfold OutputsSound at htr ⊢
    rwa [hout]
  -- the remaining VCs only push non-output events, push v, or pop
  all_goals simp_all +zetaDelta [OutputsSound.push_iff]
termination_by k - h

/-! ## The theorem -/

variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- path mode: every output is a simple s-t path with at most k edges -/
theorem bsdfs_sound (hst : s ≠ t) : ∀ p ∈ outputs (bsdfs G s t k), G.BoundedPath k s t p := by
  -- the root call: the stack [s] is a stack path because s ≠ t
  refine bsdfs_of_root (fun st => st.S = #[] ∧ StackPath G s t ((#[] : Array (Fin n)).toList ++ [s]) ∧ (#[] : Array (Fin n)).size = 0 ∧ 0 ≤ k ∧ OutputsSound G s t k st.trace)
    (fun T => ∀ p ∈ outputs T, G.BoundedPath k s t p) ⟨rfl, ⟨rfl, by simp, by simpa using Ne.symm hst, by simp⟩, rfl, Nat.zero_le k, by simp [OutputsSound]⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  simpa [OutputsSound] using ((StateM.triple_iff _ _ _).mp (search_sound G s t k 0 s #[]) st hpre).2
