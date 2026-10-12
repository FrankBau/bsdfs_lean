import Bsdfs.Paths

/-!
  The cascade `fruitful G v sd` as a breadth-first search: every enqueued node keeps the value it was enqueued with, every node is
  enqueued at most once (so the queue has at most n entries and `for i in List.range n` processes all of them), and every
  processed pair (q, d) leaves its off-stack predecessors with barrier at most d + 1.  This gives Update Repairs
  (lem:update-repairs-consistency) without exact distances, and the lower bound of every cascade write (lem:update-distance-bound).
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

@[simp] theorem vset_get (b : Vector Nat n) (p : Fin n) (j : Nat) (hj : j < n) (c : Nat) : (b.set p.1 c p.2)[j] = if p.1 = j then c else b[j] :=
  Vector.getElem_set p.2 hj

theorem range_eq_append_cons {pref suff : List Nat} {cur : Nat} (h : List.range n = pref ++ cur :: suff) : cur = pref.length := by
  have h1 : (List.range n)[pref.length]'(by rw [h]; simp) = cur := by simp only [h]; simp
  simp at h1
  exact h1.symm

/-- facts about the cascade queue that hold between any two steps -/
structure CascCore (G : Graph n) (t v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (queue : Array (Fin n × Nat)) (b : Vector Nat n) : Prop where
  pos : 0 < queue.size
  head : queue[0]'pos = (v, sd)
  val : ∀ j (hj : j < queue.size), b[queue[j].1] = queue[j].2
  nodup : (queue.toList.map Prod.fst).Nodup
  off : ∀ j (hj : j < queue.size), 0 < j → queue[j].1 ∉ S0.toList ∧ queue[j].1 ≠ v
  sorted : ∀ j j' (hj : j < queue.size) (hj' : j' < queue.size), j ≤ j' → queue[j].2 ≤ queue[j'].2
  low : ∀ x, x ≠ v → b[x] ≤ b0[x]
  same : ∀ x, x ≠ v → (∀ j (hj : j < queue.size), queue[j].1 ≠ x) → b[x] = b0[x]
  walk : ∀ j (hj : j < queue.size), G.WalkLE S0.toList t queue[j].1 queue[j].2

/-- every predecessor in ps that is off the stack has barrier at most d + 1 -/
def Processed (v : Fin n) (S0 : Array (Fin n)) (b : Vector Nat n) (d : Nat) (ps : List (Fin n)) : Prop :=
  ∀ p ∈ ps, p ∉ S0.toList → p ≠ v → b[p] ≤ d + 1

/-- invariant of the outer loop at read index i -/
structure CascOuter (G : Graph n) (t v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (i : Nat) (queue : Array (Fin n × Nat)) (b : Vector Nat n) : Prop extends CascCore G t v sd S0 b0 queue b where
  bound : ∀ (hi : i < queue.size) j (hj : j < queue.size), queue[j].2 ≤ queue[i].2 + 1
  done : ∀ j (hj : j < queue.size), j < i → Processed v S0 b queue[j].2 (G.pred queue[j].1)

/-- invariant of the inner loop while the pair e at index i is processed, after the predecessors ps -/
structure CascInner (G : Graph n) (t v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (i : Nat) (e : Fin n × Nat) (ps : List (Fin n)) (queue : Array (Fin n × Nat)) (b : Vector Nat n) : Prop extends CascCore G t v sd S0 b0 queue b where
  entry : ∃ hi : i < queue.size, queue[i] = e
  bound : ∀ j (hj : j < queue.size), queue[j].2 ≤ e.2 + 1
  done : ∀ j (hj : j < queue.size), j < i → Processed v S0 b queue[j].2 (G.pred queue[j].1)
  part : Processed v S0 b e.2 ps

/-- what the cascade guarantees: Update Repairs and the barrier facts used by `search` -/
structure CascPost (G : Graph n) (t v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (b0 b : Vector Nat n) : Prop where
  bv : b[v] = sd
  stack : ∀ x, x ∈ S0.toList → b[x] = b0[x]
  low : ∀ x, x ≠ v → b[x] ≤ b0[x]
  mon : ∀ y, b0[y] ≤ b[y] ∨ G.WalkLE S0.toList t y b[y]
  repair : EC G b0 (S0.toList ++ [v]) → ∀ x y, y ∈ G.succ x → x ∉ S0.toList → y ∉ S0.toList → x ≠ v → b[x] ≤ b[y] + 1

section cascade
variable {G : Graph n} {t v : Fin n} {sd : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n}

theorem CascCore.size_le {queue : Array (Fin n × Nat)} {b : Vector Nat n} (h : CascCore G t v sd S0 b0 queue b) : queue.size ≤ n := by
  have := nodup_length_le _ h.nodup
  simpa using this

theorem CascCore.not_mem {queue : Array (Fin n × Nat)} {b : Vector Nat n} {p : Fin n} {c : Nat} (h : CascCore G t v sd S0 b0 queue b) (hbound : ∀ j (hj : j < queue.size), queue[j].2 ≤ c) (hp : c < b[p]) : ∀ j (hj : j < queue.size), queue[j].1 ≠ p := by
  intro j hj hjp
  have h1 := h.val j hj
  have h2 := hbound j hj
  simp only [hjp] at h1
  omega

theorem casc_init (hw : G.WalkLE S0.toList t v sd) : CascOuter G t v sd S0 b0 0 #[(v, sd)] (b0.set v.1 sd v.2) where
  pos := by simp
  head := rfl
  val := by intro j hj; simp at hj; subst hj; simp
  nodup := by simp
  off := by intro j hj h0; simp at hj; omega
  sorted := by intro j j' hj hj' _; simp at hj hj'; subst hj; subst hj'; simp
  low := by intro x hx; simp [Fin.val_inj, Ne.symm hx]
  same := by intro x hx _; simp [Fin.val_inj, Ne.symm hx]
  walk := by intro j hj; simp at hj; subst hj; simpa using hw
  bound := by intro _ j hj; simp at hj; subst hj; simp
  done := by intro j _ hj; omega

theorem casc_dequeue {i : Nat} {queue : Array (Fin n × Nat)} {b : Vector Nat n} (h : CascOuter G t v sd S0 b0 i queue b) (hi : i < queue.size) : CascInner G t v sd S0 b0 i queue[i] [] queue b where
  toCascCore := h.toCascCore
  entry := ⟨hi, rfl⟩
  bound := h.bound hi
  done := h.done
  part := by intro p hp; simp at hp

theorem casc_relax (hG : G.WF) (hv : v ∉ S0.toList) {i : Nat} {e : Fin n × Nat} {ps : List (Fin n)} {queue : Array (Fin n × Nat)} {b : Vector Nat n} {p : Fin n} (h : CascInner G t v sd S0 b0 i e ps queue b) (hp : p ∈ G.pred e.1) (hpS : p ∉ S0.toList) (hpv : p ≠ v) (hlt : e.2 + 1 < b[p]) :
    CascInner G t v sd S0 b0 i e (ps ++ [p]) (queue.push (p, e.2 + 1)) (b.set p.1 (e.2 + 1) p.2) := by
  have hnot := h.not_mem h.bound hlt
  obtain ⟨hi, hie⟩ := h.entry
  have he1 : e.1 ∉ S0.toList := by
    by_cases h0 : i = 0
    · subst h0; have := h.head; rw [hie] at this; rw [this]; exact hv
    · have := (h.off i hi (by omega)).1; rwa [hie] at this
  have hwalk : G.WalkLE S0.toList t p (e.2 + 1) := by
    obtain ⟨l, hl, hw⟩ := h.walk i hi
    rw [hie] at hl hw
    exact ⟨l + 1, by omega, .step ((hG.rev p e.1).mpr hp) he1 hw⟩
  have hbp : ∀ x : Fin n, (b.set p.1 (e.2 + 1) p.2)[x] ≤ b[x] := by
    intro x; by_cases hx : p = x
    · subst hx; simp only [Fin.getElem_fin] at hlt ⊢; simp; omega
    · simp [Fin.val_inj, hx]
  refine { pos := by simp, head := ?_, val := ?_, nodup := ?_, off := ?_, sorted := ?_, low := ?_, same := ?_, walk := ?_, entry := ?_, bound := ?_, done := ?_, part := ?_ }
  · rw [Array.getElem_push_lt h.pos]; exact h.head
  · intro j hj
    by_cases hj' : j < queue.size
    · have e1 : (queue.push (p, e.2 + 1))[j] = queue[j] := Array.getElem_push_lt hj'
      have h1 := h.val j hj'
      have hne := hnot j hj'
      simp only [e1]
      simp only [Fin.getElem_fin] at h1 ⊢
      simp [Fin.val_inj, Ne.symm hne, h1]
    · have hjs : j = queue.size := by simp at hj; omega
      subst hjs
      simp only [Array.getElem_push_eq]
      simp
  · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    intro a ha c hc
    simp only [List.mem_singleton] at hc
    subst hc
    simp only [List.mem_map] at ha
    obtain ⟨⟨a', da⟩, ha', rfl⟩ := ha
    obtain ⟨j, hj, hja⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp ha')
    intro heq
    exact hnot j hj (by rw [hja]; exact heq)
  · intro j hj h0
    rw [Array.getElem_push]
    split
    · next hj' => exact h.off j hj' h0
    · exact ⟨hpS, hpv⟩
  · intro j j' hj hj' hjj
    rw [Array.getElem_push, Array.getElem_push]
    split <;> split
    · next hj1 hj2 => exact h.sorted j j' hj1 hj2 hjj
    · next hj1 _ => exact h.bound j hj1
    · next hj1 hj2 => simp at hj hj'; omega
    · exact Nat.le_refl _
  · intro x hx
    by_cases hpx : p = x
    · subst hpx; have h1 := h.low p hx; simp only [Fin.getElem_fin] at h1 hlt ⊢; simp; omega
    · simp [Fin.val_inj, hpx]; exact h.low x hx
  · intro x hx hq
    have hpx : p ≠ x := by
      intro hpx; have := hq queue.size (by simp); simp at this; exact this hpx
    simp [Fin.val_inj, hpx]
    exact h.same x hx (fun j hj => by have := hq j (by simp; omega); rwa [Array.getElem_push_lt hj] at this)
  · intro j hj
    rw [Array.getElem_push]
    split
    · next hj' => exact h.walk j hj'
    · exact hwalk
  · exact ⟨by simp; omega, by rw [Array.getElem_push_lt hi]; exact hie⟩
  · intro j hj
    rw [Array.getElem_push]
    split
    · next hj' => exact h.bound j hj'
    · simp
  · intro j hj hji q hq hqS hqv
    have hj' : j < queue.size := by omega
    have := h.done j hj' hji q (by rwa [Array.getElem_push_lt hj'] at hq) hqS hqv
    rw [Array.getElem_push_lt hj']
    exact Nat.le_trans (hbp q) this
  · intro q hq hqS hqv
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact Nat.le_trans (hbp q) (h.part q hq hqS hqv)
    · simp

theorem casc_skip {i : Nat} {e : Fin n × Nat} {ps : List (Fin n)} {queue : Array (Fin n × Nat)} {b : Vector Nat n} {p : Fin n} (h : CascInner G t v sd S0 b0 i e ps queue b) (hno : p ∉ S0.toList → p ≠ v → b[p] ≤ e.2 + 1) :
    CascInner G t v sd S0 b0 i e (ps ++ [p]) queue b := by
  refine { h with part := ?_ }
  intro q hq hqS hqv
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact h.part q hq hqS hqv
  · exact hno hqS hqv

theorem casc_next {i : Nat} {e : Fin n × Nat} {queue : Array (Fin n × Nat)} {b : Vector Nat n} (h : CascInner G t v sd S0 b0 i e (G.pred e.1) queue b) : CascOuter G t v sd S0 b0 (i + 1) queue b where
  toCascCore := h.toCascCore
  bound := by
    intro hi j hj
    obtain ⟨hi0, hie⟩ := h.entry
    have h1 := h.sorted i (i + 1) hi0 hi (by omega)
    rw [hie] at h1
    have h2 := h.bound j hj
    omega
  done := by
    intro j hj hji
    obtain ⟨hi0, hie⟩ := h.entry
    by_cases hji' : j < i
    · exact h.done j hj hji'
    · have : j = i := by omega
      subst this
      rw [hie]; exact h.part

theorem casc_break {i : Nat} {queue : Array (Fin n × Nat)} {b : Vector Nat n} (h : CascOuter G t v sd S0 b0 i queue b) (hi : ¬ i < queue.size) : CascOuter G t v sd S0 b0 n queue b where
  toCascCore := h.toCascCore
  bound := by intro hn; have := h.size_le; omega
  done := by intro j hj _; exact h.done j hj (by omega)

theorem casc_final (hG : G.WF) (hv : v ∉ S0.toList) {queue : Array (Fin n × Nat)} {b : Vector Nat n} (h : CascOuter G t v sd S0 b0 n queue b) : CascPost G t v sd S0 b0 b := by
  have hall : ∀ j (hj : j < queue.size), Processed v S0 b queue[j].2 (G.pred queue[j].1) := fun j hj => h.done j hj (by have := h.size_le; omega)
  have h0 := h.head
  have hv0 : b[v] = sd := by have := h.val 0 h.pos; simp only [h0] at this; exact this
  have hmem : ∀ y, y ≠ v → (∀ j (hj : j < queue.size), queue[j].1 ≠ y) ∨ ∃ j, ∃ hj : j < queue.size, queue[j].1 = y := by
    intro y _
    by_cases hq : ∃ j, ∃ hj : j < queue.size, queue[j].1 = y
    · exact Or.inr hq
    · exact Or.inl (fun j hj hjy => hq ⟨j, hj, hjy⟩)
  refine { bv := hv0, stack := ?_, low := h.low, mon := ?_, repair := ?_ }
  · intro x hx
    have hxv : x ≠ v := fun hxv => hv (hxv ▸ hx)
    apply h.same x hxv
    intro j hj hjx
    by_cases hj0 : j = 0
    · subst hj0; simp only [h0] at hjx; exact hxv hjx.symm
    · exact (h.off j hj (by omega)).1 (hjx ▸ hx)
  · intro y
    by_cases hyv : y = v
    · subst hyv; right; rw [hv0]; have := h.walk 0 h.pos; simp only [h0] at this; exact this
    rcases hmem y hyv with hq | ⟨j, hj, hjy⟩
    · left; rw [h.same y hyv hq]; exact Nat.le_refl _
    · right; have hw := h.walk j hj; have hval := h.val j hj; simp only [hjy] at hw hval; rw [hval]; exact hw
  · intro hEC x y hxy hx hy hxv
    by_cases hyv : y = v
    · subst hyv
      have := hall 0 h.pos
      simp only [h0] at this
      have := this x ((hG.rev x y).mp hxy) hx hxv
      rw [hv0]; exact this
    rcases hmem y hyv with hq | ⟨j, hj, hjy⟩
    · have h1 := hEC x y hxy (by simp [hx, hxv]) (by simp [hy, hyv])
      have h2 := h.low x hxv
      rw [h.same y hyv hq]
      omega
    · have hp := hall j hj
      have hval := h.val j hj
      simp only [hjy] at hp hval
      rw [hval]
      exact hp x ((hG.rev x y).mp hxy) hx hxv

end cascade

/-- Cascade spec (ghost equations first, so that `mvcgen` instantiates b0 and O0 by unification): `fruitful` leaves the stack and the outputs unchanged and establishes `CascPost` -/
theorem fruitful_spec (G : Graph n) (hG : G.WF) (t v : Fin n) (S0 : Array (Fin n)) (sd : Nat) (b0 : Vector Nat n) (O0 : List (List (Fin n))) :
    ⦃fun st => ⌜st.b = b0 ∧ outputs st.trace.toList = O0 ∧ st.S = S0.push v ∧ v ∉ S0.toList ∧ G.WalkLE S0.toList t v sd⌝⦄
    fruitful G v sd
    ⦃⇓ _ st => ⌜st.S = S0.push v ∧ outputs st.trace.toList = O0 ∧ CascPost G t v sd S0 b0 st.b⌝⦄ := by
  mvcgen [fruitful, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack] invariants
  | inv1 => ⇓⟨xs, queue⟩ st => ⌜st.S = S0.push v ∧ outputs st.trace.toList = O0 ∧ v ∉ S0.toList ∧ CascOuter G t v sd S0 b0 xs.prefix.length queue st.b⌝
  | inv2 _ cur _ _ qo hcur _ _ _ _ => ⇓⟨xs, queue⟩ st => ⌜st.S = S0.push v ∧ outputs st.trace.toList = O0 ∧ v ∉ S0.toList ∧ CascInner G t v sd S0 b0 cur (qo[cur]'hcur) xs.prefix queue st.b⌝
  case vc1.step.isTrue =>
    -- relaxation: casc_relax
    obtain ⟨hS, hout, hv, hinv⟩ := ‹_ = S0.push v ∧ _ ∧ _ ∧ CascInner G t v sd S0 b0 _ _ _ _ _›
    have hp := mem_of_eq_append_cons ‹G.pred _ = _ ++ _ :: _›
    have hcond := ‹¬_ ∈ _ ∧ _ > _›
    simp +zetaDelta only at hcond ⊢
    rw [hS] at hcond
    simp only [Array.mem_push, not_or] at hcond
    refine ⟨hS, by simp [hout], hv, ?_⟩
    exact casc_relax hG hv hinv hp (by simpa using hcond.1.1) hcond.1.2 hcond.2
  case vc2.step.isFalse =>
    -- no relaxation: casc_skip
    obtain ⟨hS, hout, hv, hinv⟩ := ‹_ = S0.push v ∧ _ ∧ _ ∧ CascInner G t v sd S0 b0 _ _ _ _ _›
    have hcond := ‹¬(¬_ ∈ _ ∧ _ > _)›
    simp +zetaDelta only at hcond ⊢
    rw [hS] at hcond
    simp only [Array.mem_push, not_or] at hcond
    refine ⟨hS, hout, hv, casc_skip hinv ?_⟩
    intro hpS hpv
    exact Nat.le_of_not_lt fun hlt => hcond ⟨⟨by simpa using hpS, hpv⟩, hlt⟩
  case vc3.step.isTrue.pre =>
    -- dequeue: casc_dequeue
    obtain ⟨hS, hout, hv, hinv⟩ := ‹_ = S0.push v ∧ _ ∧ _ ∧ CascOuter G t v sd S0 b0 _ _ _›
    have hcur := range_eq_append_cons ‹List.range n = _ ++ _ :: _›
    have hlt := ‹_ < Array.size _›
    simp +zetaDelta only
    refine ⟨hS, by simp [hout], hv, ?_⟩
    subst hcur
    exact casc_dequeue hinv hlt
  case vc4.step.isTrue.post.success =>
    -- next pair: casc_next
    obtain ⟨hS, hout, hv, hinv⟩ := ‹_ = S0.push v ∧ _ ∧ _ ∧ CascInner G t v sd S0 b0 _ _ _ _ _›
    have hcur := range_eq_append_cons ‹List.range n = _ ++ _ :: _›
    refine ⟨hS, hout, hv, ?_⟩
    simp only [List.length_append, List.length_singleton]
    rw [← hcur]
    exact casc_next hinv
  case vc5.step.isFalse =>
    -- break: casc_break
    obtain ⟨hS, hout, hv, hinv⟩ := ‹_ = S0.push v ∧ _ ∧ _ ∧ CascOuter G t v sd S0 b0 _ _ _›
    have hcur := range_eq_append_cons ‹List.range n = _ ++ _ :: _›
    have hge := ‹¬_ < Array.size _›
    refine ⟨hS, hout, hv, ?_⟩
    simp only [List.length_range]
    subst hcur
    exact casc_break hinv hge
  case vc6.pre =>
    -- initial pair (v, sd): casc_init
    obtain ⟨hb, hout, hS, hv, hw⟩ := ‹_ = b0 ∧ _ ∧ _ = S0.push v ∧ _ ∧ _›
    simp +zetaDelta only
    refine ⟨hS, by simp [hout], hv, ?_⟩
    simp only [List.length_nil]
    rw [hb]
    exact casc_init hw
  case vc7.post.success =>
    -- all pairs processed: casc_final
    obtain ⟨hS, hout, hv, hinv⟩ := ‹_ = S0.push v ∧ _ ∧ _ ∧ CascOuter G t v sd S0 b0 _ _ _›
    simp only [List.length_range] at hinv
    exact ⟨hS, hout, casc_final hG hv hinv⟩
