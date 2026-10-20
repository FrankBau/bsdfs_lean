/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.RunTrace
import Bsdfs.Complete

/-!
  Stage 3c, part 2: the trace facts of the cascade `fruitful G v sd`, as a Hoare spec extending `fruitful_spec`.  The cascade
  emits only cascade events (start, origin write, dequeues, drops) and keeps the stack; it drops only nodes that are not yet
  queued, so a dropped node is not written again, and it dequeues every queued node once.
-/

open Std.Do Trace

set_option mvcgen.warning false

variable {n : Nat}

/-! ## One more event -/

section snoc
variable {T : List (Ev n)} {e : Ev n}

theorem Trace.getElem?_snoc_gt {q : Nat} (hq : T.length < q) : (T ++ [e])[q]? = none := List.getElem?_eq_none (by simp; omega)

theorem Trace.stk_snoc_other (h1 : ∀ σ v h, e ≠ .enter σ v h) (h2 : ∀ σ v h sd f, e ≠ .exit σ v h sd f) : stk (T ++ [e]) (T.length + 1) = stk T T.length := by
  rw [Trace.stk_succ_other (fun σ v h he => h1 σ v h (by simpa using he)) (fun σ v h sd f he => h2 σ v h sd f (by simpa using he)), Trace.stk_append (Nat.le_refl _)]

theorem Trace.stk_snoc_enter {σ : Nat} {v : Fin n} {h : Nat} : stk (T ++ [.enter σ v h]) (T.length + 1) = stk T T.length ++ [v] := by
  have hp : (T ++ [Ev.enter σ v h])[T.length]? = some (.enter σ v h) := by simp
  rw [Trace.stk_succ_enter hp, Trace.stk_append (Nat.le_refl _)]

theorem Trace.stk_snoc_exit {σ : Nat} {v : Fin n} {h sd : Nat} {f : Bool} : stk (T ++ [.exit σ v h sd f]) (T.length + 1) = (stk T T.length).dropLast := by
  have hp : (T ++ [Ev.exit σ v h sd f])[T.length]? = some (.exit σ v h sd f) := by simp
  rw [Trace.stk_succ_exit hp, Trace.stk_append (Nat.le_refl _)]

theorem Trace.bar_snoc_write {σ : Nat} {x : Fin n} {o nw : Nat} {kd : Kind} (z : Fin n) : bar (T ++ [.write σ x o nw kd]) (T.length + 1) z = if x = z then nw else bar T T.length z := by
  have hp : (T ++ [Ev.write σ x o nw kd])[T.length]? = some (.write σ x o nw kd) := by simp
  rw [Trace.bar_succ_write hp, Trace.bar_append (Nat.le_refl _)]

theorem Trace.bar_snoc_other (h : ∀ σ x o nw kd, e ≠ .write σ x o nw kd) (z : Fin n) : bar (T ++ [e]) (T.length + 1) z = bar T T.length z := by
  rw [Trace.bar_succ_other (fun σ x o nw kd he => h σ x o nw kd (by simpa using he)), Trace.bar_append (Nat.le_refl _)]

theorem Trace.dropAt_none {q : Nat} (h : T[q]? = none) (z : Fin n) : dropAt T z q = false := by simp [dropAt, h]

theorem Trace.deqAt_none {q : Nat} (h : T[q]? = none) (z : Fin n) : deqAt T z q = false := by simp [deqAt, h]

theorem Trace.dropAt_ne {q : Nat} (h : T[q]? = some e) (he : ∀ σ x o nw, e ≠ .write σ x o nw .drop) (z : Fin n) : dropAt T z q = false := by
  unfold dropAt; rw [h]
  cases e <;> try rfl
  rename_i σ x o nw kd
  cases kd <;> try rfl
  exact absurd rfl (he σ x o nw)

theorem Trace.deqAt_ne {q : Nat} (h : T[q]? = some e) (he : ∀ σ v d, e ≠ .dequeue σ v d) (z : Fin n) : deqAt T z q = false := by
  unfold deqAt; rw [h]
  cases e <;> try rfl
  rename_i σ v d
  exact absurd rfl (he σ v d)

end snoc

/-! ## The trace invariant of the cascade -/

/-- what the cascade's trace facts need from the calling `search` (T1 is the trace before the cascade) -/
structure CascCtx (s t : Fin n) (k : Nat) (v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (T1 : List (Ev n)) : Prop where
  stk : stk T1 T1.length = (S0.push v).toList
  bar : ∀ z, bar T1 T1.length z = b0[z]
  target : b0[t] = 0
  sd_pos : 1 ≤ sd
  sd_le : sd + S0.size ≤ k
  bv : b0[v] ≤ sd
  depth : 1 ≤ S0.size
  vt : v ≠ t

/-- the trace part of the cascade invariant: T1 is the trace before the cascade, T the current one, nd the number of dequeued pairs -/
structure TrCasc (G : Graph n) (s t : Fin n) (k : Nat) (v : Fin n) (sd : Nat) (S0 : Array (Fin n)) (T1 : List (Ev n)) (nd : Nat) (queue : Array (Fin n × Nat)) (b : Vector Nat n) (T : List (Ev n)) : Prop where
  ext : ∃ E, T = T1 ++ E
  len : T1.length + 2 ≤ T.length
  start : ∃ σ, T[T1.length]? = some (.cascade σ v sd)
  fruit : fruitAt T v (T1.length + 1) = true
  stk : ∀ q, T1.length ≤ q → q ≤ T.length → stk T q = (S0.push v).toList
  bar : ∀ z, bar T T.length z = b[z]
  casc : ∀ q, T1.length ≤ q → q < T.length → isCasc T q = true
  ev : ∀ q, T1.length ≤ q → q < T.length → EvOK G s t k T q
  drop_last : ∀ θ y, T1.length ≤ θ → dropAt T y θ = true → ∀ r σ o nw kd, θ < r → T[r]? ≠ some (.write σ y o nw kd)
  deq_once : ∀ q₁ q₂ z, T1.length ≤ q₁ → q₁ < q₂ → deqAt T z q₁ = true → deqAt T z q₂ = false
  deq_drop : ∀ q z, T1.length ≤ q → deqAt T z q = true → z ≠ v → ∃ q', T1.length ≤ q' ∧ q' < q ∧ dropAt T z q' = true
  in_queue : ∀ θ y, T1.length ≤ θ → dropAt T y θ = true → ∃ j, ∃ hj : j < queue.size, 0 < j ∧ queue[j].1 = y
  dropped : ∀ j (hj : j < queue.size), 0 < j → ∃ θ, T1.length ≤ θ ∧ dropAt T queue[j].1 θ = true
  deqs : ∀ q z, T1.length ≤ q → deqAt T z q = true → ∃ j, ∃ hj : j < queue.size, j < nd ∧ queue[j].1 = z

section steps
variable {G : Graph n} {s t : Fin n} {k : Nat} {v : Fin n} {sd : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n} {T1 : List (Ev n)}

/-- the start of the cascade: the cascade event and the origin write b[v] := sd -/
theorem tc_init (hctx : CascCtx s t k v sd S0 b0 T1) {σ σ' : Nat} :
    TrCasc G s t k v sd S0 T1 0 #[(v, sd)] (b0.set v.1 sd v.2) (T1 ++ [.cascade σ v sd] ++ [.write σ' v b0[v] sd .fruitful]) := by
  have hl1 : (T1 ++ [Ev.cascade σ v sd]).length = T1.length + 1 := by simp
  have hl2 : (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful]).length = T1.length + 2 := by simp
  have g0 : (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful])[T1.length]? = some (.cascade σ v sd) := by simp
  have g1 : (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful])[T1.length + 1]? = some (.write σ' v b0[v] sd .fruitful) := by simp
  have s0 : stk (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful]) T1.length = (S0.push v).toList := by
    rw [Trace.stk_append (by simp), Trace.stk_append (Nat.le_refl _)]; exact hctx.stk
  have s1 : stk (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful]) (T1.length + 1) = (S0.push v).toList := by
    rw [Trace.stk_append (by simp), Trace.stk_snoc_other (by intros; simp) (by intros; simp)]; exact hctx.stk
  have s2 : stk (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful]) (T1.length + 2) = (S0.push v).toList := by
    have := Trace.stk_snoc_other (T := T1 ++ [Ev.cascade σ v sd]) (e := .write σ' v b0[v] sd .fruitful) (by intros; simp) (by intros; simp)
    rw [hl1] at this; rw [this, Trace.stk_snoc_other (by intros; simp) (by intros; simp)]; exact hctx.stk
  have b1 : ∀ z, bar (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful]) (T1.length + 1) z = b0[z] := by
    intro z; rw [Trace.bar_append (by simp), Trace.bar_snoc_other (by intros; simp)]; exact hctx.bar z
  have hpos : ∀ q, T1.length ≤ q → q < T1.length + 2 → q = T1.length ∨ q = T1.length + 1 := by intro q h1 h2; omega
  have hnone : ∀ q, T1.length + 2 ≤ q → (T1 ++ [Ev.cascade σ v sd] ++ [Ev.write σ' v b0[v] sd .fruitful])[q]? = none := by
    intro q hq; exact List.getElem?_eq_none (by simp; omega)
  have hS : (S0.push v).toList.length = S0.size + 1 := by simp
  refine { ext := ⟨_, List.append_assoc _ _ _⟩, len := by simp, start := ⟨σ, g0⟩, fruit := by simp [fruitAt], stk := ?_, bar := ?_, casc := ?_, ev := ?_, drop_last := ?_, deq_once := ?_, deq_drop := ?_, in_queue := ?_, dropped := ?_, deqs := ?_ }
  · intro q h1 h2
    rw [hl2] at h2
    rcases Nat.lt_or_ge q (T1.length + 2) with h | h
    · rcases hpos q h1 h with rfl | rfl
      · exact s0
      · exact s1
    · rw [show q = T1.length + 2 by omega]; exact s2
  · intro z
    have := Trace.bar_snoc_write (T := T1 ++ [Ev.cascade σ v sd]) (σ := σ') (x := v) (o := b0[v]) (nw := sd) (kd := .fruitful) z
    have b1' : bar (T1 ++ [Ev.cascade σ v sd]) (T1.length + 1) z = b0[z] := by rw [Trace.bar_snoc_other (by intros; simp)]; exact hctx.bar z
    rw [hl1] at this; rw [hl2, this, b1']
    by_cases hvz : v = z
    · subst hvz; simp
    · simp [hvz, Fin.val_inj]
  · intro q h1 h2
    rw [hl2] at h2
    rcases hpos q h1 h2 with rfl | rfl
    · simp [isCasc]
    · simp [isCasc]
  · intro q h1 h2
    rw [hl2] at h2
    rcases hpos q h1 h2 with rfl | rfl
    · simp [EvOK]
    · simp only [EvOK, g1]
      rw [s1, b1]
      refine ⟨rfl, hctx.vt, by simp, ?_, hctx.bv, hctx.sd_pos, ?_⟩
      · rw [hS]; have := hctx.sd_le; omega
      · rw [hS]; have := hctx.depth; omega
  · intro θ y h1 hd
    rcases Nat.lt_or_ge θ (T1.length + 2) with h | h
    · rcases hpos θ h1 h with rfl | rfl
      · rw [Trace.dropAt_ne g0 (by intros; simp)] at hd; cases hd
      · rw [Trace.dropAt_ne g1 (by intros; simp)] at hd; cases hd
    · rw [Trace.dropAt_none (hnone θ h)] at hd; cases hd
  · intro q₁ q₂ z h1 _ hd
    rcases Nat.lt_or_ge q₁ (T1.length + 2) with h | h
    · rcases hpos q₁ h1 h with rfl | rfl
      · rw [Trace.deqAt_ne g0 (by intros; simp)] at hd; cases hd
      · rw [Trace.deqAt_ne g1 (by intros; simp)] at hd; cases hd
    · rw [Trace.deqAt_none (hnone q₁ h)] at hd; cases hd
  · intro q z h1 hd
    rcases Nat.lt_or_ge q (T1.length + 2) with h | h
    · rcases hpos q h1 h with rfl | rfl
      · rw [Trace.deqAt_ne g0 (by intros; simp)] at hd; cases hd
      · rw [Trace.deqAt_ne g1 (by intros; simp)] at hd; cases hd
    · rw [Trace.deqAt_none (hnone q h)] at hd; cases hd
  · intro θ y h1 hd
    rcases Nat.lt_or_ge θ (T1.length + 2) with h | h
    · rcases hpos θ h1 h with rfl | rfl
      · rw [Trace.dropAt_ne g0 (by intros; simp)] at hd; cases hd
      · rw [Trace.dropAt_ne g1 (by intros; simp)] at hd; cases hd
    · rw [Trace.dropAt_none (hnone θ h)] at hd; cases hd
  · intro j hj h0; simp at hj; omega
  · intro q z h1 hd
    rcases Nat.lt_or_ge q (T1.length + 2) with h | h
    · rcases hpos q h1 h with rfl | rfl
      · rw [Trace.deqAt_ne g0 (by intros; simp)] at hd; cases hd
      · rw [Trace.deqAt_ne g1 (by intros; simp)] at hd; cases hd
    · rw [Trace.deqAt_none (hnone q h)] at hd; cases hd

/-- a dequeue of the pair at read index i -/
theorem tc_dequeue {i : Nat} {queue : Array (Fin n × Nat)} {b : Vector Nat n} {T : List (Ev n)} {σ : Nat}
    (hc : CascOuter G t v sd S0 b0 i queue b) (htr : TrCasc G s t k v sd S0 T1 i queue b T) (hi : i < queue.size) :
    TrCasc G s t k v sd S0 T1 (i + 1) queue b (T ++ [.dequeue σ queue[i].1 queue[i].2]) := by
  have hT := htr.len
  have hlen : (T ++ [Ev.dequeue σ queue[i].1 queue[i].2]).length = T.length + 1 := by simp
  have hlast : (T ++ [Ev.dequeue σ queue[i].1 queue[i].2])[T.length]? = some (.dequeue σ queue[i].1 queue[i].2) := by simp
  have hstk := Trace.stk_snoc_other (T := T) (e := .dequeue σ queue[i].1 queue[i].2) (by intros; simp) (by intros; simp)
  have hbar := Trace.bar_snoc_other (T := T) (e := .dequeue σ queue[i].1 queue[i].2) (by intros; simp)
  have hgt : ∀ q, T.length < q → (T ++ [Ev.dequeue σ queue[i].1 queue[i].2])[q]? = none := fun q hq => Trace.getElem?_snoc_gt hq
  -- an old dequeue at q: of a pair with index below i
  have hold : ∀ q z, T1.length ≤ q → deqAt (T ++ [Ev.dequeue σ queue[i].1 queue[i].2]) z q = true → q < T.length ∨ (q = T.length ∧ z = queue[i].1) := by
    intro q z h1 hd
    rcases Nat.lt_trichotomy q T.length with h | h | h
    · exact Or.inl h
    · subst h; simp [deqAt] at hd; exact Or.inr ⟨rfl, hd.symm⟩
    · rw [Trace.deqAt_none (hgt q h)] at hd; cases hd
  refine { ext := ?_, len := by rw [hlen]; omega, start := ?_, fruit := ?_, stk := ?_, bar := ?_, casc := ?_, ev := ?_, drop_last := ?_, deq_once := ?_, deq_drop := ?_, in_queue := ?_, dropped := ?_, deqs := ?_ }
  · obtain ⟨E, hE⟩ := htr.ext; exact ⟨E ++ [_], by rw [hE, List.append_assoc]⟩
  · obtain ⟨σ', h'⟩ := htr.start; exact ⟨σ', by rw [List.getElem?_append_left (by omega)]; exact h'⟩
  · rw [Trace.fruitAt_append (by omega)]; exact htr.fruit
  · intro q h1 h2
    rw [hlen] at h2
    rcases Nat.lt_or_ge q (T.length + 1) with h | h
    · rw [Trace.stk_append (by omega)]; exact htr.stk q h1 (by omega)
    · rw [show q = T.length + 1 by omega, hstk]; exact htr.stk T.length (by omega) (Nat.le_refl _)
  · intro z; rw [hlen, hbar]; exact htr.bar z
  · intro q h1 h2
    rw [hlen] at h2
    rcases Nat.lt_or_ge q T.length with h | h
    · rw [Trace.isCasc_append h]; exact htr.casc q h1 h
    · rw [show q = T.length by omega]; simp [isCasc]
  · intro q h1 h2
    rw [hlen] at h2
    rcases Nat.lt_or_ge q T.length with h | h
    · exact (htr.ev q h1 h).append h
    · rw [show q = T.length by omega]; simp [EvOK]
  · intro θ y h1 hd r σ' o nw kd h2
    rcases Nat.lt_or_ge θ T.length with hθ | hθ
    · rw [Trace.dropAt_append hθ] at hd
      rcases Nat.lt_trichotomy r T.length with h | h | h
      · rw [List.getElem?_append_left h]; exact htr.drop_last θ y h1 hd r σ' o nw kd h2
      · subst h; rw [hlast]; simp
      · rw [hgt r h]; simp
    · rcases Nat.eq_or_lt_of_le hθ with h | h
      · subst h; rw [Trace.dropAt_ne hlast (by intros; simp)] at hd; cases hd
      · rw [Trace.dropAt_none (hgt θ h)] at hd; cases hd
  · intro q₁ q₂ z h1 h12 hd₁
    rcases hold q₁ z h1 hd₁ with hq₁ | ⟨hq₁, _⟩
    · rw [Trace.deqAt_append hq₁] at hd₁
      cases hd₂ : deqAt (T ++ [Ev.dequeue σ queue[i].1 queue[i].2]) z q₂
      · rfl
      · rcases hold q₂ z (by omega) hd₂ with hq₂ | ⟨hq₂, hz⟩
        · rw [Trace.deqAt_append hq₂] at hd₂; rw [htr.deq_once q₁ q₂ z h1 h12 hd₁] at hd₂; cases hd₂
        · -- the new dequeue repeats an old one: both are queue[i].1, but old dequeues have indices below i
          obtain ⟨j, hj, hji, hjz⟩ := htr.deqs q₁ z h1 hd₁
          have hj' : j < (queue.toList.map Prod.fst).length := by simp; omega
          have hi' : i < (queue.toList.map Prod.fst).length := by simp; omega
          have := hc.nodup.eq_of_getElem_eq hj' hi' (by simp [hjz, hz])
          omega
    · simp only [hq₁] at h12
      cases hd₂ : deqAt (T ++ [Ev.dequeue σ queue[i].1 queue[i].2]) z q₂
      · rfl
      · rw [Trace.deqAt_none (hgt q₂ h12)] at hd₂; cases hd₂
  · intro q z h1 hd hzv
    rcases hold q z h1 hd with hq | ⟨hq, hz⟩
    · rw [Trace.deqAt_append hq] at hd
      obtain ⟨q', h1', h2', hq'⟩ := htr.deq_drop q z h1 hd hzv
      exact ⟨q', h1', h2', by rw [Trace.dropAt_append (by omega)]; exact hq'⟩
    · -- the pair at index i > 0 was queued by a drop
      have hi0 : 0 < i := by
        refine Nat.pos_of_ne_zero fun h0 => hzv ?_
        subst h0; rw [hz]; have := hc.head; simp only [this]
      obtain ⟨θ, h1', hθ⟩ := htr.dropped i hi hi0
      have hθT : θ < T.length := by
        refine Nat.lt_of_not_le fun hle => ?_
        rw [Trace.dropAt_none (List.getElem?_eq_none hle)] at hθ; cases hθ
      exact ⟨θ, h1', by omega, by rw [Trace.dropAt_append hθT, hz]; exact hθ⟩
  · intro θ y h1 hd
    rcases Nat.lt_trichotomy θ T.length with h | h | h
    · rw [Trace.dropAt_append h] at hd; exact htr.in_queue θ y h1 hd
    · subst h; rw [Trace.dropAt_ne hlast (by intros; simp)] at hd; cases hd
    · rw [Trace.dropAt_none (hgt θ h)] at hd; cases hd
  · intro j hj h0
    obtain ⟨θ, h1', hθ⟩ := htr.dropped j hj h0
    have hθT : θ < T.length := by
      refine Nat.lt_of_not_le fun hle => ?_
      rw [Trace.dropAt_none (List.getElem?_eq_none hle)] at hθ; cases hθ
    exact ⟨θ, h1', by rw [Trace.dropAt_append hθT]; exact hθ⟩
  · intro q z h1 hd
    rcases hold q z h1 hd with hq | ⟨hq, hz⟩
    · rw [Trace.deqAt_append hq] at hd
      obtain ⟨j, hj, hji, hjz⟩ := htr.deqs q z h1 hd
      exact ⟨j, hj, by omega, hjz⟩
    · exact ⟨i, hi, by omega, hz.symm⟩

/-- a drop of the predecessor p of the pair e at read index i -/
theorem tc_relax (hctx : CascCtx s t k v sd S0 b0 T1) {i : Nat} {e : Fin n × Nat} {ps : List (Fin n)} {queue : Array (Fin n × Nat)} {b : Vector Nat n} {T : List (Ev n)} {p : Fin n} {σ : Nat}
    (hc : CascInner G t v sd S0 b0 i e ps queue b) (hc' : CascInner G t v sd S0 b0 i e (ps ++ [p]) (queue.push (p, e.2 + 1)) (b.set p.1 (e.2 + 1) p.2)) (htr : TrCasc G s t k v sd S0 T1 (i + 1) queue b T)
    (hpS : p ∉ S0.toList) (hpv : p ≠ v) (hlt : e.2 + 1 < b[p]) :
    TrCasc G s t k v sd S0 T1 (i + 1) (queue.push (p, e.2 + 1)) (b.set p.1 (e.2 + 1) p.2) (T ++ [.write σ p b[p] (e.2 + 1) .drop]) := by
  have hT := htr.len
  have hlen : (T ++ [Ev.write σ p b[p] (e.2 + 1) .drop]).length = T.length + 1 := by simp
  have hlast : (T ++ [Ev.write σ p b[p] (e.2 + 1) .drop])[T.length]? = some (.write σ p b[p] (e.2 + 1) .drop) := by simp
  have hstk := Trace.stk_snoc_other (T := T) (e := .write σ p b[p] (e.2 + 1) .drop) (by intros; simp) (by intros; simp)
  have hgt : ∀ q, T.length < q → (T ++ [Ev.write σ p b[p] (e.2 + 1) .drop])[q]? = none := fun q hq => Trace.getElem?_snoc_gt hq
  have hnot := hc.not_mem hc.bound hlt
  have hS : (S0.push v).toList.length = S0.size + 1 := by simp
  have hstkT := htr.stk T.length (by omega) (Nat.le_refl _)
  -- d ≥ sd ≥ 1 along the queue
  obtain ⟨hi, hie⟩ := hc.entry
  have hsd : sd ≤ e.2 := by have := hc.sorted 0 i hc.pos hi (Nat.zero_le _); rw [hc.head, hie] at this; exact this
  have hpt : p ≠ t := by
    intro hpt; subst hpt
    have := hc.low p (fun h => hctx.vt h.symm)
    have := hctx.target
    simp only [Fin.getElem_fin] at *
    omega
  have hwalk : G.WalkLE S0.toList t p (e.2 + 1) := by
    have := hc'.walk queue.size (by simp)
    simpa using this
  -- an old drop: of a queued node, so not of p
  have hold : ∀ θ y, T1.length ≤ θ → dropAt (T ++ [Ev.write σ p b[p] (e.2 + 1) .drop]) y θ = true → θ < T.length ∨ (θ = T.length ∧ y = p) := by
    intro θ y h1 hd
    rcases Nat.lt_trichotomy θ T.length with h | h | h
    · exact Or.inl h
    · subst h; simp [dropAt] at hd; exact Or.inr ⟨rfl, hd.symm⟩
    · rw [Trace.dropAt_none (hgt θ h)] at hd; cases hd
  have hdeq : ∀ q z, deqAt (T ++ [Ev.write σ p b[p] (e.2 + 1) .drop]) z q = true → q < T.length := by
    intro q z hd
    rcases Nat.lt_trichotomy q T.length with h | h | h
    · exact h
    · subst h; rw [Trace.deqAt_ne hlast (by intros; simp)] at hd; cases hd
    · rw [Trace.deqAt_none (hgt q h)] at hd; cases hd
  refine { ext := ?_, len := by rw [hlen]; omega, start := ?_, fruit := ?_, stk := ?_, bar := ?_, casc := ?_, ev := ?_, drop_last := ?_, deq_once := ?_, deq_drop := ?_, in_queue := ?_, dropped := ?_, deqs := ?_ }
  · obtain ⟨E, hE⟩ := htr.ext; exact ⟨E ++ [_], by rw [hE, List.append_assoc]⟩
  · obtain ⟨σ', h'⟩ := htr.start; exact ⟨σ', by rw [List.getElem?_append_left (by omega)]; exact h'⟩
  · rw [Trace.fruitAt_append (by omega)]; exact htr.fruit
  · intro q h1 h2
    rw [hlen] at h2
    rcases Nat.lt_or_ge q (T.length + 1) with h | h
    · rw [Trace.stk_append (by omega)]; exact htr.stk q h1 (by omega)
    · rw [show q = T.length + 1 by omega, hstk]; exact hstkT
  · intro z
    rw [hlen, Trace.bar_snoc_write, htr.bar z]
    by_cases hpz : p = z
    · subst hpz; simp
    · simp [hpz, Fin.val_inj]
  · intro q h1 h2
    rw [hlen] at h2
    rcases Nat.lt_or_ge q T.length with h | h
    · rw [Trace.isCasc_append h]; exact htr.casc q h1 h
    · rw [show q = T.length by omega]; simp [isCasc]
  · intro q h1 h2
    rw [hlen] at h2
    rcases Nat.lt_or_ge q T.length with h | h
    · exact (htr.ev q h1 h).append h
    · rw [show q = T.length by omega]
      simp only [EvOK, hlast]
      rw [Trace.stk_append (Nat.le_refl T.length), Trace.bar_append (Nat.le_refl T.length), hstkT, htr.bar]
      refine ⟨rfl, hpt, ?_, hlt, by have := hctx.sd_pos; omega, by rw [hS]; have := hctx.depth; omega, ?_⟩
      · simp [hpS, hpv]
      · simpa using hwalk
  · intro θ y h1 hd r σ' o nw kd h2
    rcases hold θ y h1 hd with hθ | ⟨hθ, hy⟩
    · rw [Trace.dropAt_append hθ] at hd
      rcases Nat.lt_trichotomy r T.length with h | h | h
      · rw [List.getElem?_append_left h]; exact htr.drop_last θ y h1 hd r σ' o nw kd h2
      · -- y is queued, p is not
        subst h; rw [hlast]
        obtain ⟨j, hj, -, hjy⟩ := htr.in_queue θ y h1 hd
        intro heq
        simp only [Option.some.injEq, Ev.write.injEq] at heq
        exact hnot j hj (hjy.trans heq.2.1.symm)
      · rw [hgt r h]; simp
    · subst hθ; rw [hgt r h2]; simp
  · intro q₁ q₂ z h1 h12 hd₁
    have hq₁ := hdeq q₁ z hd₁
    rw [Trace.deqAt_append hq₁] at hd₁
    cases hd₂ : deqAt (T ++ [Ev.write σ p b[p] (e.2 + 1) .drop]) z q₂
    · rfl
    · have hq₂ := hdeq q₂ z hd₂
      rw [Trace.deqAt_append hq₂, htr.deq_once q₁ q₂ z h1 h12 hd₁] at hd₂; cases hd₂
  · intro q z h1 hd hzv
    have hq := hdeq q z hd
    rw [Trace.deqAt_append hq] at hd
    obtain ⟨q', h1', h2', hq'⟩ := htr.deq_drop q z h1 hd hzv
    exact ⟨q', h1', h2', by rw [Trace.dropAt_append (by omega)]; exact hq'⟩
  · intro θ y h1 hd
    rcases hold θ y h1 hd with hθ | ⟨hθ, hy⟩
    · rw [Trace.dropAt_append hθ] at hd
      obtain ⟨j, hj, hj0, hjy⟩ := htr.in_queue θ y h1 hd
      exact ⟨j, by simp; omega, hj0, by rw [Array.getElem_push_lt hj]; exact hjy⟩
    · exact ⟨queue.size, by simp, hc.pos, by simp [hy]⟩
  · intro j hj h0
    rw [Array.getElem_push]
    split
    · next hj' =>
      obtain ⟨θ, h1', hθ⟩ := htr.dropped j hj' h0
      have hθT : θ < T.length := by
        refine Nat.lt_of_not_le fun hle => ?_
        rw [Trace.dropAt_none (List.getElem?_eq_none hle)] at hθ; cases hθ
      exact ⟨θ, h1', by rw [Trace.dropAt_append hθT]; exact hθ⟩
    · exact ⟨T.length, by omega, by simp [dropAt]⟩
  · intro q z h1 hd
    have hq := hdeq q z hd
    rw [Trace.deqAt_append hq] at hd
    obtain ⟨j, hj, hji, hjz⟩ := htr.deqs q z h1 hd
    exact ⟨j, by simp; omega, hji, by rw [Array.getElem_push_lt hj]; exact hjz⟩

theorem TrCasc.mono_nd {nd nd' : Nat} {queue : Array (Fin n × Nat)} {b : Vector Nat n} {T : List (Ev n)} (h : TrCasc G s t k v sd S0 T1 nd queue b T) (hle : nd ≤ nd') : TrCasc G s t k v sd S0 T1 nd' queue b T :=
  { h with deqs := fun q z h1 hd => by obtain ⟨j, hj, hjn, hjz⟩ := h.deqs q z h1 hd; exact ⟨j, hj, by omega, hjz⟩ }

end steps

/-- Cascade spec with the trace (ghost equations first): `fruitful_spec` plus the trace facts of the cascade -/
theorem fruitful_spec_tr (G : Graph n) (hG : G.WF) (s t : Fin n) (k : Nat) (v : Fin n) (S0 : Array (Fin n)) (sd : Nat) (b0 : Vector Nat n) (T1 : List (Ev n)) :
    ⦃fun st => ⌜st.b = b0 ∧ st.trace.toList = T1 ∧ st.S = S0.push v ∧ v ∉ S0.toList ∧ G.WalkLE S0.toList t v sd ∧ CascCtx s t k v sd S0 b0 T1⌝⦄
    fruitful G v sd
    ⦃⇓ _ st => ⌜st.S = S0.push v ∧ CascPost G t v sd S0 b0 st.b ∧ ∃ nd queue, TrCasc G s t k v sd S0 T1 nd queue st.b st.trace.toList⌝⦄ := by
  mvcgen [fruitful, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack] invariants
  | inv1 => ⇓⟨xs, queue⟩ st => ⌜st.S = S0.push v ∧ v ∉ S0.toList ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascOuter G t v sd S0 b0 xs.prefix.length queue st.b ∧ TrCasc G s t k v sd S0 T1 xs.prefix.length queue st.b st.trace.toList⌝
  | inv2 _ cur _ _ qo hcur _ _ _ _ => ⇓⟨xs, queue⟩ st => ⌜st.S = S0.push v ∧ v ∉ S0.toList ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascInner G t v sd S0 b0 cur (qo[cur]'hcur) xs.prefix queue st.b ∧ TrCasc G s t k v sd S0 T1 (cur + 1) queue st.b st.trace.toList⌝
  case vc1.step.isTrue =>
    -- relaxation: casc_relax, tc_relax
    obtain ⟨hS, hv, hctx, hinv, htr⟩ := ‹_ = S0.push v ∧ _ ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascInner G t v sd S0 b0 _ _ _ _ _ ∧ TrCasc G s t k v sd S0 T1 _ _ _ _›
    have hp := mem_of_eq_append_cons ‹G.pred _ = _ ++ _ :: _›
    have hcond := ‹¬_ ∈ _ ∧ _ > _›
    simp +zetaDelta only at hcond ⊢
    rw [hS] at hcond
    simp only [Array.mem_push, not_or] at hcond
    have hc' := casc_relax hG hv hinv hp (by simpa using hcond.1.1) hcond.1.2 hcond.2
    refine ⟨hS, hv, hctx, hc', ?_⟩
    rw [Array.toList_push]
    exact tc_relax hctx hinv hc' htr (by simpa using hcond.1.1) hcond.1.2 hcond.2
  case vc2.step.isFalse =>
    -- no relaxation: casc_skip
    obtain ⟨hS, hv, hctx, hinv, htr⟩ := ‹_ = S0.push v ∧ _ ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascInner G t v sd S0 b0 _ _ _ _ _ ∧ TrCasc G s t k v sd S0 T1 _ _ _ _›
    have hcond := ‹¬(¬_ ∈ _ ∧ _ > _)›
    simp +zetaDelta only at hcond ⊢
    rw [hS] at hcond
    simp only [Array.mem_push, not_or] at hcond
    refine ⟨hS, hv, hctx, casc_skip hinv ?_, htr⟩
    intro hpS hpv
    exact Nat.le_of_not_lt fun hlt => hcond ⟨⟨by simpa using hpS, hpv⟩, hlt⟩
  case vc3.step.isTrue.pre =>
    -- dequeue: casc_dequeue, tc_dequeue
    obtain ⟨hS, hv, hctx, hinv, htr⟩ := ‹_ = S0.push v ∧ _ ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascOuter G t v sd S0 b0 _ _ _ ∧ TrCasc G s t k v sd S0 T1 _ _ _ _›
    have hcur := range_eq_append_cons ‹List.range n = _ ++ _ :: _›
    have hlt := ‹_ < Array.size _›
    simp +zetaDelta only
    subst hcur
    refine ⟨hS, hv, hctx, casc_dequeue hinv hlt, ?_⟩
    rw [Array.toList_push]
    exact tc_dequeue hinv htr hlt
  case vc4.step.isTrue.post.success =>
    -- next pair: casc_next
    obtain ⟨hS, hv, hctx, hinv, htr⟩ := ‹_ = S0.push v ∧ _ ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascInner G t v sd S0 b0 _ _ _ _ _ ∧ TrCasc G s t k v sd S0 T1 _ _ _ _›
    have hcur := range_eq_append_cons ‹List.range n = _ ++ _ :: _›
    refine ⟨hS, hv, hctx, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      rw [← hcur]
      exact casc_next hinv
    · simp only [List.length_append, List.length_singleton]
      rw [← hcur]
      exact htr
  case vc5.step.isFalse =>
    -- break: casc_break
    obtain ⟨hS, hv, hctx, hinv, htr⟩ := ‹_ = S0.push v ∧ _ ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascOuter G t v sd S0 b0 _ _ _ ∧ TrCasc G s t k v sd S0 T1 _ _ _ _›
    have hcur := range_eq_append_cons ‹List.range n = _ ++ _ :: _›
    have hge := ‹¬_ < Array.size _›
    refine ⟨hS, hv, hctx, ?_, ?_⟩
    · simp only [List.length_range]
      subst hcur
      exact casc_break hinv hge
    · simp only [List.length_range]
      refine htr.mono_nd ?_
      have := congrArg List.length ‹List.range n = _ ++ _ :: _›
      simp at this; omega
  case vc6.pre =>
    -- the cascade event and the origin write: casc_init, tc_init
    obtain ⟨hb, hT1, hS, hv, hw, hctx⟩ := ‹_ = b0 ∧ _ = T1 ∧ _ = S0.push v ∧ _ ∧ _ ∧ CascCtx s t k v sd S0 b0 T1›
    simp +zetaDelta only
    refine ⟨hS, hv, hctx, ?_, ?_⟩
    · simp only [List.length_nil]; rw [hb]; exact casc_init hw
    · simp only [List.length_nil, Array.toList_push, hT1, hb]
      exact tc_init hctx
  case vc7.post.success =>
    -- all pairs processed: casc_final
    obtain ⟨hS, hv, hctx, hinv, htr⟩ := ‹_ = S0.push v ∧ _ ∧ CascCtx s t k v sd S0 b0 T1 ∧ CascOuter G t v sd S0 b0 _ _ _ ∧ TrCasc G s t k v sd S0 T1 _ _ _ _›
    simp only [List.length_range] at hinv htr
    exact ⟨hS, casc_final hG hv hinv, _, _, htr⟩
