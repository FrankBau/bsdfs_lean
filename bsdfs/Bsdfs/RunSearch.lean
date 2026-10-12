import Bsdfs.RunCasc

/-!
  Stage 3c, part 3: the trace facts of `search v h`, as a Hoare spec extending `search_spec`.  The call emits its entry, the
  events of its loop (outputs and the complete traces of its child calls), then the cascade or the raise, and its exit.  Every
  position of this segment satisfies `PosOK`; the entry gets its `CallOK` at the exit.
-/

open Std.Do Trace

set_option mvcgen.warning false

variable {n : Nat}

/-! ## Outputs of a segment -/

section outputs

theorem outputs_append' (A B : List (Ev n)) : outputs (A ++ B) = outputs A ++ outputs B := by simp [outputs]

/-- an output of the events after e0 sits at a position after e0 -/
theorem output_pos {T0 E : List (Ev n)} {e0 : Ev n} {p : List (Fin n)} (hp : p ∈ outputs E) : ∃ q σ, T0.length < q ∧ q < (T0 ++ e0 :: E).length ∧ (T0 ++ e0 :: E)[q]? = some (.output σ p) := by
  unfold outputs at hp
  obtain ⟨e, he, hep⟩ := List.mem_filterMap.mp hp
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
  cases e with
  | output σ p' =>
    simp only [Option.some.injEq] at hep
    subst hep
    refine ⟨T0.length + (i + 1), σ, by omega, by simp; omega, ?_⟩
    rw [List.getElem?_append_right (by omega), show T0.length + (i + 1) - T0.length = i + 1 by omega, List.getElem?_cons_succ, List.getElem?_eq_getElem hi, hei]
  | _ => simp at hep

/-- an output at a position after e0 belongs to the outputs of the events after e0 -/
theorem output_mem {T0 E : List (Ev n)} {e0 : Ev n} {q σ : Nat} {p : List (Fin n)} (h1 : T0.length < q) (hq : (T0 ++ e0 :: E)[q]? = some (.output σ p)) : p ∈ outputs E := by
  rw [List.getElem?_append_right (by omega)] at hq
  obtain ⟨j, hj⟩ : ∃ j, q - T0.length = j + 1 := ⟨q - T0.length - 1, by omega⟩
  rw [hj, List.getElem?_cons_succ] at hq
  unfold outputs
  exact List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hq, rfl⟩

theorem outputs_nil_of_casc {T Ec : List (Ev n)} (h : ∀ q, T.length ≤ q → q < (T ++ Ec).length → isCasc (T ++ Ec) q = true) : outputs Ec = [] := by
  unfold outputs
  rw [List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
  have hc := h (T.length + i) (by omega) (by simp; omega)
  have hq : (T ++ Ec)[T.length + i]? = some e := by rw [List.getElem?_append_right (by omega), show T.length + i - T.length = i by omega, List.getElem?_eq_getElem hi, hei]
  cases e with
  | output σ p => simp [isCasc, hq] at hc
  | _ => rfl

end outputs

/-! ## The trace invariant of `search` -/

/-- what the trace facts of `search v h` need at its entry (T0 is the trace before the call) -/
structure TrPre (h : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (T0 : List (Ev n)) : Prop where
  stk : stk T0 T0.length = S0.toList
  bar : ∀ z, bar T0 T0.length z = b0[z]
  root : h = 0 → T0.length = 1

/-- the trace part of the loop invariant of `search v h` after the successors pref; T is the current trace -/
structure TrLoop (G : Graph n) (s t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (T0 : List (Ev n)) (pref : List (Fin n)) (b : Vector Nat n) (N : List (List (Fin n))) (T : List (Ev n)) : Prop where
  ext : ∃ σ E, T = T0 ++ Ev.enter σ v h :: E ∧ outputs E = N
  stk0 : stk T T0.length = S0.toList
  bar0 : ∀ z, bar T T0.length z = b0[z]
  stk_now : stk T T.length = (S0.push v).toList
  bar_now : ∀ z, bar T T.length z = b[z]
  isOpen : ∀ q, T0.length < q → q ≤ T.length → (stk T q).take (S0.size + 1) = (S0.push v).toList
  ev0 : EvOK G s t k T T0.length
  seg : ∀ q, T0.length < q → q < T.length → PosOK G s t k T q
  scan : ∀ y ∈ pref, ∃ q, T0.length < q ∧ q ≤ T.length ∧ stk T q = (S0.push v).toList ∧ (y = t ∨ y ∈ stk T q ∨ enterAt T y q = true ∨ k ≤ bar T q y + h)

/-- what `search v h` guarantees about the trace: T0 before the call, T after it, N its outputs, b the barriers at exit -/
structure TrCall (G : Graph n) (s t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (T0 : List (Ev n)) (N : List (List (Fin n))) (b : Vector Nat n) (T : List (Ev n)) : Prop where
  ext : ∃ σ E, T = T0 ++ Ev.enter σ v h :: E ∧ outputs E = N
  stk_now : stk T T.length = S0.toList
  bar_now : ∀ z, bar T T.length z = b[z]
  seg : ∀ q, T0.length ≤ q → q < T.length → PosOK G s t k T q
  call : CallOK G s t k T T0.length (T.length - 1)

section steps
variable {G : Graph n} {s t : Fin n} {k h : Nat} {v : Fin n} {S0 : Array (Fin n)} {b0 : Vector Nat n} {T0 : List (Ev n)}

theorem TrLoop.len {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) : T0.length < T.length := by
  obtain ⟨σ, E, hE, -⟩ := tl.ext; rw [hE]; simp

theorem TrLoop.enter {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) : ∃ σ, T[T0.length]? = some (.enter σ v h) := by
  obtain ⟨σ, E, hE, -⟩ := tl.ext; exact ⟨σ, by rw [hE]; simp⟩

/-- a scan fact at q ≤ |T| survives appending events -/
theorem scan_fact_append {T E : List (Ev n)} {q : Nat} {y : Fin n} (hq : q ≤ T.length) (hc : y = t ∨ y ∈ stk T q ∨ enterAt T y q = true ∨ k ≤ bar T q y + h) : y = t ∨ y ∈ stk (T ++ E) q ∨ enterAt (T ++ E) y q = true ∨ k ≤ bar (T ++ E) q y + h := by
  rw [Trace.stk_append hq, Trace.bar_append hq]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · obtain ⟨σ, hh, he⟩ := Trace.enterAt_iff.mp hc
    rw [Trace.enterAt_append (Trace.lt_of_getElem? he)]
    exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hc))

/-- the scan facts of the loop survive appending events -/
theorem TrLoop.scan_append {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T E : List (Ev n)} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) :
    ∀ y ∈ pref, ∃ q, T0.length < q ∧ q ≤ T.length ∧ stk (T ++ E) q = (S0.push v).toList ∧ (y = t ∨ y ∈ stk (T ++ E) q ∨ enterAt (T ++ E) y q = true ∨ k ≤ bar (T ++ E) q y + h) := by
  intro y hy
  obtain ⟨q, h1, h2, hst, hc⟩ := tl.scan y hy
  exact ⟨q, h1, h2, by rw [Trace.stk_append h2]; exact hst, scan_fact_append h2 hc⟩

/-- the entry: push v and the enter event -/
theorem tl_init (pre : SearchPre G s t k h v S0 b0) (tp : TrPre h S0 b0 T0) {σ : Nat} : TrLoop G s t k h v S0 b0 T0 [] b0 [] (T0 ++ [.enter σ v h]) where
  ext := ⟨σ, [], rfl, rfl⟩
  stk0 := by rw [Trace.stk_append (Nat.le_refl _)]; exact tp.stk
  bar0 := fun z => by rw [Trace.bar_append (Nat.le_refl _)]; exact tp.bar z
  stk_now := by rw [List.length_append, List.length_singleton, Trace.stk_snoc_enter, tp.stk]; simp
  bar_now := fun z => by rw [List.length_append, List.length_singleton, Trace.bar_snoc_other (by intros; simp), tp.bar z]
  isOpen := by
    intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rw [show q = T0.length + 1 by omega, Trace.stk_snoc_enter, tp.stk, List.take_of_length_le (by simp)]
    simp
  ev0 := by
    simp only [EvOK, List.getElem?_concat_length]
    rw [Trace.stk_append (Nat.le_refl _), tp.stk]
    simp only [Trace.bar_append (Nat.le_refl _), tp.bar]
    exact ⟨pre.length.symm, pre.v_not_mem, fun hvt => pre.t_not_mem (by simp [hvt]), pre.guard, tp.root, pre.stack.1, Graph.edges_of_stack pre.stack⟩
  seg := by intro q h1 h2; simp at h2; omega
  scan := by simp

/-- the closing edge (v, t): the output S0 ++ [v, t] -/
theorem tl_output (pre : SearchPre G s t k h v S0 b0) (hhk : h < k) {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) {σ : Nat} :
    TrLoop G s t k h v S0 b0 T0 (pref ++ [t]) b (N ++ [S0.toList ++ [v, t]]) (T ++ [.output σ (S0.toList ++ [v, t])]) := by
  have hlen0 := tl.len
  have hstk := Trace.stk_snoc_other (T := T) (e := .output σ (S0.toList ++ [v, t])) (by intros; simp) (by intros; simp)
  refine { ext := ?_, stk0 := ?_, bar0 := ?_, stk_now := ?_, bar_now := ?_, isOpen := ?_, ev0 := ?_, seg := ?_, scan := ?_ }
  · obtain ⟨σ0, E, hE, hN⟩ := tl.ext
    exact ⟨σ0, E ++ [.output σ (S0.toList ++ [v, t])], by rw [hE]; simp, by rw [outputs_append', hN]; simp [outputs]⟩
  · rw [Trace.stk_append (by omega)]; exact tl.stk0
  · intro z; rw [Trace.bar_append (by omega)]; exact tl.bar0 z
  · rw [List.length_append, List.length_singleton, hstk]; exact tl.stk_now
  · intro z; rw [List.length_append, List.length_singleton, Trace.bar_snoc_other (by intros; simp)]; exact tl.bar_now z
  · intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rcases Nat.lt_or_ge q (T.length + 1) with h | h
    · rw [Trace.stk_append (by omega)]; exact tl.isOpen q h1 (by omega)
    · rw [show q = T.length + 1 by omega, hstk, tl.stk_now, List.take_of_length_le (by simp)]
  · exact tl.ev0.append (by omega)
  · intro q h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    rcases Nat.lt_or_ge q T.length with h | h
    · exact (tl.seg q h1 h).append h
    · rw [show q = T.length by omega]
      refine ⟨?_, ?_, ?_⟩
      · simp only [EvOK, List.getElem?_concat_length]
        rw [Trace.stk_append (Nat.le_refl _), tl.stk_now]
        refine ⟨by simp, ?_⟩
        simp [pre.size]; omega
      · intro σ' v' h' he; simp at he
      · intro hc; simp [isCasc] at hc
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨q, h1, h2, hst, hc⟩ := tl.scan_append (E := [.output σ (S0.toList ++ [v, t])]) y hy
      exact ⟨q, h1, by simp; omega, hst, hc⟩
    · simp at hy; subst hy
      exact ⟨T.length, by omega, by simp, by rw [Trace.stk_append (Nat.le_refl _)]; exact tl.stk_now, Or.inl rfl⟩

/-- a pruned successor w: b[w] + h ≥ k -/
theorem tl_prune {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} {w : Fin n} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) (hw : ¬ b[w] + h < k) :
    TrLoop G s t k h v S0 b0 T0 (pref ++ [w]) b N T := by
  refine { tl with scan := ?_ }
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact tl.scan y hy
  · simp at hy; subst hy
    exact ⟨T.length, tl.len, Nat.le_refl _, tl.stk_now, Or.inr (Or.inr (Or.inr (by rw [tl.bar_now]; omega)))⟩

/-- a successor w on the stack -/
theorem tl_onstack {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} {w : Fin n} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) (hws : w ∈ S0.toList ++ [v]) :
    TrLoop G s t k h v S0 b0 T0 (pref ++ [w]) b N T := by
  refine { tl with scan := ?_ }
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact tl.scan y hy
  · simp at hy; subst hy
    exact ⟨T.length, tl.len, Nat.le_refl _, tl.stk_now, Or.inr (Or.inl (by rw [tl.stk_now]; simpa using hws))⟩

/-- the precondition of a child call -/
theorem tl_child_pre {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) :
    TrPre (h + 1) (S0.push v) b T := ⟨tl.stk_now, tl.bar_now, fun h' => by omega⟩

/-- back from a child call at w: its trace is appended -/
theorem tl_child_post {pref : List (Fin n)} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} {w : Fin n} {b' : Vector Nat n} {Nc : List (List (Fin n))} {T' : List (Ev n)}
    (tl : TrLoop G s t k h v S0 b0 T0 pref b N T) (tc : TrCall G s t k (h + 1) w (S0.push v) b T Nc b' T') :
    TrLoop G s t k h v S0 b0 T0 (pref ++ [w]) b' (N ++ Nc) T' := by
  have hlen0 := tl.len
  obtain ⟨σc, Ec, hEc, hNc⟩ := tc.ext
  have hT'len : T'.length = T.length + 1 + Ec.length := by rw [hEc]; simp; omega
  have hT'e : T'[T.length]? = some (.enter σc w (h + 1)) := by rw [hEc]; simp
  have hfr := tc.call.frame
  have hS : (S0.push v).toList.length = S0.size + 1 := by simp
  refine { ext := ?_, stk0 := ?_, bar0 := ?_, stk_now := tc.stk_now, bar_now := tc.bar_now, isOpen := ?_, ev0 := ?_, seg := ?_, scan := ?_ }
  · obtain ⟨σ0, E, hE, hN⟩ := tl.ext
    refine ⟨σ0, E ++ Ev.enter σc w (h + 1) :: Ec, by rw [hEc, hE]; simp, ?_⟩
    rw [outputs_append', hN, ← hNc]; simp [outputs]
  · rw [hEc, Trace.stk_append (by omega)]; exact tl.stk0
  · intro z; rw [hEc, Trace.bar_append (by omega)]; exact tl.bar0 z
  · intro q h1 h2
    rcases Nat.lt_or_ge T.length q with hq | hq
    · rcases Nat.lt_or_ge q T'.length with hq' | hq'
      · -- inside the child's frame: its stack starts with S0.push v
        have hp := hfr.prefix (q := q) hq (by omega)
        have he1 : stk T' (T.length + 1) = (S0.push v).toList ++ [w] := by
          rw [Trace.stk_succ_enter hT'e, hEc, Trace.stk_append (Nat.le_refl _), tl.stk_now]
        have he0 : (stk T' T.length).length = S0.size + 1 := by
          rw [hEc, Trace.stk_append (Nat.le_refl _), tl.stk_now]; simp
        rw [he1, he0] at hp
        have := congrArg (List.take (S0.size + 1)) hp
        rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' (by simp)] at this
        exact this
      · rw [show q = T'.length by omega, tc.stk_now, List.take_of_length_le (by simp)]
    · rw [hEc, Trace.stk_append hq]; exact tl.isOpen q h1 hq
  · rw [hEc]; exact tl.ev0.append (by omega)
  · intro q h1 h2
    rcases Nat.lt_or_ge q T.length with hq | hq
    · rw [hEc]; exact (tl.seg q h1 hq).append hq
    · exact tc.seg q hq h2
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨q, h1, h2, hst, hc⟩ := tl.scan_append (E := Ev.enter σc w (h + 1) :: Ec) y hy
      rw [← hEc] at hst hc
      exact ⟨q, h1, by omega, hst, hc⟩
    · simp at hy; subst hy
      refine ⟨T.length, hlen0, by omega, by rw [hEc, Trace.stk_append (Nat.le_refl _)]; exact tl.stk_now, Or.inr (Or.inr (Or.inl ?_))⟩
      simp [enterAt, hT'e]

end steps

/-! ## The exit of `search` -/

section exits
variable {G : Graph n} {s t : Fin n} {k h : Nat} {v : Fin n} {S0 : Array (Fin n)} {b0 : Vector Nat n} {T0 : List (Ev n)}

theorem Trace.isCasc_enter {T : List (Ev n)} {q σ : Nat} {u : Fin n} {hh : Nat} (he : T[q]? = some (.enter σ u hh)) : isCasc T q = false := by simp [isCasc, he]

theorem Trace.isCasc_raise {T : List (Ev n)} {q σ : Nat} {x : Fin n} {o nw : Nat} (he : T[q]? = some (.write σ x o nw .raise)) : isCasc T q = false := by simp [isCasc, he]

/-- Per-Call Global Monotonicity (lem:per-call-monotone): the barriers at exit are at least those at entry -/
theorem SearchPost.mono_all (pre : SearchPre G s t k h v S0 b0) {r : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hpost : SearchPost G s t k h v S0 b0 r b N) (z : Fin n) : b0[z] ≤ b[z] := by
  by_cases hz : z ∈ S0.toList
  · exact Nat.le_of_eq (hpost.stack z hz).symm
  · rcases hpost.mon z with h1 | ⟨l, hl, hw⟩
    · exact h1
    · have := pre.ec.walk_bound hz hw; have := pre.target; omega

theorem le_length_of_take_eq {l l' : List (Fin n)} {m : Nat} (h : l.take m = l') (hl' : l'.length = m) : m ≤ l.length := by
  have := congrArg List.length h
  rw [List.length_take] at this
  omega

/-- the exit of `search v h` after its loop and the tail Etl (cascade or raise): the call's facts and the segment's -/
theorem tl_exit (pre : SearchPre G s t k h v S0 b0) {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} (tl : TrLoop G s t k h v S0 b0 T0 (G.succ v) b N T) {Etl : List (Ev n)} {σx sd : Nat} {f : Bool} {bf : Vector Nat n}
    (hEtl : 0 < Etl.length)
    (hstk : ∀ q, T.length ≤ q → q ≤ T.length + Etl.length → stk (T ++ Etl) q = (S0.push v).toList)
    (hout : outputs Etl = [])
    (hbar : ∀ z, bar (T ++ Etl) (T.length + Etl.length) z = bf[z])
    (hpost : SearchPost G s t k h v S0 b0 sd bf N)
    (hret : f = true ↔ N ≠ [])
    (hfl : f = false → ∃ σ' o, (T ++ Etl)[T.length + Etl.length - 1]? = some (.write σ' v o (k + 1 - h) .raise))
    (htail : Frame (T ++ Etl ++ [.exit σx v h sd f]) T0.length (T.length + Etl.length) → ∀ q, T.length ≤ q → q < T.length + Etl.length → PosOK G s t k (T ++ Etl ++ [.exit σx v h sd f]) q) :
    TrCall G s t k h v S0 b0 T0 N bf (T ++ Etl ++ [.exit σx v h sd f]) := by
  have hlen0 := tl.len
  have hTE : (T ++ Etl).length = T.length + Etl.length := List.length_append
  have hlen : (T ++ Etl ++ [Ev.exit σx v h sd f]).length = T.length + Etl.length + 1 := by simp; omega
  have hassoc : T ++ Etl ++ [Ev.exit σx v h sd f] = T ++ (Etl ++ [Ev.exit σx v h sd f]) := List.append_assoc _ _ _
  have hx : (T ++ Etl ++ [Ev.exit σx v h sd f])[T.length + Etl.length]? = some (.exit σx v h sd f) := by rw [← hTE]; simp
  have hstkx : stk (T ++ Etl ++ [Ev.exit σx v h sd f]) (T.length + Etl.length) = (S0.push v).toList := by
    rw [Trace.stk_append (by simp), hstk _ (by omega) (Nat.le_refl _)]
  have hstkf : stk (T ++ Etl ++ [Ev.exit σx v h sd f]) (T.length + Etl.length + 1) = S0.toList := by
    rw [← hTE, Trace.stk_snoc_exit, hTE, hstk _ (by omega) (Nat.le_refl _)]; simp
  have hbarf : ∀ z, bar (T ++ Etl ++ [Ev.exit σx v h sd f]) (T.length + Etl.length + 1) z = bf[z] := by
    intro z; rw [← hTE, Trace.bar_snoc_other (by intros; simp), hTE, hbar z]
  obtain ⟨σ0, hent⟩ := tl.enter
  have hent' : (T ++ Etl ++ [Ev.exit σx v h sd f])[T0.length]? = some (.enter σ0 v h) := by rw [hassoc, List.getElem?_append_left hlen0]; exact hent
  have hstk0 : stk (T ++ Etl ++ [Ev.exit σx v h sd f]) T0.length = S0.toList := by rw [hassoc, Trace.stk_append (by omega)]; exact tl.stk0
  have hstk1 : stk (T ++ Etl ++ [Ev.exit σx v h sd f]) (T0.length + 1) = (S0.push v).toList := by rw [Trace.stk_succ_enter hent', hstk0]; simp
  have hfr : Frame (T ++ Etl ++ [Ev.exit σx v h sd f]) T0.length (T.length + Etl.length) := by
    refine ⟨by omega, ⟨σ0, v, h, hent'⟩, ⟨σx, v, h, sd, f, hx⟩, by rw [hstkf, hstk0], ?_⟩
    intro q h1 h2
    rw [hstk0]
    rcases Nat.lt_or_ge T.length q with hq | hq
    · rw [Trace.stk_append (by simp; omega), hstk q (by omega) h2]; simp
    · rw [hassoc, Trace.stk_append hq]
      have := le_length_of_take_eq (tl.isOpen q h1 hq) (by simp)
      simp at this ⊢; omega
  -- the outputs of the call are the outputs of its loop
  obtain ⟨σe, E, hE, hN⟩ := tl.ext
  have hTf : T ++ Etl ++ [Ev.exit σx v h sd f] = T0 ++ Ev.enter σe v h :: (E ++ Etl ++ [Ev.exit σx v h sd f]) := by rw [hE]; simp
  have houts : outputs (E ++ Etl ++ [Ev.exit σx v h sd f]) = N := by rw [outputs_append', outputs_append', hN, hout]; simp [outputs]
  have hout_iff : (∃ q σ' P, T0.length < q ∧ q < T.length + Etl.length ∧ (T ++ Etl ++ [Ev.exit σx v h sd f])[q]? = some (.output σ' P)) ↔ N ≠ [] := by
    constructor
    · rintro ⟨q, σ', P, h1, h2, hq⟩
      rw [hTf] at hq
      have := output_mem h1 hq
      rw [houts] at this
      exact List.ne_nil_of_mem this
    · intro hne
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil N hne
      rw [← hN] at hp
      obtain ⟨q, σ', h1, h2, hq⟩ := output_pos (T0 := T0) (e0 := Ev.enter σe v h) hp
      rw [← hE] at h2 hq
      exact ⟨q, σ', p, h1, by omega, by rw [hassoc, List.getElem?_append_left h2]; exact hq⟩
  have hcall : CallOK G s t k (T ++ Etl ++ [Ev.exit σx v h sd f]) T0.length (T.length + Etl.length) := by
    refine ⟨hfr, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ' v' h' sd' f' hx'
      rw [hx] at hx'
      simp only [Option.some.injEq, Ev.exit.injEq] at hx'
      rw [← hx'.2.2.2.2, hret, hout_iff]
    · intro σe' ve he σ' v' h' sd' hee hx'
      rw [hent'] at hee
      simp only [Option.some.injEq, Ev.enter.injEq] at hee
      obtain ⟨-, hve, hhe⟩ := hee
      rw [hx] at hx'
      simp only [Option.some.injEq, Ev.exit.injEq] at hx'
      obtain ⟨σ'', o, hw⟩ := hfl hx'.2.2.2.2
      refine ⟨σ'', o, ?_⟩
      rw [← hve, ← hhe, List.getElem?_append_left (by simp; omega)]
      exact hw
    · intro z
      rw [hbarf z, hassoc, Trace.bar_append (by omega), tl.bar0 z]
      exact hpost.mono_all pre z
    · intro σ' u h' hee y hy
      rw [hent'] at hee
      simp only [Option.some.injEq, Ev.enter.injEq] at hee
      obtain ⟨-, hu, hh'⟩ := hee
      subst hu hh'
      obtain ⟨q, h1, h2, hst, hc⟩ := tl.scan_append (E := Etl ++ [Ev.exit σx v h sd f]) y hy
      rw [← hassoc] at hst hc
      exact ⟨q, h1, by omega, by rw [hst, hstk1], hc⟩
    · intro p hp hpre
      rw [hstk1] at hpre
      have hmem := hpost.complete p hp (by simpa using hpre)
      rw [← hN] at hmem
      obtain ⟨q, σ', h1, h2, hq⟩ := output_pos (T0 := T0) (e0 := Ev.enter σe v h) hmem
      rw [← hE] at h2 hq
      exact ⟨q, σ', h1, by omega, by rw [hassoc, List.getElem?_append_left h2]; exact hq⟩
  refine { ext := ⟨σe, E ++ Etl ++ [Ev.exit σx v h sd f], hTf, houts⟩, stk_now := by rw [hlen]; exact hstkf, bar_now := by rw [hlen]; exact hbarf, seg := ?_, call := by rw [hlen, Nat.add_sub_cancel]; exact hcall }
  intro q h1 h2
  rw [hlen] at h2
  rcases Nat.eq_or_lt_of_le h1 with hq | hq
  · -- the entry
    subst hq
    refine ⟨by rw [hassoc]; exact tl.ev0.append (by omega), fun σ' v' h' _ => ⟨_, hcall⟩, fun hc => ?_⟩
    rw [Trace.isCasc_enter hent'] at hc; cases hc
  rcases Nat.lt_or_ge q T.length with hq' | hq'
  · rw [hassoc]; exact (tl.seg q hq hq').append hq'
  rcases Nat.lt_or_ge q (T.length + Etl.length) with hq'' | hq''
  · exact htail hfr q hq' hq''
  · -- the exit
    rw [show q = T.length + Etl.length by omega]
    refine ⟨?_, fun σ' v' h' he => by rw [hx] at he; simp at he, fun hc => by rw [RunFacts.not_isCasc_of_exit hx] at hc; cases hc⟩
    simp only [EvOK, hx, hstkx]
    exact ⟨by simp, by simp [pre.size]⟩

/-- the cascade's context, from the loop invariant at the end of the loop (fruitful, h > 0) -/
theorem tl_casc_ctx (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (tl : TrLoop G s t k h v S0 b0 T0 (G.succ v) b N T) (hsd : sd ≤ k) (hh : 0 < h) :
    CascCtx s t k v sd S0 b T where
  stk := tl.stk_now
  bar := tl.bar_now
  target := hinv.target
  sd_pos := hinv.ret_pos
  sd_le := by have := hinv.fruitful_return hsd; have := pre.size; omega
  bv := by
    rw [hinv.bv]
    obtain ⟨l, hl, hw⟩ := hinv.walk_sd pre hsd
    have := pre.ec.walk_bound pre.v_not_mem hw
    have := pre.target
    omega
  depth := by have := pre.size; omega
  vt := fun hvt => pre.t_not_mem (by simp [hvt])

/-- exit of a fruitful call (h > 0): the cascade, then the exit -/
theorem tl_exit_fruitful (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b b' : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} {nd : Nat} {queue : Array (Fin n × Nat)} {Ec : List (Ev n)} {σx : Nat}
    (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (tl : TrLoop G s t k h v S0 b0 T0 (G.succ v) b N T) (hsd : sd ≤ k)
    (htc : TrCasc G s t k v sd S0 T nd queue b' (T ++ Ec)) (hpost : SearchPost G s t k h v S0 b0 sd b' N) :
    TrCall G s t k h v S0 b0 T0 N b' (T ++ Ec ++ [.exit σx v h sd (decide (sd ≤ k))]) := by
  have hlenc := htc.len
  have hEc : 2 ≤ Ec.length := by simp at hlenc; omega
  have hlen0 := tl.len
  have hd : decide (sd ≤ k) = true := by simp [hsd]
  refine tl_exit pre tl (by omega) (fun q h1 h2 => htc.stk q h1 (by simp; omega)) (outputs_nil_of_casc (fun q h1 h2 => htc.casc q h1 h2)) (fun z => by have := htc.bar z; simpa using this) hpost ?_ ?_ ?_
  · rw [hd]
    simp only [true_iff]
    obtain ⟨p, hp, -⟩ := hinv.ret_wit hsd
    exact List.ne_nil_of_mem hp
  · intro hf; rw [hd] at hf; cases hf
  · intro hfr q h1 h2
    have hq : q < (T ++ Ec).length := by simp; omega
    have hcq : isCasc (T ++ Ec) q = true := htc.casc q h1 hq
    have hstkq : stk (T ++ Ec ++ [Ev.exit σx v h sd (decide (sd ≤ k))]) q = (S0.push v).toList := by rw [Trace.stk_append (by omega)]; exact htc.stk q h1 (by omega)
    refine ⟨(htc.ev q h1 hq).append hq, fun σ' v' h' he => ?_, fun _ => ⟨T0.length, T.length, T.length + Ec.length, ?_⟩⟩
    · rw [List.getElem?_append_left hq] at he
      rw [Trace.isCasc_enter he] at hcq; cases hcq
    have h0 : stk (T ++ Ec ++ [Ev.exit σx v h sd (decide (sd ≤ k))]) T0.length = S0.toList := by
      rw [List.append_assoc, Trace.stk_append (by omega)]; exact tl.stk0
    refine { frame := hfr, lt := ⟨hlen0, h1, h2⟩, top := ?_, exit := ?_, all := ?_, drop_last := ?_, deq_once := ?_, deq_drop := ?_, deq_origin := ?_ }
    · rw [hfr.push, h0, hstkq]; simp
    · refine ⟨σx, v, h, sd, ?_⟩
      rw [← hd, show T.length + Ec.length = (T ++ Ec).length by simp]
      simp
    · intro r hr1 hr2
      rw [Trace.isCasc_append (by simp; omega)]
      exact htc.casc r hr1 (by simp; omega)
    · intro y hdy r σ' o nw kd hqr hrx
      rw [Trace.dropAt_append hq] at hdy
      rw [List.getElem?_append_left (by simp; omega)]
      exact htc.drop_last q y h1 hdy r σ' o nw kd hqr
    · intro z hdz r hqr hrx
      rw [Trace.deqAt_append hq] at hdz
      rw [Trace.deqAt_append (by simp; omega)]
      exact htc.deq_once q r z h1 hqr hdz
    · intro z hdz hne
      rw [Trace.deqAt_append hq] at hdz
      have hzv : z ≠ v := by intro hzv; apply hne; rw [hstkq, hzv]; simp
      obtain ⟨q', h1', h2', hq'⟩ := htc.deq_drop q z h1 hdz hzv
      exact ⟨q', h1', h2', by rw [Trace.dropAt_append (by omega)]; exact hq'⟩
    · intro z hdz htop
      rw [hstkq] at htop
      have hzv : z = v := by simp at htop; exact htop.symm
      rw [Trace.deqAt_append hq] at hdz
      have hq2 : T.length + 1 < q := by
        obtain ⟨σc, hc⟩ := htc.start
        obtain ⟨σf, o, nw, hw⟩ := Trace.fruitAt_iff.mp htc.fruit
        rcases Nat.lt_trichotomy q (T.length + 1) with h' | h' | h'
        · rw [show q = T.length by omega, Trace.deqAt_ne hc (by intros; simp)] at hdz; cases hdz
        · rw [h', Trace.deqAt_ne hw (by intros; simp)] at hdz; cases hdz
        · exact h'
      exact ⟨T.length + 1, by omega, hq2, by rw [Trace.fruitAt_append (by omega), hzv]; exact htc.fruit⟩

/-- exit of a call without cascade (fruitless, or the early exit at s): the raise, then the exit -/
theorem tl_exit_raise (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} {T : List (Ev n)} {σw σx : Nat}
    (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (tl : TrLoop G s t k h v S0 b0 T0 (G.succ v) b N T)
    (hpost : SearchPost G s t k h v S0 b0 sd (b.set v.1 (k - h + 1) v.2) N) :
    TrCall G s t k h v S0 b0 T0 N (b.set v.1 (k - h + 1) v.2) (T ++ [.write σw v b[v] (k - h + 1) .raise] ++ [.exit σx v h sd (decide (sd ≤ k))]) := by
  have hlen0 := tl.len
  have hguard := pre.guard
  have hbv := hinv.bv
  have hhk : h ≤ k := by omega
  have hlast : (T ++ [Ev.write σw v b[v] (k - h + 1) .raise])[T.length]? = some (.write σw v b[v] (k - h + 1) .raise) := by simp
  have hstkw := Trace.stk_snoc_other (T := T) (e := .write σw v b[v] (k - h + 1) .raise) (by intros; simp) (by intros; simp)
  refine tl_exit pre tl (by simp) ?_ (by simp [outputs]) ?_ hpost ?_ ?_ ?_
  · intro q h1 h2
    simp only [List.length_singleton] at h2
    rcases Nat.lt_or_ge q (T.length + 1) with h' | h'
    · rw [Trace.stk_append (by omega), show q = T.length by omega]; exact tl.stk_now
    · rw [show q = T.length + 1 by omega, hstkw]; exact tl.stk_now
  · intro z
    simp only [List.length_singleton]
    rw [Trace.bar_snoc_write, tl.bar_now z]
    by_cases hvz : v = z
    · subst hvz; simp
    · simp [hvz, Fin.val_inj]
  · simp only [decide_eq_true_eq]
    constructor
    · intro hsd; obtain ⟨p, hp, -⟩ := hinv.ret_wit hsd; exact List.ne_nil_of_mem hp
    · intro hne
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil N hne
      have h1 := hpost.ret_min p hp
      have h2 := (hpost.sound p hp).1.2.2.2.1
      omega
  · intro _
    refine ⟨σw, b[v], ?_⟩
    simp only [List.length_singleton, Nat.add_sub_cancel]
    rw [show k + 1 - h = k - h + 1 by omega]; exact hlast
  · intro hfr q h1 h2
    simp only [List.length_singleton] at h2
    rw [show q = T.length by omega]
    have hq : T.length < (T ++ [Ev.write σw v b[v] (k - h + 1) .raise]).length := by simp
    have hlast' : (T ++ [Ev.write σw v b[v] (k - h + 1) .raise] ++ [Ev.exit σx v h sd (decide (sd ≤ k))])[T.length]? = some (.write σw v b[v] (k - h + 1) .raise) := by rw [List.getElem?_append_left hq]; exact hlast
    refine ⟨?_, fun σ' v' h' he => by rw [hlast'] at he; simp at he, fun hc => by rw [Trace.isCasc_raise hlast'] at hc; cases hc⟩
    simp only [EvOK, hlast']
    rw [Trace.stk_append (by simp), Trace.stk_append (Nat.le_refl _), tl.stk_now, Trace.bar_append (by simp), Trace.bar_append (Nat.le_refl _), tl.bar_now]
    exact ⟨rfl, fun hvt => pre.t_not_mem (by simp [hvt]), by simp, by simp [pre.size]; omega, by omega⟩

end exits

/-! ## The spec -/

/-- spec of `search v h` with the trace: `search_spec` plus the trace facts of the call's segment; induction on k - h -/
theorem search_spec_tr (G : Graph n) (hG : G.WF) (s t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (T0 : List (Ev n)) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.trace.toList = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0⌝⦄
    search G t k v h
    ⦃⇓ r st => ⌜st.S = S0 ∧ ∃ N, SearchPost G s t k h v S0 b0 r st.b N ∧ TrCall G s t k h v S0 b0 T0 N st.b st.trace.toList⌝⦄ := by
  -- spec of the recursive call; vacuous unless h < k
  have ih : ∀ w (S1 : Array (Fin n)) (b1 : Vector Nat n) (T1 : List (Ev n)), ⦃fun st => ⌜st.S = S1 ∧ st.b = b1 ∧ st.trace.toList = T1 ∧ SearchPre G s t k (h + 1) w S1 b1 ∧ TrPre (h + 1) S1 b1 T1⌝⦄ search G t k w (h + 1) ⦃⇓ r st => ⌜st.S = S1 ∧ ∃ N, SearchPost G s t k (h + 1) w S1 b1 r st.b N ∧ TrCall G s t k (h + 1) w S1 b1 T1 N st.b st.trace.toList⌝⦄ := by
    intro w S1 b1 T1
    by_cases hk : h < k
    · exact search_spec_tr G hG s t k (h + 1) w S1 b1 T1
    · intro st hP
      exact absurd hP.2.2.2.1.guard (by omega)
  have hcasc := fruitful_spec_tr G hG s t k v S0
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, ih, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜st.S = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 xs.prefix sd st.b N ∧ TrLoop G s t k h v S0 b0 T0 xs.prefix st.b N st.trace.toList⌝
  case vc1.step.isTrue.isTrue =>
    -- closing edge (v, t): output S0 ++ [v, t]
    obtain ⟨-, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    have hmem := mem_of_eq_append_cons hsplit
    have hnp := not_mem_of_nodup_split (hG.succ_nodup v) hsplit
    have htest := ‹_ + h < k›
    have hcur := ‹_ = t›
    simp +zetaDelta only at htest ⊢
    subst hcur
    have hhk : h < k := by have := hinv.target; omega
    refine ⟨hS, N ++ [S0.toList ++ [v, _]], loop_output pre hinv hmem hnp htest, ?_⟩
    rw [Array.toList_push, hS, push_append]
    exact tl_output pre hhk tl
  case vc2.step.isTrue.isFalse.isTrue.pre =>
    -- recursive call: its precondition
    obtain ⟨-, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have htest := ‹_ + h < k›
    have hnt := ‹¬_ = t›
    have hnS := ‹¬_ ∈ _›
    simp +zetaDelta only at htest hnS ⊢
    rw [hS] at hnS ⊢
    exact ⟨trivial, trivial, trivial, loop_child_pre pre hinv hmem htest hnt (by simpa using hnS), tl_child_pre tl⟩
  case vc3.step.isTrue.isFalse.isTrue.post.success =>
    -- recursive call: back in the loop
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    obtain ⟨hS', Nc, hpost, tc⟩ := ‹_ ∧ ∃ N, SearchPost G s t k (h + 1) _ _ _ _ _ N ∧ TrCall G s t k (h + 1) _ _ _ _ N _ _›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    have hnp := not_mem_of_nodup_split (hG.succ_nodup v) hsplit
    have htest := ‹_ + h < k›
    have hnt := ‹¬_ = t›
    simp +zetaDelta only at hS' hpost tc htest
    rw [hS] at hS' hpost tc
    exact ⟨hS', N ++ Nc, loop_child_post hinv htest hnt hnp hpost, tl_child_post tl tc⟩
  case vc4.step.isTrue.isFalse.isFalse =>
    -- successor on the stack
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hnt := ‹¬_ = t›
    have hin := ‹¬¬_ ∈ _›
    simp +zetaDelta only at hin ⊢
    rw [hS] at hin
    have hin' := Classical.not_not.mp hin
    exact ⟨hS, N, loop_onstack hinv (by simpa using hin') hnt, tl_onstack tl (by simpa using hin')⟩
  case vc5.step.isFalse =>
    -- pruned successor
    obtain ⟨-, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hpr := ‹¬_ + h < k›
    simp +zetaDelta only at hpr ⊢
    exact ⟨hS, N, loop_prune pre hinv hpr, tl_prune tl hpr⟩
  case vc6.pre =>
    -- entry: push v, the enter event
    obtain ⟨hS, hb, hT, pre, tp⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    simp +zetaDelta only
    rw [hS, hb, Array.toList_push, hT]
    exact ⟨rfl, [], loop_init pre, tl_init pre tp⟩
  case vc7.post.success.isTrue.pre =>
    -- fruitful (h > 0): precondition of the cascade
    obtain ⟨-, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hc := ‹_ ≤ k ∧ h > 0›
    exact ⟨trivial, trivial, hS, pre.v_not_mem, hinv.walk_sd pre hc.1, tl_casc_ctx pre hinv tl hc.1 hc.2⟩
  case vc8.post.success.isTrue.post.success =>
    -- fruitful (h > 0): after the cascade, exit and pop
    obtain ⟨-, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hc := ‹_ ≤ k ∧ h > 0›
    obtain ⟨hS', hcp, nd, queue, htc⟩ := ‹_ = S0.push v ∧ CascPost G t v _ S0 _ _ ∧ ∃ nd queue, TrCasc G s t k v _ S0 _ nd queue _ _›
    simp +zetaDelta only
    obtain ⟨Ec, hEc⟩ := htc.ext
    rw [hEc] at htc
    rw [hS', Array.toList_push, hEc]
    have hpost := post_fruitful pre hinv hc.1 hc.2 hcp
    exact ⟨by simp, N, hpost, tl_exit_fruitful pre hinv tl hc.1 htc hpost⟩
  case vc9.post.success.isFalse =>
    -- fruitless, or the early exit at s: raise, exit and pop
    obtain ⟨-, -, -, pre, -⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = T0 ∧ SearchPre G s t k h v S0 b0 ∧ TrPre h S0 b0 T0›
    obtain ⟨hS, N, hinv, tl⟩ := ‹_ = S0.push v ∧ ∃ N, LoopInv G s t k h v S0 b0 _ _ _ N ∧ TrLoop G s t k h v S0 b0 T0 _ _ N _›
    have hc := ‹¬(_ ≤ k ∧ h > 0)›
    simp +zetaDelta only
    rw [hS, Array.toList_push, Array.toList_push]
    have hpost := post_raise pre hinv hc
    exact ⟨by simp, N, hpost, tl_exit_raise pre hinv tl hpost⟩
termination_by k - h
