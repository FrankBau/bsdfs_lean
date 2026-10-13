import Bsdfs.Phases

/-!
  Stage 3c, part 1: `RunFacts` from facts about single positions (`PosOK`): the event itself as the code emits it (`EvOK`),
  the call entered there (`CallOK`), and the cascade an event belongs to (`CascAt`).  The Hoare specs of `fruitful` and `search`
  establish `PosOK` segment by segment.  The facts at a position look only at positions up to the exit of the call or cascade
  involved, so they survive appending further events (`PosOK.append`).
-/

open Trace

variable {n : Nat}

/-! ## Appending events keeps the past -/

section append
variable {T E : List (Ev n)}

theorem Trace.lt_of_getElem? {q : Nat} {e : Ev n} (h : T[q]? = some e) : q < T.length := (List.getElem?_eq_some_iff.mp h).1

theorem Trace.stk_append : ∀ {q : Nat}, q ≤ T.length → stk (T ++ E) q = stk T q
  | 0, _ => rfl
  | q + 1, hq => by
    rw [Trace.stk_succ, Trace.stk_succ, List.getElem?_append_left (by omega), Trace.stk_append (by omega)]

theorem Trace.bar_append : ∀ {q : Nat}, q ≤ T.length → ∀ z, bar (T ++ E) q z = bar T q z
  | 0, _, _ => rfl
  | q + 1, hq, z => by
    rw [Trace.bar_succ, Trace.bar_succ, List.getElem?_append_left (by omega), Trace.bar_append (by omega)]

theorem Trace.isCasc_append {q : Nat} (hq : q < T.length) : isCasc (T ++ E) q = isCasc T q := by
  unfold isCasc; rw [List.getElem?_append_left hq]

theorem Trace.enterAt_append {q : Nat} (hq : q < T.length) (z : Fin n) : enterAt (T ++ E) z q = enterAt T z q := by
  unfold enterAt; rw [List.getElem?_append_left hq]

theorem Trace.deqAt_append {q : Nat} (hq : q < T.length) (z : Fin n) : deqAt (T ++ E) z q = deqAt T z q := by
  unfold deqAt; rw [List.getElem?_append_left hq]

theorem Trace.dropAt_append {q : Nat} (hq : q < T.length) (z : Fin n) : dropAt (T ++ E) z q = dropAt T z q := by
  unfold dropAt; rw [List.getElem?_append_left hq]

theorem Trace.fruitAt_append {q : Nat} (hq : q < T.length) (z : Fin n) : fruitAt (T ++ E) z q = fruitAt T z q := by
  unfold fruitAt; rw [List.getElem?_append_left hq]

theorem Trace.Frame.exit_lt {e x : Nat} (h : Frame T e x) : x < T.length := by
  obtain ⟨σ, v, hh, sd, f, hx⟩ := h.2.2.1
  exact Trace.lt_of_getElem? hx

theorem Trace.Frame.append {e x : Nat} (h : Frame T e x) : Frame (T ++ E) e x := by
  have hx := h.exit_lt
  obtain ⟨hex, ⟨σ, v, hh, he⟩, ⟨σ', v', hh', sd, f, hxe⟩, hsz, hopen⟩ := h
  refine ⟨hex, ⟨σ, v, hh, by rw [List.getElem?_append_left (by omega)]; exact he⟩, ⟨σ', v', hh', sd, f, by rw [List.getElem?_append_left hx]; exact hxe⟩, ?_, ?_⟩
  · rw [Trace.stk_append (by omega), Trace.stk_append (by omega)]; exact hsz
  · intro q h1 h2
    rw [Trace.stk_append (by omega), Trace.stk_append (by omega)]
    exact hopen q h1 h2

end append

/-! ## Facts at a position -/

section posok
variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- the facts of the event at q, as the code emits it -/
def EvOK (T : List (Ev n)) (q : Nat) : Prop :=
  match T[q]? with
  | some (.enter _ z h) => h = (stk T q).length ∧ z ∉ stk T q ∧ z ≠ t ∧ bar T q z + h ≤ k ∧ (h = 0 → q = 1) ∧ (stk T q ++ [z]).head? = some s ∧ G.Edges (stk T q ++ [z])
  | some (.exit _ v h _ _) => (stk T q).getLast? = some v ∧ h + 1 = (stk T q).length
  | some (.output _ P) => P = stk T q ++ [t] ∧ (stk T q).length ≤ k
  | some (.write _ x o nw .raise) => o = bar T q x ∧ x ≠ t ∧ (stk T q).getLast? = some x ∧ nw + (stk T q).length = k + 2 ∧ o < nw
  | some (.write _ x o nw .fruitful) => o = bar T q x ∧ x ≠ t ∧ (stk T q).getLast? = some x ∧ nw + (stk T q).length ≤ k + 1 ∧ o ≤ nw ∧ 1 ≤ nw ∧ 2 ≤ (stk T q).length
  | some (.write _ x o nw .drop) => o = bar T q x ∧ x ≠ t ∧ x ∉ stk T q ∧ nw < o ∧ 2 ≤ nw ∧ 2 ≤ (stk T q).length ∧ G.WalkLE (stk T q).dropLast t x nw
  | _ => True

/-- the facts of the call entered at e and exited at x -/
structure CallOK (T : List (Ev n)) (e x : Nat) : Prop where
  frame : Frame T e x
  ret : ∀ σ v h sd f, T[x]? = some (.exit σ v h sd f) → (f = true ↔ ∃ q σ' P, e < q ∧ q < x ∧ T[q]? = some (.output σ' P))
  fruitless_end : ∀ σe ve he σ v h sd, T[e]? = some (.enter σe ve he) → T[x]? = some (.exit σ v h sd false) → ∃ σ' o, T[x - 1]? = some (.write σ' ve o (k + 1 - he) .raise)
  mono : ∀ z, bar T e z ≤ bar T (x + 1) z
  scan : ∀ σ u h, T[e]? = some (.enter σ u h) → ∀ y ∈ G.succ u, ∃ q, e < q ∧ q < x ∧ stk T q = stk T (e + 1) ∧ (y = t ∨ y ∈ stk T q ∨ enterAt T y q = true ∨ k ≤ bar T q y + h)
  complete : ∀ p, G.BoundedPath k s t p → (stk T (e + 1)) <+: p → ∃ q σ, e < q ∧ q < x ∧ T[q]? = some (.output σ p)

/-- the cascade event at q belongs to the cascade (from c0) of the top frame (e, x), which runs to the exit at x -/
structure CascAt (T : List (Ev n)) (q e c0 x : Nat) : Prop where
  frame : Frame T e x
  lt : e < c0 ∧ c0 ≤ q ∧ q < x
  top : (stk T (e + 1)).length = (stk T q).length
  exit : ∃ σ v h sd, T[x]? = some (.exit σ v h sd true)
  all : ∀ r, c0 ≤ r → r < x → isCasc T r = true
  drop_last : ∀ y, dropAt T y q = true → ∀ r σ o nw kd, q < r → r < x → T[r]? ≠ some (.write σ y o nw kd)
  deq_once : ∀ z, deqAt T z q = true → ∀ r, q < r → r < x → deqAt T z r = false
  deq_drop : ∀ z, deqAt T z q = true → (stk T q).getLast? ≠ some z → ∃ q', c0 ≤ q' ∧ q' < q ∧ dropAt T z q' = true
  deq_origin : ∀ z, deqAt T z q = true → (stk T q).getLast? = some z → ∃ q', c0 ≤ q' ∧ q' < q ∧ fruitAt T z q' = true

/-- everything the delay proof needs to know about position q -/
structure PosOK (T : List (Ev n)) (q : Nat) : Prop where
  ev : EvOK G s t k T q
  call : ∀ σ v h, T[q]? = some (.enter σ v h) → ∃ x, CallOK G s t k T q x
  casc : isCasc T q = true → ∃ e c0 x, CascAt T q e c0 x

end posok

section stable
variable {G : Graph n} {s t : Fin n} {k : Nat} {T E : List (Ev n)}

theorem EvOK.append {q : Nat} (hq : q < T.length) (h : EvOK G s t k T q) : EvOK G s t k (T ++ E) q := by
  unfold EvOK at h ⊢
  rw [List.getElem?_append_left hq, Trace.stk_append (Nat.le_of_lt hq)]
  simp only [Trace.bar_append (Nat.le_of_lt hq)]
  exact h

theorem CallOK.append {e x : Nat} (h : CallOK G s t k T e x) : CallOK G s t k (T ++ E) e x := by
  have hx := h.frame.exit_lt
  have hex := h.frame.1
  refine ⟨h.frame.append, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ v hh sd f hxe
    rw [List.getElem?_append_left hx] at hxe
    rw [h.ret σ v hh sd f hxe]
    constructor
    · rintro ⟨q, σ', P, h1, h2, hq⟩; exact ⟨q, σ', P, h1, h2, by rw [List.getElem?_append_left (by omega)]; exact hq⟩
    · rintro ⟨q, σ', P, h1, h2, hq⟩; exact ⟨q, σ', P, h1, h2, by rw [List.getElem?_append_left (by omega)] at hq; exact hq⟩
  · intro σe ve he σ v hh sd hee hxe
    rw [List.getElem?_append_left (by omega)] at hee
    rw [List.getElem?_append_left hx] at hxe
    obtain ⟨σ', o, hw⟩ := h.fruitless_end σe ve he σ v hh sd hee hxe
    exact ⟨σ', o, by rw [List.getElem?_append_left (by omega)]; exact hw⟩
  · intro z
    rw [Trace.bar_append (by omega), Trace.bar_append (by omega)]
    exact h.mono z
  · intro σ u hh hee y hy
    rw [List.getElem?_append_left (by omega)] at hee
    obtain ⟨q, h1, h2, hst, hc⟩ := h.scan σ u hh hee y hy
    refine ⟨q, h1, h2, by rw [Trace.stk_append (by omega), Trace.stk_append (by omega)]; exact hst, ?_⟩
    rw [Trace.stk_append (by omega), Trace.enterAt_append (by omega), Trace.bar_append (by omega)]
    exact hc
  · intro p hp hpre
    rw [Trace.stk_append (by omega)] at hpre
    obtain ⟨q, σ, h1, h2, hq⟩ := h.complete p hp hpre
    exact ⟨q, σ, h1, h2, by rw [List.getElem?_append_left (by omega)]; exact hq⟩

theorem CascAt.append {q e c0 x : Nat} (h : CascAt T q e c0 x) : CascAt (T ++ E) q e c0 x := by
  have hx := h.frame.exit_lt
  obtain ⟨hl1, hl2, hl3⟩ := h.lt
  refine ⟨h.frame.append, h.lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Trace.stk_append (by have := h.frame.1; omega), Trace.stk_append (by omega)]; exact h.top
  · obtain ⟨σ, v, hh, sd, hxe⟩ := h.exit
    exact ⟨σ, v, hh, sd, by rw [List.getElem?_append_left hx]; exact hxe⟩
  · intro r h1 h2; rw [Trace.isCasc_append (by omega)]; exact h.all r h1 h2
  · intro y hd r σ o nw kd h1 h2
    rw [Trace.dropAt_append (by omega)] at hd
    rw [List.getElem?_append_left (by omega)]
    exact h.drop_last y hd r σ o nw kd h1 h2
  · intro z hd r h1 h2
    rw [Trace.deqAt_append (by omega)] at hd
    rw [Trace.deqAt_append (by omega)]
    exact h.deq_once z hd r h1 h2
  · intro z hd hno
    rw [Trace.deqAt_append (by omega)] at hd
    rw [Trace.stk_append (by omega)] at hno
    obtain ⟨q', h1, h2, hq'⟩ := h.deq_drop z hd hno
    exact ⟨q', h1, h2, by rw [Trace.dropAt_append (by omega)]; exact hq'⟩
  · intro z hd htop
    rw [Trace.deqAt_append (by omega)] at hd
    rw [Trace.stk_append (by omega)] at htop
    obtain ⟨q', h1, h2, hq'⟩ := h.deq_origin z hd htop
    exact ⟨q', h1, h2, by rw [Trace.fruitAt_append (by omega)]; exact hq'⟩

theorem PosOK.append {q : Nat} (hq : q < T.length) (h : PosOK G s t k T q) : PosOK G s t k (T ++ E) q := by
  refine ⟨h.ev.append hq, ?_, ?_⟩
  · intro σ v hh he
    rw [List.getElem?_append_left hq] at he
    obtain ⟨x, hc⟩ := h.call σ v hh he
    exact ⟨x, hc.append⟩
  · intro hc
    rw [Trace.isCasc_append hq] at hc
    obtain ⟨e, c0, x, hca⟩ := h.casc hc
    exact ⟨e, c0, x, hca.append⟩

end stable

/-! ## RunFacts from PosOK -/

section runfacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {T : List (Ev n)}

theorem Trace.lt_of_isCasc {q : Nat} (h : isCasc T q = true) : q < T.length := by
  unfold isCasc at h
  cases hq : T[q]? with
  | none => simp [hq] at h
  | some e => exact Trace.lt_of_getElem? hq

theorem runFacts_of_posOK (hP : ∀ q, q < T.length → PosOK G s t k T q) : RunFacts G s t k T := by
  have hev : ∀ q (e : Ev n), T[q]? = some e → EvOK G s t k T q := fun q e he => (hP q (Trace.lt_of_getElem? he)).ev
  have hcall : ∀ e x, Frame T e x → CallOK G s t k T e x := by
    intro e x hfr
    obtain ⟨σ, v, hh, he⟩ := hfr.2.1
    obtain ⟨x', hc⟩ := (hP e (Trace.lt_of_getElem? he)).call σ v hh he
    rw [hc.frame.exit_unique hfr] at hc
    exact hc
  have hcasc : ∀ q, isCasc T q = true → ∃ e c0 x, CascAt T q e c0 x := fun q hq => (hP q (Trace.lt_of_isCasc hq)).casc hq
  refine { enter := ?_, exit := ?_, output := ?_, write_old := ?_, raise := ?_, fruitful := ?_, drop := ?_, bar_t := ?_, frame := ?_, ret := ?_, fruitless_end := ?_, casc := ?_, drop_last := ?_, deq_drop := ?_, deq_origin := ?_, deq_once := ?_, mono := ?_, scan := ?_, complete := ?_, witness := ?_ }
  · intro q σ z h he; have := hev q _ he; simp only [EvOK, he] at this; exact this
  · intro q σ v h sd f he; have := hev q _ he; simp only [EvOK, he] at this; exact this
  · intro q σ P he; have := hev q _ he; simp only [EvOK, he] at this; exact this
  · intro q σ x o nw kd he; have := hev q _ he; cases kd <;> simp only [EvOK, he] at this <;> exact this.1
  · intro q σ x o nw he; have := hev q _ he; simp only [EvOK, he] at this; exact this.2.2
  · intro q σ x o nw he; have := hev q _ he; simp only [EvOK, he] at this; exact this.2.2
  · intro q σ x o nw he; have := hev q _ he; simp only [EvOK, he] at this; exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1⟩
  · intro q
    rw [Trace.bar_eq_of_no_write (p₁ := 0) (Nat.zero_le q) (fun r σ o nw kd _ _ hw => by
      have := hev r _ hw
      cases kd <;> simp only [EvOK, hw] at this <;> exact this.2.1 rfl)]
    rfl
  · intro e σ v h he
    obtain ⟨x, hc⟩ := (hP e (Trace.lt_of_getElem? he)).call σ v h he
    exact ⟨x, hc.frame⟩
  · intro e x σ v h sd f hfr hex; exact (hcall e x hfr).ret σ v h sd f hex
  · intro e x σe ve he σ v h sd hfr hee hex; exact (hcall e x hfr).fruitless_end σe ve he σ v h sd hee hex
  · intro q hq
    obtain ⟨e, c0, x, hca⟩ := hcasc q hq
    obtain ⟨σ, v, h, sd, hxe⟩ := hca.exit
    exact ⟨e, x, σ, v, h, sd, hca.frame, by have := hca.lt; omega, hca.lt.2.2, hca.top, hxe, fun r h1 h2 => hca.all r (by have := hca.lt; omega) h2⟩
  · intro θ y hd r σ o nw kd hθr hall
    obtain ⟨e, c0, x, hca⟩ := hcasc θ (Trace.isCasc_of_drop hd)
    rcases Nat.lt_or_ge r x with hrx | hrx
    · exact hca.drop_last y hd r σ o nw kd hθr hrx
    · obtain ⟨σx, vx, hx, sdx, hxe⟩ := hca.exit
      have := hall x (by have := hca.lt; omega) hrx
      rw [Trace.not_isCasc_of_exit hxe] at this; cases this
  · intro q z hd hno
    obtain ⟨e, c0, x, hca⟩ := hcasc q (Trace.isCasc_of_deq hd)
    obtain ⟨q', h1, h2, hq'⟩ := hca.deq_drop z hd hno
    exact ⟨q', h2, hq', fun r hr1 hr2 => hca.all r (by omega) (by have := hca.lt; omega)⟩
  · intro q z hd htop
    obtain ⟨e, c0, x, hca⟩ := hcasc q (Trace.isCasc_of_deq hd)
    obtain ⟨q', h1, h2, hq'⟩ := hca.deq_origin z hd htop
    exact ⟨q', h2, hq', fun r hr1 hr2 => hca.all r (by omega) (by have := hca.lt; omega)⟩
  · intro q₁ q₂ z hlt hd₁ hd₂
    obtain ⟨e, c0, x, hca⟩ := hcasc q₁ (Trace.isCasc_of_deq hd₁)
    obtain ⟨σx, vx, hx, sdx, hxe⟩ := hca.exit
    rcases Nat.lt_trichotomy q₂ x with h | h | h
    · rw [hca.deq_once z hd₁ q₂ hlt h] at hd₂; cases hd₂
    · subst h; simp [deqAt, hxe] at hd₂
    · exact ⟨x, hca.lt.2.2, h, Trace.not_isCasc_of_exit hxe⟩
  · intro e x hfr; exact (hcall e x hfr).mono
  · intro e x σ u h hfr he; exact (hcall e x hfr).scan σ u h he
  · intro e x hfr; exact (hcall e x hfr).complete
  · intro θ σ y o nw hd; have := hev θ _ hd; simp only [EvOK, hd] at this; exact this.2.2.2.2.2.2

end runfacts
