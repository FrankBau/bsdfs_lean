/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Amortized

/-!
  Two Visits per Pair: between consecutive observable events, BS-DFS visits every node at most twice at each depth.  A visit of
  z is an entry of z or a dequeue of z.  Its depth is the depth of the search right after it: the new frame's for an entry, the
  cascade origin's for a dequeue; so the stack holds h + 1 nodes after a visit at depth h.

  The ascent has no dequeues, and at most one entry of z at each depth (One Entry per Pair per Phase).  The descent has at most
  one visit of z at each depth:
  - entries: One Entry per Pair per Phase;
  - dequeues: the cascades of an interval belong to frames open at its start, one per depth, and a cascade dequeues z at most once;
  - a dequeue and an entry: if z was dropped by the origin at depth h, Descent Split puts every descent call at z at depth ≥ h + 1;
    if z is the origin, its frame contains an output P through z at index h, and a call at z at depth h entered in the descent
    would make, by Call Completeness, the lowest call on its stack whose node lies on P from z on output a path inside the descent.
-/

open Trace

variable {n : Nat}

/-- a visit of z at depth h at position q: an entry or a dequeue of z after which the stack holds h + 1 nodes -/
def Trace.visitAt (tr : List (Ev n)) (z : Fin n) (h q : Nat) : Bool :=
  (enterAt tr z q || deqAt tr z q) && (stk tr (q + 1)).length == h + 1

section
variable {tr : List (Ev n)}

/-- cascade events are neither entries nor exits, so the stack stays put during a cascade -/
theorem Trace.stk_eq_of_casc {p : Nat} : ∀ d, (∀ r, p ≤ r → r < p + d → isCasc tr r = true) → stk tr (p + d) = stk tr p
  | 0, _ => rfl
  | d + 1, h => by
    have hc := h (p + d) (by omega) (by omega)
    rw [show p + (d + 1) = p + d + 1 by omega, Trace.stk_succ_other (fun σ v hh he => by simp [isCasc, he] at hc) (fun σ v hh sd f he => by simp [isCasc, he] at hc)]
    exact Trace.stk_eq_of_casc d (fun r h1 h2 => h r h1 (by omega))

theorem Trace.stk_succ_deq {q : Nat} {z : Fin n} (hd : deqAt tr z q = true) : stk tr (q + 1) = stk tr q := by
  obtain ⟨σ, d, he⟩ := Trace.deqAt_iff.mp hd
  exact Trace.stk_succ_other (fun σ' v hh h' => by rw [he] at h'; cases h') (fun σ' v hh sd f h' => by rw [he] at h'; cases h')

theorem Trace.mem_outputs {q σ : Nat} {P : List (Fin n)} (hq : tr[q]? = some (.output σ P)) : P ∈ outputs tr := by
  unfold outputs
  exact List.mem_filterMap.mpr ⟨.output σ P, List.mem_of_getElem? hq, rfl⟩

end

namespace RunFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hR : RunFacts G s t k tr)
include hR

/-- a frame entered in the descent has no cascade: it is fruitless and ends with its raise -/
theorem no_casc_desc {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β) {e x q : Nat} (hfr : Frame tr e x) (he1 : a < e) (he2 : e ≤ β) (hqx : q < x) (hall : ∀ r, q ≤ r → r < x → isCasc tr r = true) : False := by
  obtain ⟨σ, v, h, hent⟩ := hfr.2.1
  obtain ⟨x', hfr', -, σ', o, hraise⟩ := (hR.intervalFacts hC hS).desc_call e σ v h he1 he2 hent
  rw [← hfr.exit_unique hfr'] at hraise
  have := hfr.1
  have hc := hall (x - 1) (by omega) (by omega)
  rw [Trace.not_isCasc_of_raise hraise] at hc
  cases hc

/-- the dequeues of z in an interval have pairwise distinct depths: the cascades of the interval belong to frames open at its
    start, one per depth, and a cascade dequeues z at most once -/
theorem deq_depth_unique {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β) {z : Fin n} {q₁ q₂ : Nat} (h1 : a < q₁) (h1' : q₁ ≤ c) (h2 : a < q₂) (h2' : q₂ ≤ c)
    (d1 : deqAt tr z q₁ = true) (d2 : deqAt tr z q₂ = true) (hlen : (stk tr q₁).length = (stk tr q₂).length) : q₁ = q₂ := by
  have key : ∀ q₁ q₂, q₁ < q₂ → a < q₁ → q₂ ≤ c → deqAt tr z q₁ = true → deqAt tr z q₂ = true → (stk tr q₁).length = (stk tr q₂).length → False := by
    intro q₁ q₂ hlt h1 h2' d1 d2 hlen
    have hI := hR.intervalFacts hC hS
    have hq2β : q₂ ≤ β := by
      refine Nat.le_of_not_lt fun hβ => ?_
      obtain ⟨σ, d, hd⟩ := Trace.deqAt_iff.mp d2
      exact (hI.asc_pure q₂ hβ h2').2.2 σ z d hd
    obtain ⟨e₁, x₁, σ₁, v₁, h₁, sd₁, hfr₁, he₁, hx₁, hl₁, hex₁, hall₁⟩ := hR.casc q₁ (Trace.isCasc_of_deq d1)
    -- the cascade of q₁ holds no second dequeue of z
    have hxq : x₁ < q₂ := by
      rcases Nat.lt_or_ge q₂ x₁ with h | h
      · obtain ⟨r, hr1, hr2, hr⟩ := hR.deq_once q₁ q₂ z hlt d1 d2
        rw [hall₁ r (by omega) (by omega)] at hr
        cases hr
      · rcases Nat.eq_or_lt_of_le h with h | h
        · obtain ⟨σ, d, hd⟩ := Trace.deqAt_iff.mp d2
          rw [← h, hex₁] at hd
          cases hd
        · exact h
    obtain ⟨e₂, x₂, σ₂, v₂, h₂, sd₂, hfr₂, he₂, hx₂, hl₂, -, hall₂⟩ := hR.casc q₂ (Trace.isCasc_of_deq d2)
    have hp₁ := hfr₁.push
    have hp₂ := hfr₂.push
    -- the frame of q₂ has the depth of the frame of q₁, so it is entered after that one exits, hence in the descent
    have hex : x₁ < e₂ := by
      refine Nat.lt_of_not_le fun hle => ?_
      rcases Nat.lt_trichotomy e₂ e₁ with h | h | h
      · have := (hfr₂.nest hfr₁ h (by omega)).2
        omega
      · rw [h] at hfr₂
        have := hfr₁.exit_unique hfr₂
        omega
      · have := (hfr₁.nest hfr₂ h hle).1
        omega
    exact hR.no_casc_desc hC hS hfr₂ (by omega) (by omega) hx₂ hall₂
  rcases Nat.lt_trichotomy q₁ q₂ with h | h | h
  · exact (key q₁ q₂ h h1 h2' d1 d2 hlen).elim
  · exact h
  · exact (key q₂ q₁ h h2 h1' d2 d1 hlen.symm).elim

end RunFacts

namespace AmortFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hA : AmortFacts G s t k tr)
variable (hsound : ∀ (q σ : Nat) (P : List (Fin n)), tr[q]? = some (Ev.output σ P) → G.BoundedPath k s t P)
include hA hsound

/-- in an interval, a dequeue of z and an entry of z in the descent at the same depth h exclude each other -/
theorem deq_not_desc_entry {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β) {z : Fin n} {h qd qe : Nat} (hd1 : a < qd) (hd2 : qd ≤ c) (hdq : deqAt tr z qd = true)
    (hdl : (stk tr qd).length = h + 1) (he1 : a < qe) (he2 : qe ≤ β) (heq : enterAt tr z qe = true) (hel : (stk tr qe).length = h) : False := by
  have hR := hA.toRunFacts
  have hI := hR.intervalFacts hC hS
  have hF := hR.toDelayFacts
  have hqdβ : qd ≤ β := by
    refine Nat.le_of_not_lt fun hβ => ?_
    obtain ⟨σ, d, hd⟩ := Trace.deqAt_iff.mp hdq
    exact (hI.asc_pure qd hβ hd2).2.2 σ z d hd
  obtain ⟨σe, he, hent⟩ := Trace.enterAt_iff.mp heq
  have hhe : he = h := by
    have := (hR.enter qe σe z he hent).1
    omega
  by_cases horg : (stk tr qd).getLast? = some z
  · -- z is the origin of the cascade: a spine frame at depth h, fruitful, so it contains an output P through z
    obtain ⟨e, x, σx, vx, hx, sdx, hfr, heqd, hqdx, hlen, hexit, hall⟩ := hR.casc qd (Trace.isCasc_of_deq hdq)
    have htop := hfr.top heqd (Nat.le_of_lt hqdx) hlen
    obtain ⟨σ0, v0, h0, hent0⟩ := hfr.2.1
    have hst1 := Trace.stk_succ_enter hent0
    have hv0 : v0 = z := by
      rw [htop, hst1] at horg
      simpa using horg
    rw [hv0] at hent0 hst1
    have hpush := hfr.push
    have hle : (stk tr e).length = h := by omega
    -- the entry at qe comes after z's frame: z is on the stack inside it, and a frame entered in the descent has no cascade
    have hxqe : x < qe := by
      refine Nat.lt_of_not_le fun hle' => ?_
      rcases Nat.lt_or_ge e qe with h1 | h1
      · have hz : z ∈ stk tr (e + 1) := by rw [hst1]; simp
        rw [← hfr.prefix h1 hle'] at hz
        exact (hR.enter qe σe z he hent).2.1 (List.mem_of_mem_take hz)
      · exact hR.no_casc_desc hC hS hfr (by omega) (by omega) hqdx hall
    obtain ⟨qo, σo, P, hqo1, hqo2, hout⟩ := (hR.ret e x σx vx hx sdx true hfr hexit).mp rfl
    obtain ⟨hP, -⟩ := hR.output qo σo P hout
    have hBP := hsound qo σo P hout
    have hPnd : P.Nodup := hBP.2.2.1
    have hqolen := hfr.isOpen hqo1 (Nat.le_of_lt hqo2)
    have hPz : P[h]? = some z := by
      have hpo := hfr.prefix hqo1 (Nat.le_of_lt hqo2)
      rw [hle, hst1] at hpo
      have h2 : ((stk tr qo).take (h + 1))[h]? = some z := by
        rw [hpo, ← hle]
        exact List.getElem?_concat_length
      rw [List.getElem?_take, ite_eq_left (by omega)] at h2
      rw [hP, List.getElem?_append_left (by omega)]
      exact h2
    have hzP : z ∈ P.drop h := List.mem_iff_getElem?.mpr ⟨0, by rw [List.getElem?_drop, Nat.add_zero]; exact hPz⟩
    -- the stack right after the entry at qe, with z on top at index h
    have hS1 : stk tr (qe + 1) = stk tr qe ++ [z] := Trace.stk_succ_enter hent
    have hSz : (stk tr (qe + 1))[h]? = some z := by
      rw [hS1, ← hel]
      exact List.getElem?_concat_length
    have hSnd := hR.stk_nodup (qe + 1)
    -- the lowest node u of that stack that lies on P from z on, at index du
    obtain ⟨du, ⟨u, hu, huP⟩, hmin⟩ := Trace.exists_min (P := fun d => ∃ w, (stk tr (qe + 1))[d]? = some w ∧ w ∈ P.drop h) (fun d => d) h ⟨z, hSz, hzP⟩
    have hmin' : ∀ d', (∃ w, (stk tr (qe + 1))[d']? = some w ∧ w ∈ P.drop h) → du ≤ d' := hmin
    have hduh : du ≤ h := hmin' h ⟨z, hSz, hzP⟩
    obtain ⟨eu, xu, σu, hu', hfru, heu1, heu2, hentu⟩ := hA.frame_of_mem (List.mem_of_getElem? hu)
    have hpu := hfru.prefix heu1 heu2
    have hst1u := Trace.stk_succ_enter hentu
    have hulen := hfru.isOpen heu1 heu2
    have hidx : (stk tr (qe + 1))[(stk tr eu).length]? = some u := by
      have h2 : ((stk tr (qe + 1)).take ((stk tr eu).length + 1))[(stk tr eu).length]? = some u := by
        rw [hpu, hst1u]
        exact List.getElem?_concat_length
      rwa [List.getElem?_take, ite_eq_left (by omega)] at h2
    have hdu : (stk tr eu).length = du := hSnd.eq_of_getElem?_eq (by omega) (by rw [hidx, hu])
    -- u's frame is entered after z's frame exits
    have hxeu : x < eu := by
      rcases Nat.eq_or_lt_of_le hduh with hdh | hdh
      · -- u = z, and its frame is the call entered at qe
        rw [hdh, hSz] at hu
        have huz : u = z := (Option.some.inj hu).symm
        rw [huz] at hentu
        obtain ⟨xe, hfre⟩ := hR.frame qe σe z he hent
        have := Trace.Frame.eq_of_node hSnd hfru hfre hentu hent heu1 heu2 (Nat.lt_succ_self qe) hfre.1
        omega
      · refine Nat.lt_of_not_le fun hle' => ?_
        rcases Nat.lt_or_ge eu qo with h1 | h1
        · -- u's frame contains qo, so u = P[du]; but u lies on P from index h on, and du < h
          have hpo := hfru.prefix h1 (by omega)
          have hqolen' := hfru.isOpen h1 (by omega)
          have h2 : ((stk tr qo).take ((stk tr eu).length + 1))[(stk tr eu).length]? = some u := by
            rw [hpo, hst1u]
            exact List.getElem?_concat_length
          rw [List.getElem?_take, ite_eq_left (by omega)] at h2
          have hPu : P[du]? = some u := by
            rw [hP, List.getElem?_append_left (by omega), ← hdu]
            exact h2
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp huP
          rw [List.getElem?_drop] at hj
          have := hPnd.eq_of_getElem?_eq (by rw [hP, List.length_append, List.length_singleton]; omega) (hPu.trans hj.symm)
          omega
        · -- u's frame would lie inside z's frame, but it is still open at qe + 1
          have := (hfr.nest hfru (by omega) hle').1
          omega
    -- so u's frame is entered in the descent
    have haeu : a < eu := by omega
    have heuβ : eu ≤ β := by omega
    obtain ⟨xe', hfre', hxe'β, -⟩ := hI.desc_call eu σu u hu' haeu heuβ hentu
    have hxu : xu ≤ β := by
      rw [hfru.exit_unique hfre']
      exact hxe'β
    -- its search path, followed by P from u on, is a bounded path
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp huP
    rw [List.getElem?_drop] at hj
    obtain ⟨hiu, hPj⟩ := List.getElem?_eq_some_iff.mp hj
    have hdrop : P.drop (h + j) = u :: P.drop (h + j + 1) := by
      rw [List.drop_eq_getElem_cons hiu, hPj]
    obtain ⟨-, -, -, -, -, hhead, hedges⟩ := hR.enter eu σu u hu' hentu
    have hpre : stk tr (eu + 1) <+: stk tr eu ++ P.drop (h + j) := by
      rw [hst1u, hdrop]
      exact ⟨P.drop (h + j + 1), by simp⟩
    have hBp : G.BoundedPath k s t (stk tr eu ++ P.drop (h + j)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hdrop]
        rw [List.head?_append] at hhead ⊢
        cases hse : (stk tr eu).head? <;> simp_all
      · rw [List.getLast?_append, List.getLast?_drop, ite_eq_right (by omega), hBP.2.1]
        rfl
      · refine List.nodup_append.mpr ⟨hR.stk_nodup eu, hPnd.sublist (List.drop_sublist _ _), ?_⟩
        intro w hw w' hw' hww
        rw [← hww] at hw'
        -- w lies below u on the stack at qe + 1, at an index < du, and on P from z on: against the choice of u
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
        have hilt : i < (stk tr eu).length := (List.getElem?_eq_some_iff.mp hi).1
        have hSi : (stk tr (qe + 1))[i]? = some w := by
          have h2 : ((stk tr (qe + 1)).take ((stk tr eu).length + 1))[i]? = some w := by
            rw [hpu, hst1u, List.getElem?_append_left hilt]
            exact hi
          rwa [List.getElem?_take, ite_eq_left (by omega)] at h2
        have hwP : w ∈ P.drop h := by
          have hsub : P.drop (h + j) ⊆ P.drop h := by
            rw [← List.drop_drop]
            exact (List.drop_sublist _ _).subset
          exact hsub hw'
        have := hmin' i ⟨w, hSi, hwP⟩
        omega
      · have := hBP.2.2.2.1
        simp only [List.length_append, List.length_drop]
        omega
      · apply (Graph.edges_iff_zip G _).mp
        rw [hdrop]
        refine Graph.Edges.append_cons hedges ?_
        rw [← hdrop]
        have hPe : G.Edges P := (Graph.edges_iff_zip G P).mpr hBP.2.2.2.2
        rw [← List.take_append_drop (h + j) P] at hPe
        exact hPe.of_append_right
    -- by Call Completeness u's call outputs it, inside the descent: impossible
    obtain ⟨q', σ', hq'1, hq'2, hout'⟩ := hR.complete eu xu hfru _ hBp hpre
    have hb := hC.between q' (by omega) (by have := hS.lt; omega)
    rw [Trace.isObs_of_output hout'] at hb
    cases hb
  · -- z was dropped at θ in the same cascade, whose origin is at depth h: Descent Split
    obtain ⟨θ, hθ, hdrop, hcasc⟩ := hR.deq_drop qd z hdq horg
    have haθ : a < θ := by
      refine Nat.lt_of_not_le fun hle => ?_
      have hc := hcasc a hle (by omega)
      rw [Trace.not_isCasc_of_obs hC.obs_a] at hc
      cases hc
    have hstk : stk tr qd = stk tr θ := by
      have := Trace.stk_eq_of_casc (tr := tr) (p := θ) (qd - θ) (fun r h1 h2 => hcasc r h1 (by omega))
      rwa [show θ + (qd - θ) = qd by omega] at this
    have := hF.descent_split hC hS haθ (by omega) hdrop he1 he2 hent (Or.inl rfl)
    rw [← hstk] at this
    omega

/-- Two Visits per Pair: between consecutive observable events a < c, every node z is visited (entered or dequeued) at most twice
    at the same depth h -/
theorem two_visits {a c : Nat} (hC : Consec tr a c) (z : Fin n) (h : Nat) : cnt (fun q => visitAt tr z h q = true) a c ≤ 2 := by
  have hR := hA.toRunFacts
  obtain ⟨m, β, hS⟩ := shape_exists hC
  have hI := hR.intervalFacts hC hS
  -- the depth of a visit, read off the stack before it
  have hv : ∀ q, visitAt tr z h q = true → (enterAt tr z q = true ∧ (stk tr q).length = h) ∨ (deqAt tr z q = true ∧ (stk tr q).length = h + 1) := by
    intro q hq
    simp only [visitAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hq
    obtain ⟨he | hd, hl⟩ := hq
    · obtain ⟨σ, hh, hent⟩ := Trace.enterAt_iff.mp he
      rw [Trace.stk_succ_enter hent, List.length_append, List.length_singleton] at hl
      exact Or.inl ⟨he, by omega⟩
    · rw [Trace.stk_succ_deq hd] at hl
      exact Or.inr ⟨hd, hl⟩
  -- two entries at depth h in the same phase are one
  have hent2 : ∀ q₁ q₂, enterAt tr z q₁ = true → (stk tr q₁).length = h → enterAt tr z q₂ = true → (stk tr q₂).length = h →
      ((a < q₁ ∧ q₁ ≤ β ∧ a < q₂ ∧ q₂ ≤ β) ∨ (β < q₁ ∧ q₁ ≤ c ∧ β < q₂ ∧ q₂ ≤ c)) → q₁ = q₂ := by
    intro q₁ q₂ e₁ l₁ e₂ l₂ hph
    obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp e₁
    obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp e₂
    have d₁ := (hR.enter q₁ σ₁ z h₁ he₁).1
    have d₂ := (hR.enter q₂ σ₂ z h₂ he₂).1
    rw [show h₁ = h by omega] at he₁
    rw [show h₂ = h by omega] at he₂
    exact Decidable.byContradiction fun hne => hI.one_entry q₁ q₂ σ₁ σ₂ z h hne hph he₁ he₂
  -- the descent: at most one visit at depth h
  have hd := Trace.cnt_le_one (fun q => visitAt tr z h q = true) (lo := a) (hi := β) fun q₁ q₂ a1 b1 a2 b2 p1 p2 => by
    have := hS.lt
    rcases hv q₁ p1 with ⟨e₁, l₁⟩ | ⟨d₁, l₁⟩ <;> rcases hv q₂ p2 with ⟨e₂, l₂⟩ | ⟨d₂, l₂⟩
    · exact hent2 q₁ q₂ e₁ l₁ e₂ l₂ (Or.inl ⟨a1, b1, a2, b2⟩)
    · exact (hA.deq_not_desc_entry hsound hC hS a2 (by omega) d₂ l₂ a1 b1 e₁ l₁).elim
    · exact (hA.deq_not_desc_entry hsound hC hS a1 (by omega) d₁ l₁ a2 b2 e₂ l₂).elim
    · exact hR.deq_depth_unique hC hS a1 (by omega) a2 (by omega) d₁ d₂ (by omega)
  -- the ascent: no dequeues, at most one entry at depth h
  have ha := Trace.cnt_le_one (fun q => visitAt tr z h q = true) (lo := β) (hi := c) fun q₁ q₂ a1 b1 a2 b2 p1 p2 => by
    have nodeq : ∀ q, β < q → q ≤ c → deqAt tr z q = true → False := fun q h1 h2 hdq => by
      obtain ⟨σ, d, hd⟩ := Trace.deqAt_iff.mp hdq
      exact (hI.asc_pure q h1 h2).2.2 σ z d hd
    rcases hv q₁ p1 with ⟨e₁, l₁⟩ | ⟨d₁, -⟩
    · rcases hv q₂ p2 with ⟨e₂, l₂⟩ | ⟨d₂, -⟩
      · exact hent2 q₁ q₂ e₁ l₁ e₂ l₂ (Or.inr ⟨a1, b1, a2, b2⟩)
      · exact (nodeq q₂ a2 b2 d₂).elim
    · exact (nodeq q₁ a1 b1 d₁).elim
  rw [Trace.cnt_split _ hS.le (Nat.le_of_lt hS.lt)]
  omega

end AmortFacts

variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- Two Visits per Pair for the run of `bsdfs`: between consecutive observable events a < c, every node z is visited at most twice
    at each depth h; a visit is an entry or a dequeue, and its depth is that of the search right after it (the new frame's for an
    entry, the cascade origin's for a dequeue) -/
theorem bsdfs_two_visits (hG : G.WF) (hst : s ≠ t) {a c : Nat} (hC : Consec (bsdfs G s t k) a c) (z : Fin n) (h : Nat) :
    cnt (fun q => visitAt (bsdfs G s t k) z h q = true) a c ≤ 2 :=
  (bsdfs_amortFacts G s t k hG hst).two_visits (fun _ _ P hq => bsdfs_sound G s t k hst P (Trace.mem_outputs hq)) hC z h
