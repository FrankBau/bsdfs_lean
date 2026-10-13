import Bsdfs.WorstCase

/-!
  The amortized delay of BS-DFS (v3, thm:amortized): the τ-th observable event happens after at most τ(k+2)(n+m) steps.
  Period τ is (β_{τ-1}, β_τ], the ascent of interval τ-1 followed by the descent of interval τ.  Per period every node and every
  edge is scanned at most k + 2 times (Period Budget): of the calls entered in the period at most one per node is still open at
  the output o_τ; the others are fruitless, return within the period, and their raises form one chain, so they have pairwise
  distinct depths, which Period Split confines to [i + 1, k] when the node, or a successor, is dropped first by an origin at
  depth i; the dequeues number at most i + 1.  Summing over the periods before o_τ, plus the ascent τ, gives the bound.
-/

open Std.Do Trace

set_option mvcgen.warning false

variable {n : Nat}

/-! ## Generic lemmas -/

section generic

/-- the cost of (lo, hi] splits at mid -/
theorem lsum_range'_split (f : Nat → Nat) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) : lsum (List.range' (lo + 1) (hi - lo)) f = lsum (List.range' (lo + 1) (mid - lo)) f + lsum (List.range' (mid + 1) (hi - mid)) f := by
  have e : List.range' (lo + 1) (mid - lo) ++ List.range' (mid + 1) (hi - mid) = List.range' (lo + 1) (hi - lo) := by
    have := @List.range'_append (lo + 1) (mid - lo) (hi - mid) 1
    rw [Nat.one_mul, show lo + 1 + (mid - lo) = mid + 1 by omega, show mid - lo + (hi - mid) = hi - lo by omega] at this
    exact this
  rw [← e, lsum_append]

/-- bounds on the values of filterMap, from bounds at the positions: the τ-th value is at most (off + τ) * C -/
theorem filterMap_le {β : Type} (f : β → Option Nat) (C : Nat) : ∀ (l : List β) (off : Nat), (∀ p x σ, l[p]? = some x → f x = some σ → σ ≤ (off + (l.take p).countP (fun y => (f y).isSome)) * C) → ∀ τ σ, (l.filterMap f)[τ]? = some σ → σ ≤ (off + τ) * C
  | [], _, _, τ, σ, h => by simp at h
  | x :: l, off, hpos, τ, σ, h => by
    cases hx : f x with
    | none =>
      rw [List.filterMap_cons_none hx] at h
      refine filterMap_le f C l off (fun p y σ' hy hfy => ?_) τ σ h
      have := hpos (p + 1) y σ' (by simpa using hy) hfy
      simpa [List.take_succ_cons, List.countP_cons, hx] using this
    | some σ0 =>
      rw [List.filterMap_cons_some hx] at h
      cases τ with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        have := hpos 0 x σ0 (by simp) hx
        simpa using this
      | succ τ =>
        simp only [List.getElem?_cons_succ] at h
        have := filterMap_le f C l (off + 1) (fun p y σ' hy hfy => by
          have := hpos (p + 1) y σ' (by simpa using hy) hfy
          simp only [List.take_succ_cons, List.countP_cons, hx, Option.isSome_some, ↓reduceIte] at this
          rw [show off + 1 + (l.take p).countP (fun y => (f y).isSome) = off + ((l.take p).countP (fun y => (f y).isSome) + 1) by omega]
          exact this) τ σ h
        rw [show off + (τ + 1) = off + 1 + τ by omega]
        exact this

/-- number of observable events before position p -/
def obsBefore (tr : List (Ev n)) (p : Nat) : Nat := (tr.take p).countP (fun e => e.obs.isSome)

theorem obsBefore_succ (tr : List (Ev n)) (p : Nat) : obsBefore tr (p + 1) = obsBefore tr p + (if isObs tr p then 1 else 0) := by
  unfold obsBefore isObs
  rw [List.take_add_one, List.countP_append]
  cases tr[p]? <;> simp

theorem obsBefore_consec {tr : List (Ev n)} {a c : Nat} (hC : Consec tr a c) : obsBefore tr c = obsBefore tr a + 1 := by
  have key : ∀ j, a + 1 + j ≤ c → obsBefore tr (a + 1 + j) = obsBefore tr a + 1 := by
    intro j
    induction j with
    | zero => intro _; rw [Nat.add_zero, obsBefore_succ, hC.obs_a]; rfl
    | succ j ih =>
      intro hj
      rw [show a + 1 + (j + 1) = (a + 1 + j) + 1 by omega, obsBefore_succ, ih (by omega), hC.between (a + 1 + j) (by omega) (by omega)]
      rfl
  have := key (c - a - 1) (by have := hC.lt; omega)
  rwa [show a + 1 + (c - a - 1) = c by have := hC.lt; omega] at this

/-- from budgets per node and per edge, and the output, to the cost of the positions (lo, hi] -/
theorem cost_le_of_budget {G : Graph n} {t : Fin n} {tr : List (Ev n)} (hG : G.WF) {lo hi B : Nat}
    (hnode : ∀ z, z ≠ t → cnt (fun q => enterAt tr z q = true) lo hi + cnt (fun q => deqAt tr z q = true) lo hi ≤ B)
    (ht : cnt (fun q => enterAt tr t q = true) lo hi + cnt (fun q => deqAt tr t q = true) lo hi = 0)
    (hedge : ∀ x y, y ∈ G.succ x → cnt (fun q => enterAt tr x q = true) lo hi + cnt (fun q => deqAt tr y q = true) lo hi ≤ B)
    (hout : lsum (List.range' (lo + 1) (hi - lo)) (outCost tr) ≤ B) :
    lsum (List.range' (lo + 1) (hi - lo)) (posCost G tr) ≤ B * (n + G.m) := by
  rw [lsum_posCost G tr lo hi]
  have hE : nsum (fun z => (1 + (G.succ z).length) * cnt (fun q => enterAt tr z q = true) lo hi) = nsum (fun z => cnt (fun q => enterAt tr z q = true) lo hi) + nsum (fun x => lsum (G.succ x) (fun _ => cnt (fun q => enterAt tr x q = true) lo hi)) := by
    rw [← lsum_add]; congr 1; funext z; rw [lsum_const, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  have hD : nsum (fun z => (1 + (G.pred z).length) * cnt (fun q => deqAt tr z q = true) lo hi) = nsum (fun z => cnt (fun q => deqAt tr z q = true) lo hi) + nsum (fun x => lsum (G.succ x) (fun y => cnt (fun q => deqAt tr y q = true) lo hi)) := by
    rw [← pred_sum G hG, ← lsum_add]; congr 1; funext z; rw [Nat.add_mul, Nat.one_mul]
  have hnode' : nsum (fun z => cnt (fun q => enterAt tr z q = true) lo hi) + nsum (fun z => cnt (fun q => deqAt tr z q = true) lo hi) ≤ nsum (fun z => if z = t then 0 else B) := by
    rw [← lsum_add]
    apply lsum_le
    intro z _
    by_cases hzt : z = t
    · subst hzt; simp only [↓reduceIte]; omega
    · simp only [hzt, ↓reduceIte]; exact hnode z hzt
  have hedge' : nsum (fun x => lsum (G.succ x) (fun _ => cnt (fun q => enterAt tr x q = true) lo hi)) + nsum (fun x => lsum (G.succ x) (fun y => cnt (fun q => deqAt tr y q = true) lo hi)) ≤ B * G.m := by
    rw [← lsum_add]
    have : nsum (fun x => lsum (G.succ x) (fun _ => B)) = B * G.m := by
      rw [show (fun x => lsum (G.succ x) (fun _ => B)) = (fun x => B * (G.succ x).length) from funext fun x => lsum_const _ _]
      exact lsum_mul _ _ _
    rw [← this]
    apply lsum_le
    intro x _
    rw [← lsum_add]
    apply lsum_le
    intro y hy
    exact hedge x y hy
  have hn := nsum_ite_ne t B
  rw [hE, hD]
  have : B * (n + G.m) = B * n + B * G.m := Nat.mul_add _ _ _
  omega

/-- the outputs in (lo, hi] cost at most k + 1 if at most one observable event lies there -/
theorem out_le_of_one {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hR : RunFacts G s t k tr) {lo hi p : Nat} (hone : ∀ q, lo < q → q ≤ hi → q ≠ p → isObs tr q = false) :
    lsum (List.range' (lo + 1) (hi - lo)) (outCost tr) ≤ k + 1 := by
  have hq : ∀ q, outCost tr q ≤ k + 1 := by
    intro q
    unfold outCost
    cases hq : tr[q]? with
    | none => simp
    | some e => cases e with
      | output σ P =>
        obtain ⟨hP, hlen⟩ := hR.output q σ P hq
        simp only
        rw [hP]; simp; omega
      | _ => simp
  have h1 : ∀ q ∈ List.range' (lo + 1) (hi - lo), outCost tr q ≤ (if q = p then k + 1 else 0) := by
    intro q hq'
    simp only [List.mem_range'_1] at hq'
    by_cases hqp : q = p
    · simp only [hqp, ↓reduceIte]; exact hq p
    · simp only [hqp, ↓reduceIte]
      have hobs := hone q (by omega) (by omega) hqp
      unfold outCost
      cases hq'' : tr[q]? with
      | none => simp
      | some e => cases e with
        | output σ P => simp [isObs, hq'', Ev.obs] at hobs
        | _ => simp
  refine Nat.le_trans (lsum_le h1) ?_
  by_cases hp : p ∈ List.range' (lo + 1) (hi - lo)
  · exact Nat.le_of_eq (lsum_ite_eq (List.nodup_range' (step := 1)) hp (fun _ => k + 1))
  · rw [lsum_ite_eq_zero hp]; omega

end generic

/-! ## The run with its root call -/

/-- the run facts plus the frame of the run: the start event, the root call, and the term event right after its exit -/
structure AmortFacts (G : Graph n) (s t : Fin n) (k : Nat) (tr : List (Ev n)) : Prop extends RunFacts G s t k tr where
  start : ∃ σ, tr[0]? = some (.start σ)
  root : ∃ x σ, Frame tr 1 x ∧ tr[x + 1]? = some (.term σ) ∧ tr.length = x + 2

/-- the call entered at q is still open at a -/
def openAt (tr : List (Ev n)) (a q : Nat) : Prop := q < a ∧ ∃ x, Frame tr q x ∧ a < x

namespace AmortFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hA : AmortFacts G s t k tr)
include hA

theorem stk_one : stk tr 1 = [] := by
  obtain ⟨σ, h⟩ := hA.start
  rw [show (1 : Nat) = 0 + 1 from rfl, Trace.stk_succ, h]; rfl

theorem isObs_zero : isObs tr 0 = true := by
  obtain ⟨σ, h⟩ := hA.start
  simp [isObs, h, Ev.obs]

/-- the root call is open at every observable event before the last one -/
theorem root_open {a c : Nat} (hC : Consec tr a c) (h1 : 1 < a) : openAt tr a 1 := by
  obtain ⟨x, σ, hfr, hterm, hlen⟩ := hA.root
  refine ⟨h1, x, hfr, ?_⟩
  have hb := hC.bound
  have hac := hC.lt
  rcases Nat.lt_trichotomy a x with h | h | h
  · exact h
  · subst h
    obtain ⟨σx, v, hh, sd, f, hx⟩ := hfr.2.2.1
    have := hC.obs_a
    simp [isObs, hx, Ev.obs] at this
  · omega

/-- a node on the stack at r belongs to a frame open at r -/
theorem frame_of_mem {r : Nat} {z : Fin n} (hz : z ∈ stk tr r) : ∃ e x σ h, Frame tr e x ∧ e < r ∧ r ≤ x ∧ tr[e]? = some (.enter σ z h) := by
  have hR := hA.toRunFacts
  obtain ⟨q₀, -, hq₀r, hq₀⟩ := Trace.exists_enter_of_mem (p₁ := 0) (Nat.zero_le r) (by simp [stk]) hz
  obtain ⟨e, he1, he2, hee, hlast⟩ := Trace.exists_last (P := fun q => enterAt tr z q = true) (hi := r - 1) q₀ (by omega) hq₀
  obtain ⟨σ, h, hent⟩ := Trace.enterAt_iff.mp hee
  obtain ⟨x, hfr⟩ := hR.frame e σ z h hent
  refine ⟨e, x, σ, h, hfr, by omega, ?_, hent⟩
  refine Nat.le_of_not_lt fun hxr => ?_
  -- after the exit z is off the stack and not entered again before r
  have hoff : z ∉ stk tr (x + 1) := by
    obtain ⟨σx, vx, hx, sdx, fx, hex⟩ := hfr.2.2.1
    rw [Trace.stk_succ_exit hex, hfr.at_exit, Trace.stk_succ_enter hent, List.dropLast_concat]
    exact (hR.enter e σ z h hent).2.1
  exact Trace.not_mem_stk_of_no_enter (p₁ := x + 1) (by omega) hoff (fun q hq1 hq2 => by
    cases hq : enterAt tr z q
    · rfl
    · exact absurd hq (hlast q (by have := hfr.1; omega) (by omega))) hz

end AmortFacts

/-! ## One period -/

namespace AmortFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hA : AmortFacts G s t k tr)
include hA

theorem deqAt_t (q : Nat) : deqAt tr t q = false := by
  have hR := hA.toRunFacts
  have hF := hR.toDelayFacts
  cases hd : deqAt tr t q
  · rfl
  · by_cases htop : (stk tr q).getLast? = some t
    · exact absurd (List.mem_of_getLast? htop) (hF.t_not_mem q)
    · obtain ⟨q', -, hq', -⟩ := hR.deq_drop q t hd htop
      rw [hF.dropAt_t] at hq'; cases hq'

section period
variable {a' a c m' β' m β : Nat} (hC' : Consec tr a' a) (hC : Consec tr a c) (hS' : Shape tr a' a m' β') (hS : Shape tr a c m β)
include hC' hC hS' hS

omit hA in
theorem no_obs {q : Nat} (h1 : β' < q) (h2 : q ≤ β) (hq : q ≠ a) : isObs tr q = false := by
  rcases Nat.lt_or_gt_of_ne hq with h | h
  · exact hC'.between q (by have := hS'.le; omega) h
  · exact hC.between q h (by have := hS.lt; omega)

omit hC hS in
theorem no_drop_asc {q : Nat} {y : Fin n} (h1 : β' < q) (h2 : q ≤ a) : dropAt tr y q = false := by
  cases hd : dropAt tr y q
  · rfl
  · exact (hA.toRunFacts.asc_pure hC' hS' h1 h2 (Trace.isCasc_of_drop hd)).elim

omit hC hS in
theorem no_deq_asc {q : Nat} {y : Fin n} (h1 : β' < q) (h2 : q ≤ a) : deqAt tr y q = false := by
  cases hd : deqAt tr y q
  · rfl
  · exact (hA.toRunFacts.asc_pure hC' hS' h1 h2 (Trace.isCasc_of_deq hd)).elim

omit hC hS in
/-- a frame exiting in the ascent (β', a) is fruitless: one open at a' would be open at β' + 1 at depth ≥ m' -/
theorem asc_exit_fruitless {e x σ : Nat} {v : Fin n} {h sd : Nat} {f : Bool} (hfr : Frame tr e x) (h1 : β' < x) (h2 : x < a) (hx : tr[x]? = some (.exit σ v h sd f)) : f = false := by
  have hR := hA.toRunFacts
  rcases Nat.lt_trichotomy e a' with he | he | he
  · exfalso
    have h3 := hfr.isOpen (q := β' + 1) (by have := hS'.le; omega) (by omega)
    have h4 := hfr.2.2.2.1
    have h5 := hS'.min (x + 1) (by have := hS'.le; omega) (by omega)
    have h6 := hS'.at_beta
    omega
  · obtain ⟨σe, ve, hh, hee⟩ := hfr.2.1
    have := hC'.obs_a
    rw [← he] at this
    simp [isObs, hee, Ev.obs] at this
  · cases hf : f
    · rfl
    · obtain ⟨o, σo, P, ho1, ho2, ho⟩ := (hR.ret e x σ v h sd f hfr hx).mp hf
      have := hC'.between o (by omega) (by omega)
      rw [Trace.isObs_of_output ho] at this; cases this

/-- a call entered in the period and not open at a is fruitless: it returns within its phase, with its raise -/
theorem nR_raise {q σ : Nat} {z : Fin n} {h : Nat} (h1 : β' < q) (h2 : q ≤ β) (he : tr[q]? = some (.enter σ z h)) (hno : ¬ openAt tr a q) :
    ∃ x, Frame tr q x ∧ (q < a → x < a) ∧ (a < q → x ≤ β) ∧ ∃ σ' o, tr[x - 1]? = some (.write σ' z o (k + 1 - h) .raise) := by
  have hR := hA.toRunFacts
  rcases Nat.lt_trichotomy q a with hq | hq | hq
  · obtain ⟨x, hfr⟩ := hR.frame q σ z h he
    have hxa : x < a := by
      refine Nat.lt_of_not_le fun hle => ?_
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · obtain ⟨σx, v, hh, sd, f, hx⟩ := hfr.2.2.1
        have := hC'.obs_c
        rw [heq] at this
        simp [isObs, hx, Ev.obs] at this
      · exact hno ⟨hq, x, hfr, hlt⟩
    obtain ⟨σx, vx, hx, sdx, fx, hex⟩ := hfr.2.2.1
    have hf := hA.asc_exit_fruitless hC' hS' hfr (by have := hfr.1; omega) hxa hex
    subst hf
    exact ⟨x, hfr, fun _ => hxa, fun h' => absurd h' (by omega), hR.fruitless_end q x σ z h σx vx hx sdx hfr he hex⟩
  · have := hC.obs_a
    rw [← hq] at this
    simp [isObs, he, Ev.obs] at this
  · obtain ⟨x, hfr, hxβ, hraise⟩ := hR.desc_call hC hS hq h2 he
    exact ⟨x, hfr, fun h' => absurd h' (by omega), fun _ => hxβ, hraise⟩

omit hC' hC hS' hS in
open Classical in
/-- at most one call per node entered in the period is still open at a -/
theorem R_le_one (z : Fin n) : cnt (fun q => enterAt tr z q = true ∧ openAt tr a q) β' β ≤ 1 := by
  apply Trace.cnt_le_one
  intro q₁ q₂ a1 b1 a2 b2 ⟨he1, hr1⟩ ⟨he2, hr2⟩
  obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp he1
  obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp he2
  obtain ⟨hq1, x₁, hf₁, hx₁⟩ := hr1
  obtain ⟨hq2, x₂, hf₂, hx₂⟩ := hr2
  exact Trace.Frame.eq_of_node (q := a) (hA.toRunFacts.stk_nodup a) hf₁ hf₂ he₁ he₂ hq1 (by omega) hq2 (by omega)

/-- Period chain: two calls at z entered in the period at the same depth, the first not open at a, are impossible: the first
    raises b[z] to k + 1 - h, the second needs b[z] ≤ k - h, and the drop in between would violate Descent Seal -/
theorem nR_inj {q₁ q₂ σ₁ σ₂ : Nat} {z : Fin n} {h : Nat} (h1 : β' < q₁) (hlt : q₁ < q₂) (h2 : q₂ ≤ β) (he₁ : tr[q₁]? = some (.enter σ₁ z h)) (he₂ : tr[q₂]? = some (.enter σ₂ z h)) (hno : ¬ openAt tr a q₁) : False := by
  have hR := hA.toRunFacts
  obtain ⟨x₁, hfr, -, -, σr, o, hraise⟩ := hA.nR_raise hC' hC hS' hS h1 (by omega) he₁ hno
  have hq₁x₁ := hfr.1
  -- z stays on the stack while its frame is open, so the frame exits before q₂
  have hx₁ : x₁ < q₂ := by
    refine Nat.lt_of_not_le fun hle => ?_
    have hp := hfr.prefix hlt hle
    rw [Trace.stk_succ_enter he₁] at hp
    have hz : z ∈ (stk tr q₂).take ((stk tr q₁).length + 1) := by rw [hp]; simp
    exact (hR.enter q₂ σ₂ z h he₂).2.1 (List.mem_of_mem_take hz)
  obtain ⟨σx, vx, hx, sdx, fx, hex⟩ := hfr.2.2.1
  have hbx : bar tr (x₁ + 1) z = k + 1 - h := by
    have hb := Trace.bar_succ_of_write hraise
    rw [show x₁ - 1 + 1 = x₁ by omega] at hb
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
  have hθa : a < θ := by
    refine Nat.lt_of_not_le fun hle => ?_
    rw [hA.no_drop_asc hC' hS' (by omega) hle] at hd; cases hd
  exact hR.seal_enter hC hS (q := q₂) (by omega) h2 he₂ (θ := θ) hθa hθ2 hd

omit hS' hS in
/-- a call entered in the period and not open at a has depth ≥ 1: the root call is open at a -/
theorem nR_depth_pos {q σ : Nat} {z : Fin n} {h : Nat} (h1 : β' < q) (h2 : q ≤ β) (he : tr[q]? = some (.enter σ z h)) (hno : ¬ openAt tr a q) : 1 ≤ h := by
  refine Nat.pos_of_ne_zero fun h0 => hno ?_
  have hq := (hA.toRunFacts.enter q σ z h he).2.2.2.2.1 h0
  subst hq
  have h1a : 1 < a := by
    rcases Nat.lt_trichotomy 1 a with h' | h' | h'
    · exact h'
    · exfalso
      have := hC.obs_a
      rw [← h'] at this
      simp [isObs, he, Ev.obs] at this
    · have := hC'.lt; omega
  exact hA.root_open hC h1a

/-- Period Split (lem:period-split): if y is dropped first at θ in the descent, every call at y, or at a predecessor of y,
    entered in the period and not open at a has depth ≥ |S_θ|.  Calls of the descent: Descent Split.  Calls of the ascent
    nested in the origin's frame: by depth.  Calls of the ascent before the origin's entry e₀: they bring b[y] to ≥ k - h
    before e₀ (raise at y, a fruitless child at y, the guard, or a fruitless frame of y on the stack), b[y] does not decrease
    up to e₀, and b[y] at e₀ is at most the drop value (Per-Call Global Monotonicity) -/
theorem period_split {θ : Nat} {y : Fin n} (hθ1 : a < θ) (hθ2 : θ ≤ β) (hd : dropAt tr y θ = true) (hfirst : ∀ q, a < q → q < θ → dropAt tr y q = false)
    {q σ : Nat} {u : Fin n} {h : Nat} (hq1 : β' < q) (hq2 : q ≤ β) (he : tr[q]? = some (.enter σ u h)) (hu : u = y ∨ y ∈ G.succ u) (hno : ¬ openAt tr a q) : (stk tr θ).length ≤ h := by
  have hR := hA.toRunFacts
  have hF := hR.toDelayFacts
  rcases Nat.lt_or_ge a q with hqa | hqa
  · exact hF.descent_split hC hS hθ1 hθ2 hd hqa hq2 he hu
  have hqa' : q < a := by
    rcases Nat.eq_or_lt_of_le hqa with h' | h'
    · exfalso
      have := hC.obs_a
      rw [← h'] at this
      simp [isObs, he, Ev.obs] at this
    · exact h'
  obtain ⟨σd, o, nw, hdw⟩ := Trace.dropAt_iff.mp hd
  -- the origin frame (e₀, x₀) of the drop's cascade, open since a
  obtain ⟨e₀, x₀, σ₀, v₀, h₀, sd₀, hf₀, he₀θ, hθx₀, hlen₀, hex₀, hall₀, he₀a⟩ := hR.casc_open (a := a) (Trace.isCasc_of_drop hd) (fun r h1' h2' => hC.between r h1' (by have := hS.lt; omega))
  have hpush₀ := hf₀.push
  have hhq := (hR.enter q σ u h he).1
  have hguard := (hR.enter q σ u h he).2.2.2.1
  rcases Nat.lt_trichotomy e₀ q with h' | h' | h'
  · -- nested in the origin's frame
    have := hf₀.isOpen (q := q) h' (by omega)
    omega
  · -- the origin's frame itself, open at a
    subst h'
    exact absurd ⟨hqa', x₀, hf₀, by omega⟩ hno
  -- before the origin's entry: the call returns before e₀
  obtain ⟨x, hfr, hxa, -, σr, or, hraise⟩ := hA.nR_raise hC' hC hS' hS hq1 hq2 he hno
  have hxa' := hxa hqa'
  have hqx := hfr.1
  have hxe₀ : x < e₀ := by
    refine Nat.lt_of_not_le fun hle => ?_
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · obtain ⟨σx, vx, hx', sdx, fx, hex'⟩ := hfr.2.2.1
      obtain ⟨σe, ve, he', hee⟩ := hf₀.2.1
      rw [heq, hex'] at hee; cases hee
    · have := (hfr.nest hf₀ h' (by omega)).1
      exact hno ⟨hqa', x, hfr, by omega⟩
  -- b[y] at e₀ is at most the drop value
  have hbe₀ : bar tr e₀ y ≤ nw := by
    have hm := hR.mono e₀ x₀ hf₀ y
    have hexit : bar tr (x₀ + 1) y = nw := by
      rw [Trace.not_write_of_exit hex₀, Trace.bar_eq_of_no_write (p₁ := θ + 1) (by omega) (fun r σ' o' nw' kd' h1 h2 hw => hR.drop_last θ y hd r σ' o' nw' kd' (by omega) (fun r' hr1 hr2 => hall₀ r' hr1 (by omega)) hw), Trace.bar_succ_of_write hdw]
    omega
  have hdepth := hF.drop_depth hdw
  -- a fruitless frame of y exiting in (β', e₀) leaves b[y] ≥ k + 1 - its depth
  have hframe_y : ∀ e' x' σ' h', Frame tr e' x' → tr[e']? = some (.enter σ' y h') → β' < x' → x' < e₀ → bar tr x' y = k + 1 - h' := by
    intro e' x' σ' h' hf' he' h1 h2
    obtain ⟨σx', vx', hx'', sdx', fx', hex''⟩ := hf'.2.2.1
    have hf := hA.asc_exit_fruitless hC' hS' hf' h1 (by omega) hex''
    subst hf
    obtain ⟨σw, ow, hw⟩ := hR.fruitless_end e' x' σ' y h' σx' vx' hx'' sdx' hf' he' hex''
    have hb := Trace.bar_succ_of_write hw
    rwa [show x' - 1 + 1 = x' by have := hf'.1; omega] at hb
  -- a moment μ in (β', e₀] with b[y] + h ≥ k
  have hμ : ∃ μ, β' < μ ∧ μ ≤ e₀ ∧ k ≤ bar tr μ y + h := by
    rcases hu with rfl | hy
    · exact ⟨x, by omega, by omega, by rw [hframe_y q x σ h hfr he (by omega) hxe₀]; omega⟩
    · obtain ⟨r, hr1, hr2, hstr, hcase⟩ := hR.scan q x σ u h hfr he y hy
      have hlr : (stk tr r).length = h + 1 := by rw [hstr, hfr.push]; omega
      rcases hcase with hyt | hys | hye | hyg
      · subst hyt; rw [hF.dropAt_t] at hd; cases hd
      · -- y on the stack: its frame exits before e₀ (else y would be on the stack at θ), fruitless
        obtain ⟨ey, xy, σy, hy', hfy, hey1, hey2, heny⟩ := hA.frame_of_mem hys
        have hxy : xy < e₀ := by
          refine Nat.lt_of_not_le fun hle => ?_
          rcases Nat.eq_or_lt_of_le hle with heq | hlt
          · obtain ⟨σx, vx, hx', sdx, fx, hex'⟩ := hfy.2.2.1
            obtain ⟨σe, ve, he', hee⟩ := hf₀.2.1
            rw [heq, hex'] at hee; cases hee
          · obtain ⟨hx₀, -⟩ := hfy.nest hf₀ (by omega) (by omega)
            have hp := hfy.prefix (q := θ) (by omega) (by omega)
            rw [Trace.stk_succ_enter heny] at hp
            have hmem : y ∈ (stk tr θ).take ((stk tr ey).length + 1) := by rw [hp]; simp
            exact (hR.drop θ σd y o nw hdw).1 (List.mem_of_mem_take hmem)
        have hdy := (hR.enter ey σy y hy' heny).1
        have hopen := hfy.isOpen (q := r) hey1 hey2
        exact ⟨xy, by omega, by omega, by rw [hframe_y ey xy σy hy' hfy heny (by omega) hxy]; omega⟩
      · -- a child call at y: fruitless, nested in the call at u
        obtain ⟨σc, hc, hec⟩ := Trace.enterAt_iff.mp hye
        obtain ⟨xc, hfc⟩ := hR.frame r σc y hc hec
        have hdc := (hR.enter r σc y hc hec).1
        obtain ⟨hxc, -⟩ := hfr.nest hfc hr1 (by omega)
        exact ⟨xc, by have := hfc.1; omega, by omega, by rw [hframe_y r xc σc hc hfc hec (by have := hfc.1; omega) (by omega)]; omega⟩
      · exact ⟨r, by omega, by omega, hyg⟩
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := hμ
  -- no drops of y in [μ, e₀): b[y] does not decrease
  have hup : bar tr μ y ≤ bar tr e₀ y := by
    apply Trace.bar_ge_of_raising hμ2
    intro r σ' o' nw' kd' h1 h2 hw
    have hold := hR.write_old r σ' y o' nw' kd' hw
    cases kd' with
    | drop =>
      have := hA.no_drop_asc hC' hS' (q := r) (y := y) (by omega) (by omega)
      simp [dropAt, hw] at this
    | raise => have := (hR.raise r σ' y o' nw' hw).2.2; omega
    | fruitful => have := (hR.fruitful r σ' y o' nw' hw).2.2.1; omega
  omega

open Classical in
/-- the calls at z entered in the period and not open at a have pairwise distinct depths -/
theorem nR_depth_inj (z : Fin n) : ∀ q₁ q₂, β' < q₁ → q₁ ≤ β → β' < q₂ → q₂ ≤ β → (enterAt tr z q₁ = true ∧ ¬ openAt tr a q₁) → (enterAt tr z q₂ = true ∧ ¬ openAt tr a q₂) → DelayFacts.depthOf tr q₁ = DelayFacts.depthOf tr q₂ → q₁ = q₂ := by
  intro q₁ q₂ a1 b1 a2 b2 ⟨hq1, hno1⟩ ⟨hq2, hno2⟩ hdep
  obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp hq1
  obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp hq2
  rw [DelayFacts.depthOf_enter he₁, DelayFacts.depthOf_enter he₂] at hdep
  subst hdep
  rcases Nat.lt_trichotomy q₁ q₂ with hlt | heq | hgt
  · exact (hA.nR_inj hC' hC hS' hS a1 hlt b2 he₁ he₂ hno1).elim
  · exact heq
  · exact (hA.nR_inj hC' hC hS' hS a2 hgt b1 he₂ he₁ hno2).elim

open Classical in
/-- the calls at u entered in the period, not open at a: at most k, and at most k + 1 - |S_θ| if u or a successor of u is
    dropped first at θ in the descent -/
theorem nR_le (u : Fin n) : cnt (fun q => enterAt tr u q = true ∧ ¬ openAt tr a q) β' β ≤ k ∧
    ∀ {θ : Nat} {y : Fin n}, a < θ → θ ≤ β → dropAt tr y θ = true → (∀ q, a < q → q < θ → dropAt tr y q = false) → (u = y ∨ y ∈ G.succ u) →
      cnt (fun q => enterAt tr u q = true ∧ ¬ openAt tr a q) β' β ≤ k + 1 - (stk tr θ).length := by
  have hR := hA.toRunFacts
  refine ⟨?_, ?_⟩
  · have := Trace.cnt_le_of_depth (fun q => enterAt tr u q = true ∧ ¬ openAt tr a q) (DelayFacts.depthOf tr) (lo := β') (hi := β) (A := 1) (B := k) ?_ (hA.nR_depth_inj hC' hC hS' hS u)
    · omega
    · intro q h1 h2 ⟨hq, hno⟩
      obtain ⟨σ, h, he⟩ := Trace.enterAt_iff.mp hq
      rw [DelayFacts.depthOf_enter he]
      exact ⟨hA.nR_depth_pos hC' hC h1 h2 he hno, by have := (hR.enter q σ u h he).2.2.2.1; omega⟩
  · intro θ y hθ1 hθ2 hd hfirst hu
    apply Trace.cnt_le_of_depth (fun q => enterAt tr u q = true ∧ ¬ openAt tr a q) (DelayFacts.depthOf tr) (A := (stk tr θ).length) (B := k) _ (hA.nR_depth_inj hC' hC hS' hS u)
    intro q h1 h2 ⟨hq, hno⟩
    obtain ⟨σ, h, he⟩ := Trace.enterAt_iff.mp hq
    rw [DelayFacts.depthOf_enter he]
    exact ⟨hA.period_split hC' hC hS' hS hθ1 hθ2 hd hfirst h1 h2 he hu hno, by have := (hR.enter q σ u h he).2.2.2.1; omega⟩

/-- the dequeues of y in the period are those of the descent: one per drop, plus at most one as an origin -/
theorem D_period_le (y : Fin n) : cnt (fun q => deqAt tr y q = true) β' β ≤ cnt (fun q => dropAt tr y q = true) a β + 1 := by
  have hR := hA.toRunFacts
  have hD0 : cnt (fun q => deqAt tr y q = true) β' a = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => by rw [hA.no_deq_asc hC' hS' h1 h2] at hq; cases hq)
  have hDs := Trace.cnt_split (fun q => deqAt tr y q = true) (Nat.le_of_lt hS'.lt) hS.le
  have hDle := (hR.intervalFacts hC hS).deq_count y
  have hFle := DelayFacts.F_le (tr := tr) y (lo := a) (hi := β)
  omega

open Classical in
/-- Period Budget, per node (prop:period-budget): at most k + 2 entries and dequeues of z in the period -/
theorem node_period (z : Fin n) : cnt (fun q => enterAt tr z q = true) β' β + cnt (fun q => deqAt tr z q = true) β' β ≤ k + 2 := by
  have hR := hA.toRunFacts
  have hF := hR.toDelayFacts
  have hEs : cnt (fun q => enterAt tr z q = true) β' β ≤ cnt (fun q => enterAt tr z q = true ∧ openAt tr a q) β' β + cnt (fun q => enterAt tr z q = true ∧ ¬ openAt tr a q) β' β := Trace.cnt_le_split _ _ β' β
  have hR1 := hA.R_le_one (a := a) (β' := β') (β := β) z
  have hD := hA.D_period_le hC' hC hS' hS z
  have hnR := hA.nR_le hC' hC hS' hS z
  by_cases hdr : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr z q = true
  · obtain ⟨q0, hq01, hq02, hq0⟩ := hdr
    obtain ⟨θ, hθ1, hθq, hθ, hfirst'⟩ := Trace.exists_first (P := fun q => dropAt tr z q = true) (lo := a) q0 hq01 hq0
    have hfirst : ∀ q, a < q → q < θ → dropAt tr z q = false := fun q h1 h2 => by
      cases h : dropAt tr z q
      · rfl
      · exact absurd h (hfirst' q h1 h2)
    have hU := hF.U_le hC hS hθ1 (by omega) hθ hfirst
    have h2 := hnR.2 hθ1 (by omega) hθ hfirst (Or.inl rfl)
    obtain ⟨σd, o, nw, hdw⟩ := Trace.dropAt_iff.mp hθ
    have hdd := hF.drop_depth hdw
    have hnw := (hR.drop θ σd z o nw hdw).2.2.1
    omega
  · have h0 : cnt (fun q => dropAt tr z q = true) a β = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => hdr ⟨q, h1, h2, hq⟩)
    have := hnR.1
    omega

open Classical in
/-- Period Budget, per edge: the scans of (x, y) by calls at x entered in the period and by dequeues of y, at most k + 2 -/
theorem edge_period {x y : Fin n} (hxy : y ∈ G.succ x) : cnt (fun q => enterAt tr x q = true) β' β + cnt (fun q => deqAt tr y q = true) β' β ≤ k + 2 := by
  have hR := hA.toRunFacts
  have hF := hR.toDelayFacts
  have hEs : cnt (fun q => enterAt tr x q = true) β' β ≤ cnt (fun q => enterAt tr x q = true ∧ openAt tr a q) β' β + cnt (fun q => enterAt tr x q = true ∧ ¬ openAt tr a q) β' β := Trace.cnt_le_split _ _ β' β
  have hR1 := hA.R_le_one (a := a) (β' := β') (β := β) x
  have hD := hA.D_period_le hC' hC hS' hS y
  have hnR := hA.nR_le hC' hC hS' hS x
  by_cases hdr : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr y q = true
  · obtain ⟨q0, hq01, hq02, hq0⟩ := hdr
    obtain ⟨θ, hθ1, hθq, hθ, hfirst'⟩ := Trace.exists_first (P := fun q => dropAt tr y q = true) (lo := a) q0 hq01 hq0
    have hfirst : ∀ q, a < q → q < θ → dropAt tr y q = false := fun q h1 h2 => by
      cases h : dropAt tr y q
      · rfl
      · exact absurd h (hfirst' q h1 h2)
    have hU := hF.U_le hC hS hθ1 (by omega) hθ hfirst
    have h2 := hnR.2 hθ1 (by omega) hθ hfirst (Or.inr hxy)
    obtain ⟨σd, o, nw, hdw⟩ := Trace.dropAt_iff.mp hθ
    have hdd := hF.drop_depth hdw
    have hnw := (hR.drop θ σd y o nw hdw).2.2.1
    omega
  · have h0 : cnt (fun q => dropAt tr y q = true) a β = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => hdr ⟨q, h1, h2, hq⟩)
    have := hnR.1
    omega

/-- a period costs at most (k + 2)(n + m), the output included (t's slot) -/
theorem period_cost (hG : G.WF) : lsum (List.range' (β' + 1) (β - β')) (posCost G tr) ≤ (k + 2) * (n + G.m) := by
  have hR := hA.toRunFacts
  have hF := hR.toDelayFacts
  refine cost_le_of_budget (t := t) hG (fun z _ => hA.node_period hC' hC hS' hS z) ?_ (fun x y hxy => hA.edge_period hC' hC hS' hS hxy) ?_
  · have h1 : cnt (fun q => enterAt tr t q = true) β' β = 0 := Trace.cnt_zero _ (fun q _ _ hq => by rw [hF.enterAt_t] at hq; cases hq)
    have h2 : cnt (fun q => deqAt tr t q = true) β' β = 0 := Trace.cnt_zero _ (fun q _ _ hq => by rw [hA.deqAt_t] at hq; cases hq)
    omega
  · exact Nat.le_trans (out_le_of_one hR (p := a) (fun q h1 h2 hq => no_obs hC' hC hS' hS h1 h2 hq)) (by omega)

end period

/-- an ascent alone, (β, c], costs at most (k + 2)(n + m): entries of distinct depths, no dequeues, the output -/
theorem asc_cost (hG : G.WF) {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β) : lsum (List.range' (β + 1) (c - β)) (posCost G tr) ≤ (k + 2) * (n + G.m) := by
  have hR := hA.toRunFacts
  have hF := hR.toDelayFacts
  have hI := hR.intervalFacts hC hS
  have hD0 : ∀ y, cnt (fun q => deqAt tr y q = true) β c = 0 := fun y => Trace.cnt_zero _ (fun q h1 h2 hq => by
    obtain ⟨σ, d, he⟩ := Trace.deqAt_iff.mp hq
    exact (hI.asc_pure q h1 h2).2.2 σ y d he)
  refine cost_le_of_budget (t := t) hG (fun z _ => ?_) ?_ (fun x y _ => ?_) ?_
  · have := hF.Ea_le hC hS z; rw [hD0 z]; omega
  · have : cnt (fun q => enterAt tr t q = true) β c = 0 := Trace.cnt_zero _ (fun q _ _ hq => by rw [hF.enterAt_t] at hq; cases hq)
    rw [hD0 t]; omega
  · have := hF.Ea_le hC hS x; rw [hD0 y]; omega
  · exact Nat.le_trans (out_le_of_one hR (p := c) (fun q h1 h2 hq => hC.between q (by have := hS.le; omega) (by omega))) (by omega)

/-- the cost up to β of the interval opened by a is at most (number of observable events before a) · (k + 2)(n + m): one
    period per earlier observable event -/
theorem cost_to_beta (hG : G.WF) : ∀ a c m β, Consec tr a c → Shape tr a c m β → lsum (List.range' 1 β) (posCost G tr) ≤ obsBefore tr a * ((k + 2) * (n + G.m)) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
  intro c m β hC hS
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- the initial interval: an empty descent
    subst ha
    have hβ : β = 0 := by
      refine Nat.eq_zero_of_not_pos fun hβ => ?_
      have h1 := hS.desc 1 (by omega) hβ
      rw [hA.stk_one] at h1
      simp at h1
    subst hβ
    simp [lsum]
  · -- the previous observable event a' and the period (β', β]
    obtain ⟨a', h0a', ha'a, ha'obs, hlast⟩ := Trace.exists_last (P := fun q => isObs tr q = true) (hi := a - 1) 0 (Nat.zero_le _) hA.isObs_zero
    have hC' : Consec tr a' a := ⟨by omega, by have := hC.lt; have := hC.bound; omega, ha'obs, hC.obs_a, fun q h1 h2 => by
      cases h : isObs tr q
      · rfl
      · exact absurd h (hlast q h1 (by omega))⟩
    obtain ⟨m', β', hS'⟩ := shape_exists hC'
    have hih := ih a' (by omega) a m' β' hC' hS'
    have hper := hA.period_cost hC' hC hS' hS hG
    have hsplit := lsum_range'_split (posCost G tr) (lo := 0) (mid := β') (hi := β) (Nat.zero_le _) (by have := hS'.lt; have := hS.le; omega)
    simp only [Nat.zero_add, Nat.sub_zero] at hsplit
    rw [hsplit, obsBefore_consec hC', Nat.add_mul, Nat.one_mul]
    omega

/-- the cost up to an observable event c is at most (number of observable events before c) · (k + 2)(n + m) -/
theorem cost_to_obs (hG : G.WF) {c : Nat} (hc : isObs tr c = true) (hcl : c < tr.length) : lsum (List.range' 1 c) (posCost G tr) ≤ obsBefore tr c * ((k + 2) * (n + G.m)) := by
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · subst h0; simp [lsum]
  · obtain ⟨a, h0a, hac, haobs, hlast⟩ := Trace.exists_last (P := fun q => isObs tr q = true) (hi := c - 1) 0 (Nat.zero_le _) hA.isObs_zero
    have hC : Consec tr a c := ⟨by omega, hcl, haobs, hc, fun q h1 h2 => by
      cases h : isObs tr q
      · rfl
      · exact absurd h (hlast q h1 (by omega))⟩
    obtain ⟨m, β, hS⟩ := shape_exists hC
    have h1 := hA.cost_to_beta hG a c m β hC hS
    have h2 := hA.asc_cost hG hC hS
    have hsplit := lsum_range'_split (posCost G tr) (lo := 0) (mid := β) (hi := c) (Nat.zero_le _) (Nat.le_of_lt hS.lt)
    simp only [Nat.zero_add, Nat.sub_zero] at hsplit
    rw [hsplit, obsBefore_consec hC, Nat.add_mul, Nat.one_mul]
    omega

end AmortFacts

/-! ## The theorem -/

/-- the root call's trace gives `PosOK` everywhere and the frame of the run -/
theorem amort_run {G : Graph n} {s t : Fin n} {k : Nat} {T : List (Ev n)} {N : List (List (Fin n))} {b : Vector Nat n} {σ σ' : Nat} (tc : TrCall G s t k 0 s #[] (Vector.replicate n 0) [Ev.start σ] N b T) :
    (∀ q, q < (T ++ [Ev.term σ']).length → PosOK G s t k (T ++ [Ev.term σ']) q) ∧ (∃ σ0, (T ++ [Ev.term σ'])[0]? = some (.start σ0)) ∧
      ∃ x σ1, Frame (T ++ [Ev.term σ']) 1 x ∧ (T ++ [Ev.term σ'])[x + 1]? = some (.term σ1) ∧ (T ++ [Ev.term σ']).length = x + 2 := by
  obtain ⟨σ0, E, hE, -⟩ := tc.ext
  have hlen : 2 ≤ T.length := by rw [hE]; simp
  refine ⟨posOK_run tc, ⟨σ, by rw [List.getElem?_append_left (by omega), hE]; simp⟩, T.length - 1, σ', tc.call.frame.append, ?_, ?_⟩
  · rw [show T.length - 1 + 1 = T.length by omega]; simp
  · simp; omega

/-- the run satisfies `AmortFacts` -/
theorem bsdfs_amortFacts (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) : AmortFacts G s t k (bsdfs G s t k) :=
  bsdfs_of_trCall G s t k hG hst _ fun _ _ _ _ tc => { toRunFacts := runFacts_of_posOK (amort_run tc).1, start := (amort_run tc).2.1, root := (amort_run tc).2.2 }

variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- amortized (v3, thm:amortized): the τ-th observable event happens after at most τ(k+2)(n+m) steps -/
theorem bsdfs_amortized_delay (hG : G.WF) (hst : s ≠ t) : ∀ τ (hτ : τ < (obsSteps (bsdfs G s t k)).length), (obsSteps (bsdfs G s t k))[τ] ≤ τ * (k + 2) * (n + G.m) := by
  intro τ hτ
  have hA := bsdfs_amortFacts G s t k hG hst
  have hstamp := bsdfs_stamps G s t k
  obtain ⟨σs, hs⟩ := hA.start
  have hpos : ∀ p x σ, (bsdfs G s t k)[p]? = some x → x.obs = some σ → σ ≤ (0 + ((bsdfs G s t k).take p).countP (fun y => y.obs.isSome)) * ((k + 2) * (n + G.m)) := by
    intro p x σ hp hx
    have hpl := Trace.lt_of_getElem? hp
    have hpx : (bsdfs G s t k)[p] = x := (List.getElem?_eq_some_iff.mp hp).2
    have h1 := (hstamp p hpl σ (by rw [hpx]; exact hx)).1
    have hc : G.cost ((bsdfs G s t k).take (p + 1)) = lsum (List.range' 0 (p + 1)) (posCost G (bsdfs G s t k)) := cost_drop_take G (bsdfs G s t k) (p + 1) 0 (by omega)
    have h0 : posCost G (bsdfs G s t k) 0 = 0 := by simp [posCost, hs, Graph.evCost]
    rw [hc, List.range'_succ, lsum_cons, h0, Nat.zero_add] at h1
    have h2 := hA.cost_to_obs hG (c := p) (by simp [isObs, hp, hx]) hpl
    rw [Nat.zero_add]
    exact Nat.le_trans h1 h2
  have := filterMap_le Ev.obs ((k + 2) * (n + G.m)) (bsdfs G s t k) 0 hpos τ ((obsSteps (bsdfs G s t k))[τ]) (by rw [← obsSteps_eq]; exact List.getElem?_eq_getElem hτ)
  rw [Nat.mul_assoc]
  simpa using this
