/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Trace

/-!
  Stage 2 of the delay proof: the v3 counting (Drop Depth, Descent Split, the budgets of edge_budget.tex and visits.md) derived
  from explicit facts about the trace.  `DelayFacts` collects the facts about single events (as the code emits them), Per-Call
  Global Monotonicity, the scans of a call, and, per interval, the v2 phase lemmas of bsdfs.tex (Ascent Purity, Call--Phase
  Correspondence, Descent Origins, Dequeue Count, Descent Seal, One Entry per Pair per Phase).  Stage 3 proves `DelayFacts`
  for the actual run.

  Phases without looking ahead: for consecutive observable events a < c, let m be the least stack size on (a, c] and β the
  first position after which the stack has size m.  Then descent = (a, β], ascent = (β, c], and m is the paper's j + 1.
-/

open Trace

variable {n : Nat}

/-- an observable event (start, output, term) at q -/
def Trace.isObs (tr : List (Ev n)) (q : Nat) : Bool := match tr[q]? with | some e => e.obs.isSome | none => false

/-- a and c are consecutive observable events -/
structure Consec (tr : List (Ev n)) (a c : Nat) : Prop where
  lt : a < c
  bound : c < tr.length
  obs_a : isObs tr a = true
  obs_c : isObs tr c = true
  between : ∀ q, a < q → q < c → isObs tr q = false

/-- m is the least stack size on (a, c], first reached right after β -/
structure Shape (tr : List (Ev n)) (a c m β : Nat) : Prop where
  le : a ≤ β
  lt : β < c
  at_beta : (stk tr (β + 1)).length = m
  min : ∀ q, a < q → q ≤ c → m ≤ (stk tr q).length
  desc : ∀ q, a < q → q ≤ β → m < (stk tr q).length

/-- the v2 phase lemmas for one interval -/
structure IntervalFacts (tr : List (Ev n)) (k a c m β : Nat) : Prop where
  /-- Ascent Purity: no drop, no fruitful write, no dequeue in the ascent -/
  asc_pure : ∀ q, β < q → q ≤ c → (∀ σ x o nw, tr[q]? ≠ some (.write σ x o nw .drop)) ∧ (∀ σ x o nw, tr[q]? ≠ some (.write σ x o nw .fruitful)) ∧ ∀ σ v d, tr[q]? ≠ some (.dequeue σ v d)
  /-- Call--Phase Correspondence (1): a call entered in the descent returns fruitless within it, with its raise -/
  desc_call : ∀ q σ z h, a < q → q ≤ β → tr[q]? = some (.enter σ z h) → ∃ x, Frame tr q x ∧ x ≤ β ∧ ∃ σ' o, tr[x - 1]? = some (.write σ' z o (k + 1 - h) .raise)
  /-- Descent Origins: every drop of the descent is made by the cascade of a spine frame below the fork, open since a -/
  desc_origin : ∀ θ y, a < θ → θ ≤ β → dropAt tr y θ = true → m + 1 ≤ (stk tr θ).length ∧ ∀ q, a < q → q ≤ θ → (stk tr θ).length ≤ (stk tr q).length
  /-- Dequeue Count: one dequeue per drop, plus at most one as an origin -/
  deq_count : ∀ z, cnt (fun q => deqAt tr z q = true) a β ≤ cnt (fun q => dropAt tr z q = true) a β + (if anyIn (fruitAt tr z) a β then 1 else 0)
  /-- Descent Seal: after a drop at z in the descent, z is not entered there, and only drops write it -/
  desc_seal : ∀ θ z, a < θ → θ ≤ β → dropAt tr z θ = true → ∀ q, θ < q → q ≤ β → enterAt tr z q = false ∧ ∀ σ o nw kd, tr[q]? = some (.write σ z o nw kd) → kd = .drop
  /-- One Entry per Pair per Phase -/
  one_entry : ∀ q₁ q₂ σ₁ σ₂ z h, q₁ ≠ q₂ → ((a < q₁ ∧ q₁ ≤ β ∧ a < q₂ ∧ q₂ ≤ β) ∨ (β < q₁ ∧ q₁ ≤ c ∧ β < q₂ ∧ q₂ ≤ c)) → tr[q₁]? = some (.enter σ₁ z h) → tr[q₂]? = some (.enter σ₂ z h) → False

/-- the facts about the run that the v3 counting uses -/
structure DelayFacts (G : Graph n) (s t : Fin n) (k : Nat) (tr : List (Ev n)) : Prop where
  /-- an entry at depth h = |S|, of a node off the stack and ≠ t, under the pruning guard; depth 0 only for the initial call -/
  enter : ∀ q σ z h, tr[q]? = some (.enter σ z h) → h = (stk tr q).length ∧ z ∉ stk tr q ∧ z ≠ t ∧ bar tr q z + h ≤ k ∧ (h = 0 → q = 1)
  /-- an exit pops the top frame -/
  exit : ∀ q σ v h sd f, tr[q]? = some (.exit σ v h sd f) → (stk tr q).getLast? = some v
  /-- an output is the stack followed by t -/
  output : ∀ q σ P, tr[q]? = some (.output σ P) → P = stk tr q ++ [t] ∧ (stk tr q).length ≤ k
  write_old : ∀ q σ x o nw kd, tr[q]? = some (.write σ x o nw kd) → o = bar tr q x
  /-- a raise b[x] := k - h + 1 at the return of the top frame, increasing -/
  raise : ∀ q σ x o nw, tr[q]? = some (.write σ x o nw .raise) → (stk tr q).getLast? = some x ∧ nw + (stk tr q).length = k + 2 ∧ o < nw
  /-- a fruitful write b[x] := sd ≤ k - h at the return of the top frame at depth ≥ 1 (early exit at s), not lowering -/
  fruitful : ∀ q σ x o nw, tr[q]? = some (.write σ x o nw .fruitful) → (stk tr q).getLast? = some x ∧ nw + (stk tr q).length ≤ k + 1 ∧ o ≤ nw ∧ 1 ≤ nw ∧ 2 ≤ (stk tr q).length
  /-- a drop lowers an off-stack node to a value ≥ 2, inside the cascade of a frame at depth ≥ 1 -/
  drop : ∀ q σ x o nw, tr[q]? = some (.write σ x o nw .drop) → x ∉ stk tr q ∧ nw < o ∧ 2 ≤ nw ∧ 2 ≤ (stk tr q).length
  /-- Per-Call Global Monotonicity -/
  mono : ∀ e x, Frame tr e x → ∀ z, bar tr e z ≤ bar tr (x + 1) z
  /-- a drop lies in the cascade of the top frame, and no later write of that frame touches the dropped node -/
  cascade : ∀ θ σ y o nw, tr[θ]? = some (.write σ y o nw .drop) → ∃ e x, Frame tr e x ∧ e < θ ∧ θ < x ∧ (stk tr (e + 1)).length = (stk tr θ).length ∧ ∀ q σ' o' nw' kd', θ < q → q < x → tr[q]? ≠ some (.write σ' y o' nw' kd')
  /-- two drops of one node lie in different cascades: the first cascade's frame returns in between -/
  onedrop : ∀ θ₁ θ₂ y, θ₁ < θ₂ → dropAt tr y θ₁ = true → dropAt tr y θ₂ = true → ∃ q, θ₁ < q ∧ q ≤ θ₂ ∧ (stk tr q).length < (stk tr θ₁).length
  /-- a call at u (depth h) scans every successor y: t, on the stack, entered as a child, or pruned -/
  scan : ∀ e x σ u h, Frame tr e x → tr[e]? = some (.enter σ u h) → ∀ y ∈ G.succ u, ∃ q, e < q ∧ q < x ∧ (y = t ∨ y ∈ stk tr q ∨ (enterAt tr y q = true ∧ (stk tr q).length = h + 1) ∨ k ≤ bar tr q y + h)
  bar_t : ∀ q, bar tr q t = 0
  /-- the v2 phase lemmas, per interval -/
  interval : ∀ a c m β, Consec tr a c → Shape tr a c m β → IntervalFacts tr k a c m β

namespace DelayFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hF : DelayFacts G s t k tr)
include hF

theorem t_not_mem (q : Nat) : t ∉ stk tr q := by
  apply Trace.not_mem_stk_of_no_enter (Nat.zero_le q) (by simp [stk])
  intro p _ _
  cases h : enterAt tr t p
  · rfl
  · obtain ⟨σ, hh, he⟩ := Trace.enterAt_iff.mp h
    exact absurd rfl (hF.enter p σ t hh he).2.2.1

theorem stk_nodup (q : Nat) : (stk tr q).Nodup :=
  Trace.stk_nodup (fun p σ v hh he => (hF.enter p σ v hh he).2.1) q

theorem enterAt_t (q : Nat) : enterAt tr t q = false := by
  cases h : enterAt tr t q
  · rfl
  · obtain ⟨σ, hh, he⟩ := Trace.enterAt_iff.mp h
    exact absurd rfl (hF.enter q σ t hh he).2.2.1

theorem dropAt_t (q : Nat) : dropAt tr t q = false := by
  cases h : dropAt tr t q
  · rfl
  · obtain ⟨σ, o, nw, he⟩ := Trace.dropAt_iff.mp h
    have h1 := hF.drop q σ t o nw he
    have h2 := hF.write_old q σ t o nw .drop he
    rw [hF.bar_t] at h2
    omega

theorem fruitAt_t (q : Nat) : fruitAt tr t q = false := by
  cases h : fruitAt tr t q
  · rfl
  · obtain ⟨σ, o, nw, he⟩ := Trace.fruitAt_iff.mp h
    have h1 := (hF.fruitful q σ t o nw he).1
    exact absurd (List.mem_of_getLast? h1) (hF.t_not_mem q)

/-- for k = 1 there are no fruitful writes (they need depth ≥ 1 and value ≥ 1 ≤ k - depth) -/
theorem fruitAt_of_k1 (hk : k = 1) (z : Fin n) (q : Nat) : fruitAt tr z q = false := by
  cases h : fruitAt tr z q
  · rfl
  · obtain ⟨σ, o, nw, he⟩ := Trace.fruitAt_iff.mp h
    have := hF.fruitful q σ z o nw he
    omega

/-- Drop Depth (v3, lem:drop-depth): a drop made by the cascade of the top frame, at depth i = |S| - 1, writes at most
    k - i - 1.  Every write to y inside the origin's frame before the drop lowers b[y] or comes from a deeper frame of y
    (at most k - i), and the frame's exit value, the drop value, is at least its entry value (Per-Call Global Monotonicity). -/
theorem drop_depth {θ σ y o nw} (hd : tr[θ]? = some (.write σ y o nw .drop)) : nw + (stk tr θ).length ≤ k := by
  obtain ⟨e, x, hfr, heθ, hθx, hlen, hnow⟩ := hF.cascade θ σ y o nw hd
  obtain ⟨hy, hlt, h2, hst⟩ := hF.drop θ σ y o nw hd
  have hold := hF.write_old θ σ y o nw .drop hd
  obtain ⟨hex1, ⟨σe, ve, he', hee⟩, ⟨σx, vx, hx, sdx, fx, hxe⟩, hsz, hopen⟩ := hfr
  have hfr : Frame tr e x := ⟨hex1, ⟨σe, ve, he', hee⟩, ⟨σx, vx, hx, sdx, fx, hxe⟩, hsz, hopen⟩
  have he1 : (stk tr (e + 1)).length = (stk tr e).length + 1 := by rw [Trace.stk_succ_enter hee]; simp
  -- the exit value of the origin's frame is the drop value
  have hexit : bar tr (x + 1) y = nw := by
    rw [Trace.not_write_of_exit hxe, Trace.bar_eq_of_no_write (p₁ := θ + 1) (by omega) (fun q σ' o' nw' kd' h1 h2 => hnow q σ' o' nw' kd' (by omega) h2), Trace.bar_succ_of_write hd]
  have hmono := hF.mono e x hfr y
  rw [hexit] at hmono
  -- inside the origin's frame the stack keeps its bottom (stk tr θ).length entries
  have hge : ∀ q, e + 1 ≤ q → q ≤ x → (stk tr θ).length ≤ (stk tr q).length := by
    intro q h1 h2; have := hopen q (by omega) h2; omega
  have hpersist : ∀ q, e + 1 ≤ q → q ≤ x → (stk tr q).take (stk tr θ).length = stk tr (e + 1) := by
    intro q h1 h2
    rw [Trace.stk_take_persist (p := e + 1) h1 (fun i hi1 hi2 => hge i hi1 (by omega)), ← hlen, List.take_length]
  have hθeq : stk tr θ = stk tr (e + 1) := by
    have := hpersist θ (by omega) (by omega)
    rwa [List.take_of_length_le (Nat.le_refl _)] at this
  -- a raise or fruitful write to y inside the frame comes from a frame deeper than the origin
  have hdeep : ∀ q, e < q → q < θ → (stk tr q).getLast? = some y → (stk tr θ).length + 1 ≤ (stk tr q).length := by
    intro q h1 h2 htop
    have hp := hpersist q (by omega) (by omega)
    have hg := hge q (by omega) (by omega)
    rcases Nat.lt_or_ge (stk tr θ).length (stk tr q).length with h | h
    · omega
    · exfalso
      have heq : stk tr q = stk tr (e + 1) := by rw [← hp, List.take_of_length_le h]
      rw [heq, ← hθeq] at htop
      exact hy (List.mem_of_getLast? htop)
  have hnote : ∀ q σ' o' nw' kd', tr[q]? = some (.write σ' y o' nw' kd') → q ≠ e := by
    intro q σ' o' nw' kd' hq hqe; subst hqe; rw [hee] at hq; cases hq
  -- every write to y in [e, θ) lowers it or writes at most k - i
  have hbound : bar tr θ y ≤ max (bar tr e y) (k + 1 - (stk tr θ).length) := by
    apply Trace.bar_le_max (by omega)
    intro q σ' o' nw' kd' h1 h2 hq
    have hqe := hnote q σ' o' nw' kd' hq
    cases kd' with
    | drop => left; have := hF.drop q σ' y o' nw' hq; have := hF.write_old q σ' y o' nw' .drop hq; omega
    | raise =>
      right
      obtain ⟨htop, hval, -⟩ := hF.raise q σ' y o' nw' hq
      have := hdeep q (by omega) h2 htop
      omega
    | fruitful =>
      right
      obtain ⟨htop, hval, -⟩ := hF.fruitful q σ' y o' nw' hq
      have := hdeep q (by omega) h2 htop
      omega
  omega

end DelayFacts

namespace DelayFacts
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hF : DelayFacts G s t k tr) {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β)
include hF hC hS

omit hC in
theorem depth_desc {q σ z h} (h1 : a < q) (h2 : q ≤ β) (he : tr[q]? = some (.enter σ z h)) : m + 1 ≤ h ∧ h ≤ k := by
  have := hF.enter q σ z h he
  have := hS.desc q h1 h2
  omega

omit hC in
theorem depth_asc {q σ z h} (h1 : β < q) (h2 : q ≤ c) (he : tr[q]? = some (.enter σ z h)) : m ≤ h ∧ h ≤ k := by
  have := hF.enter q σ z h he
  have := hS.min q (by have := hS.le; omega) h2
  omega

/-- entry depth, read off the event -/
def depthOf (tr : List (Ev n)) (q : Nat) : Nat := match tr[q]? with | some (.enter _ _ h) => h | _ => 0

omit hF hC hS in
theorem depthOf_enter {q σ z h} (he : tr[q]? = some (.enter σ z h)) : depthOf tr q = h := by
  simp [depthOf, he]

/-- calls at z entered in the descent: pairwise distinct depths in [m+1, k] -/
theorem Ed_le (z : Fin n) : cnt (fun q => enterAt tr z q = true) a β ≤ k - m := by
  have := Trace.cnt_le_of_depth (fun q => enterAt tr z q = true) (depthOf tr) (lo := a) (hi := β) (A := m + 1) (B := k) ?_ ?_
  · omega
  · intro q h1 h2 hq
    obtain ⟨σ, h, he⟩ := Trace.enterAt_iff.mp hq
    rw [depthOf_enter he]; exact hF.depth_desc hS h1 h2 he
  · intro q₁ q₂ a1 b1 a2 b2 c1 c2 hd
    obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp c1
    obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp c2
    rw [depthOf_enter he₁, depthOf_enter he₂] at hd
    subst hd
    exact Classical.byContradiction fun hne => (hF.interval a c m β hC hS).one_entry q₁ q₂ σ₁ σ₂ z h₁ hne (Or.inl ⟨a1, b1, a2, b2⟩) he₁ he₂

/-- calls at z entered in the ascent: pairwise distinct depths in [m, k] -/
theorem Ea_le (z : Fin n) : cnt (fun q => enterAt tr z q = true) β c ≤ k + 1 - m := by
  apply Trace.cnt_le_of_depth (fun q => enterAt tr z q = true) (depthOf tr) (A := m) (B := k)
  · intro q h1 h2 hq
    obtain ⟨σ, h, he⟩ := Trace.enterAt_iff.mp hq
    rw [depthOf_enter he]; exact hF.depth_asc hS h1 h2 he
  · intro q₁ q₂ a1 b1 a2 b2 c1 c2 hd
    obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp c1
    obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp c2
    rw [depthOf_enter he₁, depthOf_enter he₂] at hd
    subst hd
    exact Classical.byContradiction fun hne => (hF.interval a c m β hC hS).one_entry q₁ q₂ σ₁ σ₂ z h₁ hne (Or.inr ⟨a1, b1, a2, b2⟩) he₁ he₂

/-- drops of one node in the descent come from origins of strictly decreasing depth -/
theorem drop_lt {θ₁ θ₂ : Nat} {y : Fin n} (h1 : a < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ ≤ β) (d1 : dropAt tr y θ₁ = true) (d2 : dropAt tr y θ₂ = true) : (stk tr θ₂).length < (stk tr θ₁).length := by
  obtain ⟨q, hq1, hq2, hq⟩ := hF.onedrop θ₁ θ₂ y h12 d1 d2
  have := ((hF.interval a c m β hC hS).desc_origin θ₂ y (by omega) h2 d2).2 q (by omega) hq2
  omega

omit hC hS in
/-- a drop writes a value ≥ 2 into an off-stack node, at most k - i - 1 -/
theorem drop_facts {θ : Nat} {y : Fin n} (hd : dropAt tr y θ = true) : ∃ σ o nw, tr[θ]? = some (.write σ y o nw .drop) ∧ y ∉ stk tr θ ∧ 2 ≤ nw ∧ nw + (stk tr θ).length ≤ k ∧ bar tr (θ + 1) y = nw := by
  obtain ⟨σ, o, nw, he⟩ := Trace.dropAt_iff.mp hd
  exact ⟨σ, o, nw, he, (hF.drop θ σ y o nw he).1, (hF.drop θ σ y o nw he).2.2.1, hF.drop_depth he, Trace.bar_succ_of_write he⟩

/-- Descent Split (v3, lem:descent-split): if y is dropped first at θ in the descent, by the cascade of an origin at depth
    i = |S| - 1, every call at y or at a predecessor of y entered in the descent has depth ≥ i + 1 -/
theorem descent_split {θ : Nat} {y : Fin n} (hθ1 : a < θ) (hθ2 : θ ≤ β) (hd : dropAt tr y θ = true)
    {q σ : Nat} {u : Fin n} {h : Nat} (hq1 : a < q) (hq2 : q ≤ β) (he : tr[q]? = some (.enter σ u h)) (hu : u = y ∨ y ∈ G.succ u) : (stk tr θ).length ≤ h := by
  have hI := hF.interval a c m β hC hS
  obtain ⟨hmθ, horg⟩ := hI.desc_origin θ y hθ1 hθ2 hd
  have hh := (hF.enter q σ u h he).1
  rcases Nat.lt_or_ge q θ with hlt | hge
  · have := horg q hq1 (by omega); omega
  · have hne : q ≠ θ := by
      intro hqe; subst hqe; obtain ⟨σd, od, nwd, hw⟩ := Trace.dropAt_iff.mp hd; rw [hw] at he; cases he
    have hgt : θ < q := by omega
    obtain ⟨σd, od, nwd, hw, hy, h2d, hdepth, hbar⟩ := hF.drop_facts hd
    have hseal := hI.desc_seal θ y hθ1 hθ2 hd
    rcases hu with rfl | hsucc
    · have := (hseal q hgt hq2).1
      rw [Trace.enterAt_iff.mpr ⟨σ, h, he⟩] at this; cases this
    · obtain ⟨x, hfr, hxβ, -⟩ := hI.desc_call q σ u h hq1 hq2 he
      obtain ⟨r, hr1, hr2, hcase⟩ := hF.scan q x σ u h hfr he y hsucc
      have hrβ : r ≤ β := by omega
      rcases hcase with hyt | hys | ⟨hent, -⟩ | hprune
      · subst hyt; rw [hF.dropAt_t] at hd; cases hd
      · exfalso
        apply Trace.not_mem_stk_of_no_enter (Nat.le_of_lt (show θ < r by omega)) hy (fun p hp1 hp2 => ?_) hys
        rcases Nat.lt_or_ge θ p with hp | hp
        · exact (hseal p hp (by omega)).1
        · have : p = θ := by omega
          subst this
          cases hc : enterAt tr y p
          · rfl
          · obtain ⟨σe, he2, he3⟩ := Trace.enterAt_iff.mp hc; rw [hw] at he3; cases he3
      · rw [(hseal r (by omega) hrβ).1] at hent; cases hent
      · have hlow : bar tr r y ≤ bar tr (θ + 1) y := by
          apply Trace.bar_le_of_lowering (by omega)
          intro p σw ow nww kdw hp1 hp2 hp
          have hkd := (hseal p (by omega) (by omega)).2 σw ow nww kdw hp
          subst hkd
          have := hF.drop p σw y ow nww hp
          have := hF.write_old p σw y ow nww .drop hp
          omega
        omega

/-- the drops of y in the descent: their origins have pairwise distinct depths in [max(m, 1), i], with i + 1 = |S| at the first drop -/
theorem U_le {θ : Nat} {y : Fin n} (hθ1 : a < θ) (hθ2 : θ ≤ β) (hd : dropAt tr y θ = true) (hfirst : ∀ q, a < q → q < θ → dropAt tr y q = false) : cnt (fun q => dropAt tr y q = true) a β + max (m + 1) 2 ≤ (stk tr θ).length + 1 := by
  have hI := hF.interval a c m β hC hS
  have hlow : ∀ q, a < q → q ≤ β → dropAt tr y q = true → max (m + 1) 2 ≤ (stk tr q).length := by
    intro q h1 h2 hq
    have := (hI.desc_origin q y h1 h2 hq).1
    obtain ⟨σ, o, nw, hw⟩ := Trace.dropAt_iff.mp hq
    have := (hF.drop q σ y o nw hw).2.2.2
    omega
  have hcnt := Trace.cnt_le_of_depth (fun q => dropAt tr y q = true) (fun q => (stk tr q).length) (lo := a) (hi := β) (A := max (m + 1) 2) (B := (stk tr θ).length) ?_ ?_
  · have := hlow θ hθ1 hθ2 hd
    omega
  · intro q h1 h2 hq
    refine ⟨hlow q h1 h2 hq, ?_⟩
    rcases Nat.lt_or_ge q θ with hlt | hge
    · rw [hfirst q h1 hlt] at hq; cases hq
    · rcases Nat.lt_or_ge θ q with hlt' | hge'
      · exact Nat.le_of_lt (hF.drop_lt hC hS hθ1 hlt' h2 hd hq)
      · have : q = θ := by omega
        subst this; exact Nat.le_refl _
  · intro q₁ q₂ a1 b1 a2 b2 c1 c2 heq
    rcases Nat.lt_trichotomy q₁ q₂ with hlt | heq' | hgt
    · have := hF.drop_lt hC hS a1 hlt b2 c1 c2; omega
    · exact heq'
    · have := hF.drop_lt hC hS a2 hgt b1 c2 c1; omega

/-- (i) of Interval Budget: a node dropped in the descent keeps b ≥ 2 through the ascent, so it is entered there at depth ≤ k - 2 -/
theorem obs_i {θ : Nat} {z : Fin n} (hθ1 : a < θ) (hθ2 : θ ≤ β) (hd : dropAt tr z θ = true) : cnt (fun q => enterAt tr z q = true) β c ≤ k - 1 - m := by
  have hI := hF.interval a c m β hC hS
  obtain ⟨θl, hl1, hl2, hld, hlast⟩ := Trace.exists_last (P := fun q => dropAt tr z q = true) (hi := β) θ hθ2 hd
  obtain ⟨σ, o, nw, hw, -, h2, hdepth, hbar⟩ := hF.drop_facts hld
  have hk4 : 4 ≤ k := by have := (hF.drop θl σ z o nw hw).2.2.2; omega
  -- no write lowers z after its last drop, up to c
  have hge : ∀ q, θl + 1 ≤ q → q ≤ c → 2 ≤ bar tr q z := by
    intro q h1 h2'
    have := Trace.bar_ge_of_raising (tr := tr) (z := z) (p₁ := θl + 1) (p₂ := q) h1 (fun p σw ow nww kdw hp1 hp2 hp => by
      have hold := hF.write_old p σw z ow nww kdw hp
      rcases Nat.lt_or_ge β p with hpβ | hpβ
      · have hpure := hI.asc_pure p hpβ (by omega)
        cases kdw with
        | drop => exact absurd hp (hpure.1 σw z ow nww)
        | fruitful => exact absurd hp (hpure.2.1 σw z ow nww)
        | raise => have := hF.raise p σw z ow nww hp; omega
      · have hkd := (hI.desc_seal θl z (by omega) hl2 hld p (by omega) hpβ).2 σw ow nww kdw hp
        subst hkd
        exact absurd (Trace.dropAt_iff.mpr ⟨σw, ow, nww, hp⟩) (hlast p (by omega) hpβ))
    omega
  have hcnt := Trace.cnt_le_of_depth (fun q => enterAt tr z q = true) (depthOf tr) (lo := β) (hi := c) (A := m) (B := k - 2) ?_ ?_
  · omega
  · intro q h1 h2' hq
    obtain ⟨σe, h, he⟩ := Trace.enterAt_iff.mp hq
    rw [depthOf_enter he]
    have := hF.enter q σe z h he
    have := hge q (by omega) h2'
    have := hF.depth_asc hS h1 h2' he
    omega
  · intro q₁ q₂ a1 b1 a2 b2 c1 c2 hdq
    obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp c1
    obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp c2
    rw [depthOf_enter he₁, depthOf_enter he₂] at hdq
    subst hdq
    exact Classical.byContradiction fun hne => hI.one_entry q₁ q₂ σ₁ σ₂ z h₁ hne (Or.inr ⟨a1, b1, a2, b2⟩) he₁ he₂

/-- (ii) of Interval Budget: a node not dropped in the descent is entered at most k + 1 - m times in the interval; the raise of
    its shallowest descent call persists through the ascent -/
theorem obs_ii {z : Fin n} (hnd : ∀ q, a < q → q ≤ β → dropAt tr z q = false) : cnt (fun q => enterAt tr z q = true) a β + cnt (fun q => enterAt tr z q = true) β c ≤ k + 1 - m := by
  have hI := hF.interval a c m β hC hS
  by_cases hex : ∃ q, a < q ∧ q ≤ β ∧ enterAt tr z q = true
  · obtain ⟨q₀, ⟨hq01, hq02, hq0⟩, hmin⟩ := Trace.exists_min (P := fun q => a < q ∧ q ≤ β ∧ enterAt tr z q = true) (depthOf tr) _ hex.choose_spec
    obtain ⟨σ₀, h₀, he₀⟩ := Trace.enterAt_iff.mp hq0
    have hd₀ := depthOf_enter he₀
    have hrange₀ := hF.depth_desc hS hq01 hq02 he₀
    obtain ⟨x, hfr, hxβ, σr, or, hr⟩ := hI.desc_call q₀ σ₀ z h₀ hq01 hq02 he₀
    have hx1 : q₀ < x := hfr.1
    have hbarx : bar tr x z = k + 1 - h₀ := by
      have := Trace.bar_succ_of_write hr
      rwa [show x - 1 + 1 = x by omega] at this
    have hge : ∀ q, x ≤ q → q ≤ c → k + 1 - h₀ ≤ bar tr q z := by
      intro q h1 h2'
      rw [← hbarx]
      apply Trace.bar_ge_of_raising h1
      intro p σw ow nww kdw hp1 hp2 hp
      have hold := hF.write_old p σw z ow nww kdw hp
      cases kdw with
      | raise => have := hF.raise p σw z ow nww hp; omega
      | fruitful =>
        rcases Nat.lt_or_ge β p with hpβ | hpβ
        · exact absurd hp ((hI.asc_pure p hpβ (by omega)).2.1 σw z ow nww)
        · have := hF.fruitful p σw z ow nww hp; omega
      | drop =>
        rcases Nat.lt_or_ge β p with hpβ | hpβ
        · exact absurd hp ((hI.asc_pure p hpβ (by omega)).1 σw z ow nww)
        · have := hnd p (by omega) hpβ
          rw [Trace.dropAt_iff.mpr ⟨σw, ow, nww, hp⟩] at this; cases this
    have hd := Trace.cnt_le_of_depth (fun q => enterAt tr z q = true) (depthOf tr) (lo := a) (hi := β) (A := h₀) (B := k) ?_ ?_
    have ha := Trace.cnt_le_of_depth (fun q => enterAt tr z q = true) (depthOf tr) (lo := β) (hi := c) (A := m) (B := h₀ - 1) ?_ ?_
    · omega
    · intro q h1 h2' hq
      obtain ⟨σe, h, he⟩ := Trace.enterAt_iff.mp hq
      rw [depthOf_enter he]
      have := hF.enter q σe z h he
      have := hge q (by omega) h2'
      have := hF.depth_asc hS h1 h2' he
      omega
    · intro q₁ q₂ a1 b1 a2 b2 c1 c2 hdq
      obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp c1
      obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp c2
      rw [depthOf_enter he₁, depthOf_enter he₂] at hdq
      subst hdq
      exact Classical.byContradiction fun hne => hI.one_entry q₁ q₂ σ₁ σ₂ z h₁ hne (Or.inr ⟨a1, b1, a2, b2⟩) he₁ he₂
    · intro q h1 h2' hq
      obtain ⟨σe, h, he⟩ := Trace.enterAt_iff.mp hq
      have := hmin q ⟨h1, h2', hq⟩
      rw [hd₀, depthOf_enter he] at this
      rw [depthOf_enter he]
      exact ⟨this, (hF.depth_desc hS h1 h2' he).2⟩
    · intro q₁ q₂ a1 b1 a2 b2 c1 c2 hdq
      obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp c1
      obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp c2
      rw [depthOf_enter he₁, depthOf_enter he₂] at hdq
      subst hdq
      exact Classical.byContradiction fun hne => hI.one_entry q₁ q₂ σ₁ σ₂ z h₁ hne (Or.inl ⟨a1, b1, a2, b2⟩) he₁ he₂
  · have h0 : cnt (fun q => enterAt tr z q = true) a β = 0 :=
      Trace.cnt_zero _ (fun q h1 h2 hq => hex ⟨q, h1, h2, hq⟩)
    have := hF.Ea_le hC hS z
    omega

omit hC in
/-- the ascent of the terminal interval (m = 0, non-empty descent) enters nothing -/
theorem term_asc_empty (hm : m = 0) (hβ : a < β) (z : Fin n) : cnt (fun q => enterAt tr z q = true) β c = 0 := by
  apply Trace.cnt_zero
  intro q h1 h2 hq
  obtain ⟨q₀, hq01, hq02, ⟨σ₀, v₀, h₀, he₀⟩, hfirst⟩ := Trace.exists_first (P := fun q => ∃ σ v h, tr[q]? = some (.enter σ v h)) (lo := β) q h1 (by obtain ⟨σ, h, he⟩ := Trace.enterAt_iff.mp hq; exact ⟨σ, z, h, he⟩)
  have hnil : stk tr q₀ = [] := by
    apply Trace.stk_nil_of_no_enter (p₁ := β + 1) (by omega) (by have := hS.at_beta; rw [hm] at this; exact List.length_eq_zero_iff.mp this)
    · intro p σ v h sd f hp hn
      have := hF.exit p σ v h sd f hp
      rw [hn] at this; cases this
    · intro p hp1 hp2 σ v h hp
      exact hfirst p (by omega) hp2 ⟨σ, v, h, hp⟩
  have he := hF.enter q₀ σ₀ v₀ h₀ he₀
  rw [hnil] at he
  have : q₀ = 1 := he.2.2.2.2 (by simpa using he.1)
  omega

/-- the dequeues of y in the interval: none in the ascent, and in the descent one per drop plus at most one as an origin -/
theorem D_le (y : Fin n) : cnt (fun q => deqAt tr y q = true) a c ≤ cnt (fun q => dropAt tr y q = true) a β + (if anyIn (fruitAt tr y) a β then 1 else 0) := by
  have hI := hF.interval a c m β hC hS
  rw [Trace.cnt_split _ hS.le (Nat.le_of_lt hS.lt)]
  have h0 : cnt (fun q => deqAt tr y q = true) β c = 0 := by
    apply Trace.cnt_zero
    intro q h1 h2 hq
    obtain ⟨σ, d, he⟩ := Trace.deqAt_iff.mp hq
    exact (hI.asc_pure q h1 h2).2.2 σ y d he
  have := hI.deq_count y
  omega

omit hF hC hS in
theorem F_le (y : Fin n) {lo hi : Nat} : (if anyIn (fruitAt tr y) lo hi then 1 else 0) ≤ 1 := by
  split <;> omega

omit hC hS in
theorem F_k1 (hk : k = 1) (y : Fin n) {lo hi : Nat} : (if anyIn (fruitAt tr y) lo hi then 1 else 0) = 0 := by
  have : anyIn (fruitAt tr y) lo hi = false := by
    cases h : anyIn (fruitAt tr y) lo hi
    · rfl
    · obtain ⟨q, -, -, hq⟩ := Trace.anyIn_iff.mp h
      rw [hF.fruitAt_of_k1 hk y q] at hq; cases hq
  simp [this]

/-- calls at u entered in the descent, if a successor (or u itself) is dropped first at θ: depths in [|S_θ|, k] -/
theorem Ed_le_split {θ : Nat} {y u : Fin n} (hθ1 : a < θ) (hθ2 : θ ≤ β) (hd : dropAt tr y θ = true) (hu : u = y ∨ y ∈ G.succ u) : cnt (fun q => enterAt tr u q = true) a β ≤ k + 1 - (stk tr θ).length := by
  apply Trace.cnt_le_of_depth (fun q => enterAt tr u q = true) (depthOf tr) (A := (stk tr θ).length) (B := k)
  · intro q h1 h2 hq
    obtain ⟨σ, h, he⟩ := Trace.enterAt_iff.mp hq
    rw [depthOf_enter he]
    exact ⟨hF.descent_split hC hS hθ1 hθ2 hd h1 h2 he hu, (hF.depth_desc hS h1 h2 he).2⟩
  · intro q₁ q₂ a1 b1 a2 b2 c1 c2 hdq
    obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp c1
    obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp c2
    rw [depthOf_enter he₁, depthOf_enter he₂] at hdq
    subst hdq
    exact Classical.byContradiction fun hne => (hF.interval a c m β hC hS).one_entry q₁ q₂ σ₁ σ₂ u h₁ hne (Or.inl ⟨a1, b1, a2, b2⟩) he₁ he₂

/-- the first drop of a dropped node, with the facts the budgets use -/
theorem first_drop {y : Fin n} (hex : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr y q = true) : ∃ θ, a < θ ∧ θ ≤ β ∧ dropAt tr y θ = true ∧
    cnt (fun q => dropAt tr y q = true) a β + max (m + 1) 2 ≤ (stk tr θ).length + 1 ∧ (stk tr θ).length + 2 ≤ k ∧ m + 1 ≤ (stk tr θ).length ∧ 2 ≤ (stk tr θ).length := by
  obtain ⟨q, hq1, hq2, hq⟩ := hex
  obtain ⟨θ, hθ1, hθ2, hθ, hfirst⟩ := Trace.exists_first (P := fun q => dropAt tr y q = true) (lo := a) q hq1 hq
  have hθβ : θ ≤ β := by omega
  have hU := hF.U_le hC hS hθ1 hθβ hθ (fun q' h1 h2 => by cases h : dropAt tr y q'; rfl; exact absurd h (hfirst q' h1 h2))
  obtain ⟨σ, o, nw, hw, -, h2, hdepth, -⟩ := hF.drop_facts hθ
  have := (hF.drop θ σ y o nw hw).2.2.2
  have := ((hF.interval a c m β hC hS).desc_origin θ y hθ1 hθβ hθ).1
  exact ⟨θ, hθ1, hθβ, hθ, hU, by omega, by omega, by omega⟩

omit hF in
/-- the stack at a is empty when the descent is empty and m = 0 -/
theorem stk_a_nil (hm : m = 0) (hβ : β = a) : stk tr a = [] := by
  have h1 := hS.at_beta
  rw [hβ, hm] at h1
  have hobs := hC.obs_a
  have : stk tr (a + 1) = stk tr a := by
    apply Trace.stk_succ_other
    · intro σ v h he; simp [isObs, he, Ev.obs] at hobs
    · intro σ v h sd f he; simp [isObs, he, Ev.obs] at hobs
  rw [this] at h1
  exact List.length_eq_zero_iff.mp h1

/-- Interval Budget, per node (v3): at most 2k entries and dequeues of z in the interval -/
theorem node_budget (hk : 1 ≤ k) (z : Fin n) : cnt (fun q => enterAt tr z q = true) a c + cnt (fun q => deqAt tr z q = true) a c ≤ 2 * k := by
  rw [Trace.cnt_split (fun q => enterAt tr z q = true) hS.le (Nat.le_of_lt hS.lt)]
  have hD := hF.D_le hC hS z
  have hF1 := F_le (tr := tr) (lo := a) (hi := β) z
  have hEa := hF.Ea_le hC hS z
  have hEd := hF.Ed_le hC hS z
  by_cases hdr : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr z q = true
  · obtain ⟨θ, hθ1, hθ2, hθ, hU, hL, hLm, hL2⟩ := hF.first_drop hC hS hdr
    have hEd' := hF.Ed_le_split hC hS hθ1 hθ2 hθ (Or.inl rfl)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have hEa0 := hF.term_asc_empty hS hm (by omega) z
      simp only [hm] at hU
      omega
    · have hEa' := hF.obs_i hC hS hθ1 hθ2 hθ
      omega
  · have hU0 : cnt (fun q => dropAt tr z q = true) a β = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => hdr ⟨q, h1, h2, hq⟩)
    have hii := hF.obs_ii hC hS (z := z) (fun q h1 h2 => by cases h : dropAt tr z q; rfl; exact absurd ⟨q, h1, h2, h⟩ hdr)
    rcases Nat.eq_or_lt_of_le hk with hk1 | hk1
    · have := hF.F_k1 hk1.symm (lo := a) (hi := β) z
      omega
    · omega

/-- Interval Budget, per edge (v3): the scans of an edge (x, y) — forward by calls at x entered in the interval or by the
    spine frame of x, backward by dequeues of y — number at most 2k -/
theorem edge_budget (hk : 1 ≤ k) {x y : Fin n} (hxy : y ∈ G.succ x) : cnt (fun q => enterAt tr x q = true) a c + cnt (fun q => deqAt tr y q = true) a c + (if x ∈ stk tr a then 1 else 0) ≤ 2 * k := by
  rw [Trace.cnt_split (fun q => enterAt tr x q = true) hS.le (Nat.le_of_lt hS.lt)]
  have hD := hF.D_le hC hS y
  have hF1 := F_le (tr := tr) (lo := a) (hi := β) y
  have hEa := hF.Ea_le hC hS x
  have hEd := hF.Ed_le hC hS x
  have hsp : (if x ∈ stk tr a then 1 else 0) ≤ 1 := by split <;> omega
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rcases Nat.eq_or_lt_of_le hS.le with hβ | hβ
    · -- initial interval: empty descent, empty stack at a
      have hDd0 : cnt (fun q => dropAt tr y q = true) a β = 0 := by rw [← hβ]; exact Trace.cnt_zero _ (fun q h1 h2 => by omega)
      have hF0 : (if anyIn (fruitAt tr y) a β then 1 else 0) = 0 := by
        have : anyIn (fruitAt tr y) a β = false := by
          cases h : anyIn (fruitAt tr y) a β
          · rfl
          · obtain ⟨q, h1, h2, -⟩ := Trace.anyIn_iff.mp h; omega
        simp [this]
      have hEd0 : cnt (fun q => enterAt tr x q = true) a β = 0 := by rw [← hβ]; exact Trace.cnt_zero _ (fun q h1 h2 => by omega)
      have hsp0 : (if x ∈ stk tr a then 1 else 0) = 0 := by simp [stk_a_nil hC hS hm hβ.symm]
      simp only [hm] at hEa
      omega
    · -- terminal interval: empty ascent
      have hEa0 := hF.term_asc_empty hS hm hβ x
      by_cases hdr : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr y q = true
      · obtain ⟨θ, hθ1, hθ2, hθ, hU, hL, hLm, hL2⟩ := hF.first_drop hC hS hdr
        have hEd' := hF.Ed_le_split hC hS hθ1 hθ2 hθ (Or.inr hxy)
        simp only [hm] at hU
        omega
      · have hU0 : cnt (fun q => dropAt tr y q = true) a β = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => hdr ⟨q, h1, h2, hq⟩)
        rcases Nat.eq_or_lt_of_le hk with hk1 | hk1
        · have := hF.F_k1 hk1.symm (lo := a) (hi := β) y
          simp only [hm] at hEd
          omega
        · simp only [hm] at hEd
          omega
  · -- inner interval
    by_cases hdx : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr x q = true
    · obtain ⟨θx, hθx1, hθx2, hθx, -, -, -, -⟩ := hF.first_drop hC hS hdx
      have hEa' := hF.obs_i hC hS hθx1 hθx2 hθx
      by_cases hdr : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr y q = true
      · obtain ⟨θ, hθ1, hθ2, hθ, hU, hL, hLm, hL2⟩ := hF.first_drop hC hS hdr
        have hEd' := hF.Ed_le_split hC hS hθ1 hθ2 hθ (Or.inr hxy)
        omega
      · have hU0 : cnt (fun q => dropAt tr y q = true) a β = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => hdr ⟨q, h1, h2, hq⟩)
        omega
    · have hii := hF.obs_ii hC hS (z := x) (fun q h1 h2 => by cases h : dropAt tr x q; rfl; exact absurd ⟨q, h1, h2, h⟩ hdx)
      by_cases hdr : ∃ q, a < q ∧ q ≤ β ∧ dropAt tr y q = true
      · obtain ⟨θ, hθ1, hθ2, hθ, hU, hL, hLm, hL2⟩ := hF.first_drop hC hS hdr
        omega
      · have hU0 : cnt (fun q => dropAt tr y q = true) a β = 0 := Trace.cnt_zero _ (fun q h1 h2 hq => hdr ⟨q, h1, h2, hq⟩)
        rcases Nat.eq_or_lt_of_le hk with hk1 | hk1
        · have := hF.F_k1 hk1.symm (lo := a) (hi := β) y
          omega
        · omega

end DelayFacts
