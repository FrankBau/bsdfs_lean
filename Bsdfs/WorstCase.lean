/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.RunSearch

/-!
  The worst-case delay of BS-DFS (v3, thm:worst-case-delay): consecutive observable events (start, outputs, term) are at most
  2k(n + m) steps apart.  Stage 3c, part 4: the root call gives `PosOK` at every position of the run, hence `RunFacts`, and
  `worst_case_of_run` (Stage 3b) gives the bound.
-/

open Std.Do Trace

set_option mvcgen.warning false

variable {n : Nat}

theorem root_tr {σ : Nat} : TrPre 0 (#[] : Array (Fin n)) (Vector.replicate n 0) [Ev.start σ] where
  stk := by rw [show [Ev.start σ].length = 0 + 1 from rfl, Trace.stk_succ]; rfl
  bar := fun z => by rw [show [Ev.start σ].length = 0 + 1 from rfl, Trace.bar_succ]; simp [bar]
  root := fun _ => rfl

theorem posOK_start {G : Graph n} {s t : Fin n} {k : Nat} {T : List (Ev n)} {q σ : Nat} (h : T[q]? = some (.start σ)) : PosOK G s t k T q :=
  ⟨by simp [EvOK, h], (fun σ' v h' he => by rw [h] at he; cases he), (fun hc => by simp [isCasc, h] at hc)⟩

theorem posOK_term {G : Graph n} {s t : Fin n} {k : Nat} {T : List (Ev n)} {q σ : Nat} (h : T[q]? = some (.term σ)) : PosOK G s t k T q :=
  ⟨by simp [EvOK, h], (fun σ' v h' he => by rw [h] at he; cases he), (fun hc => by simp [isCasc, h] at hc)⟩

/-- every position of the run: the start event, the root call's segment, the term event -/
theorem posOK_run {G : Graph n} {s t : Fin n} {k : Nat} {T : List (Ev n)} {N : List (List (Fin n))} {b : Vector Nat n} {σ σ' : Nat} (tc : TrCall G s t k 0 s #[] (Vector.replicate n 0) [Ev.start σ] N b T) :
    ∀ q, q < (T ++ [Ev.term σ']).length → PosOK G s t k (T ++ [Ev.term σ']) q := by
  intro q hq
  obtain ⟨σ0, E, hE, -⟩ := tc.ext
  simp only [List.length_append, List.length_singleton] at hq
  rcases Nat.lt_or_ge q 1 with h0 | h0
  · rw [show q = 0 by omega]
    exact posOK_start (σ := σ) (by rw [List.getElem?_append_left (by rw [hE]; simp), hE]; simp)
  rcases Nat.lt_or_ge q T.length with hq' | hq'
  · exact (tc.seg q (by simpa using h0) hq').append hq'
  · exact posOK_term (σ := σ') (by rw [show q = T.length by omega]; simp)

/-- the root call's `TrCall` gives properties of the whole run -/
theorem bsdfs_of_trCall (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) (Q : List (Ev n) → Prop)
    (hQ : ∀ N b T σ', TrCall G s t k 0 s #[] (Vector.replicate n 0) [Ev.start 0] N b T → Q (T ++ [Ev.term σ'])) : Q (bsdfs G s t k) := by
  refine bsdfs_of_root (fun st => st.S = #[] ∧ st.b = Vector.replicate n 0 ∧ st.trace.toList = [Ev.start 0] ∧ SearchPre G s t k 0 s #[] (Vector.replicate n 0) ∧ TrPre 0 #[] (Vector.replicate n 0) [Ev.start 0]) Q
    ⟨rfl, rfl, rfl, root_pre hst, root_tr⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  obtain ⟨-, N, -, tc⟩ := (StateM.triple_iff _ _ _).mp (search_spec_tr G hG s t k 0 s #[] (Vector.replicate n 0) [Ev.start 0]) st hpre
  exact hQ _ _ _ _ tc

/-- Stage 3c: the run satisfies `RunFacts` -/
theorem bsdfs_runFacts (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) : RunFacts G s t k (bsdfs G s t k) :=
  bsdfs_of_trCall G s t k hG hst _ fun _ _ _ _ tc => runFacts_of_posOK (posOK_run tc)

variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- worst case (v3, thm:worst-case-delay): every interval (o_τ, o_{τ+1}] costs at most 2k(n + m) steps -/
theorem bsdfs_worst_case_delay (hG : G.WF) (hst : s ≠ t) (hk : 0 < k) : ∀ x ∈ (obsSteps (bsdfs G s t k)).zip (obsSteps (bsdfs G s t k)).tail, x.2 - x.1 ≤ 2 * k * (n + G.m) :=
  worst_case_of_run G s t k hG hk (bsdfs_runFacts G s t k hG hst)

/-- Two Entries per Pair (cor:two-entries): between consecutive observable events a < c, every node z is entered at most twice
    at the same depth h, at most once in the descent and once in the ascent (One Entry per Pair per Phase) -/
theorem RunFacts.two_entries {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)} (hR : RunFacts G s t k tr) {a c : Nat} (hC : Consec tr a c) (z : Fin n) (h : Nat) :
    cnt (fun q => enterAt tr z q = true ∧ depthOf tr q = h) a c ≤ 2 := by
  obtain ⟨m, β, hS⟩ := shape_exists hC
  have hI := hR.intervalFacts hC hS
  -- two such entries in the same phase are one
  have one : ∀ q₁ q₂, enterAt tr z q₁ = true ∧ depthOf tr q₁ = h → enterAt tr z q₂ = true ∧ depthOf tr q₂ = h →
      ((a < q₁ ∧ q₁ ≤ β ∧ a < q₂ ∧ q₂ ≤ β) ∨ (β < q₁ ∧ q₁ ≤ c ∧ β < q₂ ∧ q₂ ≤ c)) → q₁ = q₂ := by
    intro q₁ q₂ ⟨e₁, d₁⟩ ⟨e₂, d₂⟩ hph
    obtain ⟨σ₁, h₁, he₁⟩ := Trace.enterAt_iff.mp e₁
    obtain ⟨σ₂, h₂, he₂⟩ := Trace.enterAt_iff.mp e₂
    rw [DelayFacts.depthOf_enter he₁] at d₁
    rw [DelayFacts.depthOf_enter he₂] at d₂
    rw [d₁] at he₁
    rw [d₂] at he₂
    exact Decidable.byContradiction fun hne => hI.one_entry q₁ q₂ σ₁ σ₂ z h hne hph he₁ he₂
  have hd := Trace.cnt_le_one (fun q => enterAt tr z q = true ∧ depthOf tr q = h) (lo := a) (hi := β) fun q₁ q₂ a1 b1 a2 b2 p1 p2 => one q₁ q₂ p1 p2 (Or.inl ⟨a1, b1, a2, b2⟩)
  have ha := Trace.cnt_le_one (fun q => enterAt tr z q = true ∧ depthOf tr q = h) (lo := β) (hi := c) fun q₁ q₂ a1 b1 a2 b2 p1 p2 => one q₁ q₂ p1 p2 (Or.inr ⟨a1, b1, a2, b2⟩)
  rw [Trace.cnt_split _ hS.le (Nat.le_of_lt hS.lt)]
  omega

/-- Two Entries per Pair (cor:two-entries) for the run of `bsdfs` -/
theorem bsdfs_two_entries (hG : G.WF) (hst : s ≠ t) {a c : Nat} (hC : Consec (bsdfs G s t k) a c) (z : Fin n) (h : Nat) :
    cnt (fun q => enterAt (bsdfs G s t k) z q = true ∧ depthOf (bsdfs G s t k) q = h) a c ≤ 2 :=
  (bsdfs_runFacts G s t k hG hst).two_entries hC z h

/-- Edge Scans (proposed corollary of Interval Budget): in every interval (a, c], every edge (x, y) is scanned at most 2k times,
    forward by calls at x and backward by dequeues of y.  The trace has no scan events, so the statement counts what does the
    scanning: the calls at x entered in the interval, the spine frame of x if it is open at a, and the dequeues of y; this is
    `edge_budget` for the run.  That these bound the scans executed in the interval is the paper's argument, not checked here:
    a call scans (x, y) at most once over its lifetime, at most one call at x is open at a, and every cascade runs to completion
    inside the descent. -/
theorem bsdfs_edge_scans (hG : G.WF) (hst : s ≠ t) (hk : 0 < k) {a c : Nat} (hC : Consec (bsdfs G s t k) a c) {x y : Fin n} (hxy : y ∈ G.succ x) :
    cnt (fun q => enterAt (bsdfs G s t k) x q = true) a c + cnt (fun q => deqAt (bsdfs G s t k) y q = true) a c + (if x ∈ stk (bsdfs G s t k) a then 1 else 0) ≤ 2 * k := by
  obtain ⟨m, β, hS⟩ := shape_exists hC
  exact (bsdfs_runFacts G s t k hG hst).toDelayFacts.edge_budget hC hS hk hxy
