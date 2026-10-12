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

/-- Stage 3c: the run satisfies `RunFacts` -/
theorem bsdfs_runFacts (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hst : s ≠ t) : RunFacts G s t k (bsdfs G s t k) := by
  have hroot := search_spec_tr G hG s t k 0 s #[] (Vector.replicate n 0)
  unfold bsdfs
  dsimp only
  generalize hx : StateT.run _ _ = x
  have key : ∀ q, q < x.2.trace.toList.length → PosOK G s t k x.2.trace.toList q := by
    refine StateM.of_wp_run_eq hx (fun x => ∀ q, q < x.2.trace.toList.length → PosOK G s t k x.2.trace.toList q) ?_
    mvcgen [M.tick, M.emit, M.steps, hroot]
    case vc1.pre =>
      -- root call: empty stack, barriers 0, the start event
      simp +zetaDelta only
      refine ⟨?_, ?_, ?_, root_pre hst, ?_⟩
      · simp
      · simp
      · simp
      · simpa using root_tr
    case vc2.post.success =>
      -- every position of the run: the start event, the root call's segment, the term event
      obtain ⟨-, N, -, tc⟩ := ‹_ = #[] ∧ ∃ N, SearchPost G s t k 0 s #[] _ _ _ N ∧ TrCall G s t k 0 s #[] _ _ N _ _›
      simp +zetaDelta only at tc ⊢
      rw [Array.toList_push]
      exact posOK_run (by simpa using tc)
  have hx' : x.run.snd.trace.toList = x.2.trace.toList := rfl
  rw [hx']
  exact runFacts_of_posOK key

variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- worst case (v3, thm:worst-case-delay): every interval (o_τ, o_{τ+1}] costs at most 2k(n + m) steps -/
theorem bsdfs_worst_case_delay (hG : G.WF) (hst : s ≠ t) (hk : 0 < k) : ∀ x ∈ (obsSteps (bsdfs G s t k)).zip (obsSteps (bsdfs G s t k)).tail, x.2 - x.1 ≤ 2 * k * (n + G.m) :=
  worst_case_of_run G s t k hG hk (bsdfs_runFacts G s t k hG hst)
