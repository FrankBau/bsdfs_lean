/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Basic
import Bsdfs.Positions

/-!
  Attribution of Work (sec:work-attribution) for the step counter: charge every call its entry and all its successor scans at
  its `enter` event, every dequeue itself and all its predecessor scans at its `dequeue` event, and every output its length.
  Then the stamp σ of every observable event satisfies  σ ≤ cost(trace up to it) ≤ σ + owed,  where owed are the scans the
  frames open at that event still have to do, at most the out-degrees of the spine less t.  Hence the steps between two
  observable events are at most the cost of the events between them plus the owed scans of the first one (`tally`).
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

/-- the cost charged to an event -/
def Graph.evCost (G : Graph n) : Ev n → Nat
  | .enter _ v _ => 1 + (G.succ v).length
  | .dequeue _ q _ => 1 + (G.pred q).length
  | .output _ p => p.length
  | _ => 0

def Graph.cost (G : Graph n) (tr : List (Ev n)) : Nat := (tr.map G.evCost).sum

-- `Ev.obs`, the step stamp of an observable event (start, output, term), is defined in Bsdfs/Positions.lean

/-- scans still owed by the frames open at an observable event: at most the out-degrees of the spine less t -/
def Graph.owed (G : Graph n) : Ev n → Nat
  | .output _ p => (p.dropLast.map fun v => (G.succ v).length).sum
  | _ => 0

/-- every observable event's stamp lies between the cost up to it, less the owed scans, and that cost -/
def Graph.StampOK (G : Graph n) (tr : List (Ev n)) : Prop :=
  ∀ i (hi : i < tr.length) σ, tr[i].obs = some σ → σ ≤ G.cost (tr.take (i + 1)) ∧ G.cost (tr.take (i + 1)) ≤ σ + G.owed tr[i]

@[simp] theorem Ev.obs_start (s : Nat) : (Ev.start s : Ev n).obs = some s := rfl
@[simp] theorem Ev.obs_output (s : Nat) (p : List (Fin n)) : (Ev.output s p).obs = some s := rfl
@[simp] theorem Ev.obs_term (s : Nat) : (Ev.term s : Ev n).obs = some s := rfl
@[simp] theorem Ev.obs_enter (s : Nat) (v : Fin n) (h : Nat) : (Ev.enter s v h).obs = none := rfl
@[simp] theorem Ev.obs_exit (s : Nat) (v : Fin n) (h sd : Nat) (f : Bool) : (Ev.exit s v h sd f).obs = none := rfl
@[simp] theorem Ev.obs_cascade (s : Nat) (v : Fin n) (sd : Nat) : (Ev.cascade s v sd).obs = none := rfl
@[simp] theorem Ev.obs_dequeue (s : Nat) (q : Fin n) (d : Nat) : (Ev.dequeue s q d).obs = none := rfl
@[simp] theorem Ev.obs_write (s : Nat) (x : Fin n) (o nw : Nat) (kd : Kind) : (Ev.write s x o nw kd).obs = none := rfl

section
variable {G : Graph n}

@[simp] theorem Graph.evCost_enter (s : Nat) (v : Fin n) (h : Nat) : G.evCost (.enter s v h) = 1 + (G.succ v).length := rfl
@[simp] theorem Graph.evCost_dequeue (s : Nat) (q : Fin n) (d : Nat) : G.evCost (.dequeue s q d) = 1 + (G.pred q).length := rfl
@[simp] theorem Graph.evCost_output (s : Nat) (p : List (Fin n)) : G.evCost (.output s p) = p.length := rfl
@[simp] theorem Graph.evCost_start (s : Nat) : G.evCost (.start s) = 0 := rfl
@[simp] theorem Graph.evCost_term (s : Nat) : G.evCost (.term s) = 0 := rfl
@[simp] theorem Graph.evCost_exit (s : Nat) (v : Fin n) (h sd : Nat) (f : Bool) : G.evCost (.exit s v h sd f) = 0 := rfl
@[simp] theorem Graph.evCost_cascade (s : Nat) (v : Fin n) (sd : Nat) : G.evCost (.cascade s v sd) = 0 := rfl
@[simp] theorem Graph.evCost_write (s : Nat) (x : Fin n) (o nw : Nat) (kd : Kind) : G.evCost (.write s x o nw kd) = 0 := rfl

@[simp] theorem Graph.cost_cons (e : Ev n) (l : List (Ev n)) : G.cost (e :: l) = G.evCost e + G.cost l := by
  simp [Graph.cost]

@[simp] theorem Graph.cost_nil : G.cost [] = 0 := rfl

@[simp] theorem Graph.cost_append (l₁ l₂ : List (Ev n)) : G.cost (l₁ ++ l₂) = G.cost l₁ + G.cost l₂ := by
  simp [Graph.cost]

@[simp] theorem Graph.cost_singleton (e : Ev n) : G.cost [e] = G.evCost e := by
  simp [Graph.cost]

theorem Graph.StampOK.nil : G.StampOK [] := by
  intro i hi; simp at hi

theorem Graph.StampOK.snoc {tr : List (Ev n)} {e : Ev n} (h : G.StampOK tr) (he : ∀ σ, e.obs = some σ → σ ≤ G.cost tr + G.evCost e ∧ G.cost tr + G.evCost e ≤ σ + G.owed e) : G.StampOK (tr ++ [e]) := by
  intro i hi σ hσ
  rcases Nat.lt_or_ge i tr.length with hlt | hge
  · have e1 : (tr ++ [e])[i] = tr[i] := List.getElem_append_left hlt
    have e2 : (tr ++ [e]).take (i + 1) = tr.take (i + 1) := List.take_append_of_le_length (by omega)
    simp only [e1, e2] at hσ ⊢
    exact h i hlt σ hσ
  · have hi2 : i < tr.length + 1 := by simpa using hi
    have hi' : i = tr.length := by omega
    subst hi'
    have e1 : (tr ++ [e])[tr.length] = e := by simp
    have e2 : (tr ++ [e]).take (tr.length + 1) = tr ++ [e] := List.take_of_length_le (by simp)
    simp only [e1, e2] at hσ ⊢
    simpa using he σ hσ

/-- appending an event that is not observable -/
theorem Graph.StampOK.snoc_hidden {tr : List (Ev n)} {e : Ev n} (h : G.StampOK tr) (he : e.obs = none) : G.StampOK (tr ++ [e]) :=
  h.snoc (by intro σ hσ; rw [he] at hσ; cases hσ)

end

section
variable {G : Graph n}

/-- appending a hidden event does not change `StampOK` -/
theorem Graph.stampOK_snoc_hidden {tr : List (Ev n)} {e : Ev n} (he : e.obs = none) : G.StampOK (tr ++ [e]) ↔ G.StampOK tr := by
  refine ⟨fun h i hi σ hσ => ?_, fun h => h.snoc_hidden he⟩
  have e1 : (tr ++ [e])[i]'(by simp; omega) = tr[i] := List.getElem_append_left hi
  have e2 : (tr ++ [e]).take (i + 1) = tr.take (i + 1) := List.take_append_of_le_length (by omega)
  have := h i (by simp; omega) σ (by rw [e1]; exact hσ)
  simp only [e1, e2] at this
  exact this

/-- appending hidden events does not change `StampOK` -/
@[simp] theorem Graph.stampOK_append_hidden {l : List (Ev n)} (hl : ∀ e ∈ l, e.obs = none) {tr : List (Ev n)} : G.StampOK (tr ++ l) ↔ G.StampOK tr := by
  induction l generalizing tr with
  | nil => simp
  | cons e l ih =>
    have e1 : tr ++ e :: l = (tr ++ [e]) ++ l := by simp
    rw [e1, ih (fun e' he' => hl e' (by simp [he'])), Graph.stampOK_snoc_hidden (hl e (by simp))]

end

/-- the cascade keeps cost − steps and `StampOK` -/
theorem fruitful_cost (G : Graph n) (v : Fin n) (sd : Nat) (S1 : Array (Fin n)) (steps0 c0 : Nat) :
    ⦃fun st => ⌜st.S = S1 ∧ st.steps = steps0 ∧ G.cost st.trace.toList = c0 ∧ G.StampOK st.trace.toList⌝⦄
    fruitful G v sd
    ⦃⇓ _ st => ⌜st.S = S1 ∧ G.cost st.trace.toList + steps0 = st.steps + c0 ∧ G.StampOK st.trace.toList⌝⦄ := by
  mvcgen [fruitful, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack] invariants
  · ⇓⟨_, _⟩ st => ⌜st.S = S1 ∧ G.cost st.trace.toList + steps0 = st.steps + c0 ∧ G.StampOK st.trace.toList⌝
  · ⇓⟨xs, _⟩ st => ⌜st.S = S1 ∧ G.cost st.trace.toList + steps0 = st.steps + c0 + xs.suffix.length ∧ G.StampOK st.trace.toList⌝
  all_goals (simp_all +zetaDelta; try omega)

/-- out-degree sum of a list of nodes -/
def Graph.outSum (G : Graph n) (L : List (Fin n)) : Nat := (L.map fun u => (G.succ u).length).sum

@[simp] theorem Graph.outSum_append (G : Graph n) (L₁ L₂ : List (Fin n)) : G.outSum (L₁ ++ L₂) = G.outSum L₁ + G.outSum L₂ := by
  simp [Graph.outSum]

@[simp] theorem Graph.outSum_singleton (G : Graph n) (v : Fin n) : G.outSum [v] = (G.succ v).length := by
  simp [Graph.outSum]

theorem Graph.owed_output (G : Graph n) (s : Nat) (p : List (Fin n)) : G.owed (.output s p) = G.outSum p.dropLast := rfl

/-- appending the output L ++ [v, t] made in the loop of v keeps `StampOK` -/
theorem Graph.StampOK.output {G : Graph n} {tr : List (Ev n)} {L : List (Fin n)} {v t : Fin n} {σ1 r c0 steps0 : Nat} (hok : G.StampOK tr) (hinv : G.cost tr + steps0 = σ1 + c0 + (r + 1)) (hr : r + 1 ≤ (G.succ v).length) (hle : steps0 ≤ c0) (hc0 : c0 ≤ steps0 + G.outSum L) :
    G.StampOK (tr ++ [.output (σ1 + 1 + (L.length + 2)) (L ++ [v, t])]) := by
  apply hok.snoc
  intro σ' hσ'
  simp only [Ev.obs_output, Option.some.injEq] at hσ'
  subst hσ'
  have hd : (L ++ [v, t]).dropLast = L ++ [v] := by
    rw [show L ++ [v, t] = (L ++ [v]) ++ [t] by simp, List.dropLast_concat]
  simp only [Graph.evCost_output, Graph.owed_output, hd, Graph.outSum_append, Graph.outSum_singleton, List.length_append, List.length_cons, List.length_nil]
  omega

/-- `search v h` with stack S0 spends exactly what its events are charged, and keeps `StampOK`; induction on k - h -/
theorem search_cost (G : Graph n) (t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) (steps0 c0 : Nat) :
    ⦃fun st => ⌜st.S = S0 ∧ st.steps = steps0 ∧ G.cost st.trace.toList = c0 ∧ S0.size = h ∧ h ≤ k ∧ steps0 ≤ c0 ∧ c0 ≤ steps0 + G.outSum S0.toList ∧ G.StampOK st.trace.toList⌝⦄
    search G t k v h
    ⦃⇓ _ st => ⌜st.S = S0 ∧ G.cost st.trace.toList + steps0 = st.steps + c0 ∧ G.StampOK st.trace.toList⌝⦄ := by
  -- spec of the recursive call; vacuous unless h < k
  have ih : ∀ w (S1 : Array (Fin n)) (steps1 c1 : Nat), ⦃fun st => ⌜st.S = S1 ∧ st.steps = steps1 ∧ G.cost st.trace.toList = c1 ∧ S1.size = h + 1 ∧ h + 1 ≤ k ∧ steps1 ≤ c1 ∧ c1 ≤ steps1 + G.outSum S1.toList ∧ G.StampOK st.trace.toList⌝⦄ search G t k w (h + 1) ⦃⇓ _ st => ⌜st.S = S1 ∧ G.cost st.trace.toList + steps1 = st.steps + c1 ∧ G.StampOK st.trace.toList⌝⦄ := by
    intro w S1 steps1 c1
    by_cases hk : h < k
    · exact search_cost G t k (h + 1) w S1 steps1 c1
    · intro st hP
      exact absurd hP.2.2.2.2.1 (by omega)
  have hcasc := fruitful_cost G v
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, ih, hcasc] invariants
  · ⇓⟨xs, _⟩ st => ⌜st.S = S0.push v ∧ G.cost st.trace.toList + steps0 = st.steps + c0 + xs.suffix.length ∧ G.StampOK st.trace.toList⌝
  case vc1.step.isTrue.isTrue =>
    -- closing edge (v, t): the output's stamp against its cost
    obtain ⟨-, -, -, hsz, -, hle, hc0, -⟩ := ‹_ = S0 ∧ _ = steps0 ∧ _ = c0 ∧ S0.size = h ∧ _›
    obtain ⟨hS, hinv, hok⟩ := ‹_ = S0.push v ∧ _ ∧ G.StampOK _›
    have hl := congrArg List.length ‹G.succ v = _ ++ _ :: _›
    simp only [List.length_append, List.length_cons] at hl
    have hL : S0.toList.length = h := by simpa using hsz
    simp +zetaDelta only
    rw [hS]
    simp only [Array.toList_push, Graph.cost_append, Graph.cost_singleton, Graph.evCost_output, List.length_append, List.length_cons, List.append_assoc, List.cons_append, List.nil_append]
    simp only [List.length_cons] at hinv
    refine ⟨trivial, by simp only [List.length_nil]; omega, ?_⟩
    rw [← hL]
    exact hok.output hinv (by omega) hle hc0
  all_goals (simp_all +zetaDelta; try omega)
termination_by k - h

/-- the whole run keeps `StampOK` -/
theorem bsdfs_stamps (G : Graph n) (s t : Fin n) (k : Nat) : G.StampOK (bsdfs G s t k) := by
  -- after the start event: stamp 0, cost 0; at the term event: stamp = steps = cost
  refine bsdfs_of_root (fun st => st.S = #[] ∧ st.steps = 0 ∧ G.cost st.trace.toList = 0 ∧ (#[] : Array (Fin n)).size = 0 ∧ 0 ≤ k ∧ 0 ≤ 0 ∧ 0 ≤ 0 + G.outSum (#[] : Array (Fin n)).toList ∧ G.StampOK st.trace.toList) G.StampOK
    ⟨rfl, rfl, by simp, rfl, Nat.zero_le k, Nat.le_refl 0, Nat.zero_le _, Graph.StampOK.nil.snoc (by intro σ hσ; simp at hσ; subst hσ; simp)⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  obtain ⟨-, hc, hok⟩ := (StateM.triple_iff _ _ _).mp (search_cost G t k 0 s #[] 0 0) st hpre
  exact hok.snoc (by intro σ hσ; simp at hσ; subst hσ; simp [Graph.owed]; omega)

/-- the tally: between any two observable events of the run, the steps are at most the cost of the events in between plus the
    scans owed at the first one -/
theorem tally (G : Graph n) (s t : Fin n) (k : Nat) {i j : Nat} (hij : i < j) (hj : j < (bsdfs G s t k).length) {σi σj : Nat}
    (hσi : ((bsdfs G s t k)[i]'(by omega)).obs = some σi) (hσj : ((bsdfs G s t k)[j]'hj).obs = some σj) :
    σj ≤ σi + G.cost (((bsdfs G s t k).drop (i + 1)).take (j - i)) + G.owed ((bsdfs G s t k)[i]'(by omega)) := by
  have hok := bsdfs_stamps G s t k
  have h1 := (hok i (by omega) σi hσi).2
  have h2 := (hok j hj σj hσj).1
  have e : (bsdfs G s t k).take (j + 1) = (bsdfs G s t k).take (i + 1) ++ ((bsdfs G s t k).drop (i + 1)).take (j - i) := by
    rw [← List.take_add]; congr 1; omega
  rw [e, Graph.cost_append] at h2
  omega
