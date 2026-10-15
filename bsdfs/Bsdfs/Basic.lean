/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.BsdfsExec
import Std.Tactic.Do

/-!
  Generic facts used by several proof files: the loop cursor of `mvcgen` (a list split as `pref ++ cur :: suff`), the tactic
  `nat_poly` for polynomial arithmetic, Hoare triples over `StateM` as statements about the run, and `bsdfs_of_root`: a property
  of the trace of `bsdfs` from a spec of the root call.
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

/-! ## The loop cursor -/

section split
variable {α : Type} {xs pref suff : List α} {cur : α}

theorem mem_of_eq_append_cons (h : xs = pref ++ cur :: suff) : cur ∈ xs := by simp [h]

theorem not_mem_of_nodup_split (hnd : xs.Nodup) (h : xs = pref ++ cur :: suff) : cur ∉ pref := by
  rw [h] at hnd
  intro hc
  exact (List.nodup_append.mp hnd).2.2 cur hc cur (by simp) rfl

theorem eq_append_cons_idx (h : xs = pref ++ cur :: suff) : ∃ hp : pref.length < xs.length, xs[pref.length] = cur :=
  ⟨by simp [h], List.getElem_of_append h rfl⟩

end split

/-- the cursor of `for i in List.range n` is the number of iterations so far -/
theorem range_eq_append_cons {pref suff : List Nat} {cur : Nat} (h : List.range n = pref ++ cur :: suff) : cur = pref.length := by
  obtain ⟨hp, he⟩ := eq_append_cons_idx h
  simpa using he.symm

/-! ## Arithmetic -/

/-- (in)equalities between polynomials over Nat, without Mathlib: distribute, sort the factors of every product (numerals last),
    then `omega` with the products as atoms -/
macro "nat_poly" : tactic => `(tactic| ((try simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at *); (try simp only [← Nat.mul_assoc] at *); omega))

/-! ## Hoare triples and the run -/

/-- a Hoare triple over `StateM` is a statement about the run, by definition -/
theorem StateM.triple_iff {σ α : Type} (x : StateM σ α) (P : σ → Prop) (Q : α → σ → Prop) :
    ⦃fun s => ⌜P s⌝⦄ x ⦃⇓ r s => ⌜Q r s⌝⦄ ↔ ∀ s, P s → Q (x.run s).1 (x.run s).2 :=
  ⟨fun h s hs => h s hs, fun h s hs => h s hs⟩

/-- the trace of `bsdfs` is the start event at step 0, the trace of the root call, and the term event: a spec of the root call
    from the state after the start event gives a property of the whole trace -/
theorem bsdfs_of_root {G : Graph n} {s t : Fin n} {k : Nat} (P : St n → Prop) (Q : List (Ev n) → Prop)
    (hpre : P ⟨Vector.replicate n 0, #[], 0, #[Ev.start 0]⟩)
    (hroot : ⦃fun st => ⌜P st⌝⦄ search G t k s 0 ⦃⇓ _ st => ⌜Q (st.trace.toList ++ [Ev.term st.steps])⌝⦄) : Q (bsdfs G s t k) := by
  unfold bsdfs
  dsimp only
  generalize hx : StateT.run _ _ = x
  refine StateM.of_wp_run_eq hx (fun x => Q x.2.trace.toList) ?_
  mvcgen [M.tick, M.emit, M.steps, hroot]
  simp +zetaDelta only [Array.toList_push]
  exact ‹Q _›
