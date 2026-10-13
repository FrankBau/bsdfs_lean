import Bsdfs.Gate

/-!
  Lower bounds, part 3: the clique trap G_c of bsdfs.tex (the complete digraph on c nodes, s among them, t isolated).  No call
  is fruitful, so the run is a single sweep of the block from s, and obsSteps = [0, c · N(c, k)].
-/

open Std.Do

set_option mvcgen.warning false

section clique
variable (c : Nat)

/-- the block: nodes 0 .. c - 1 -/
def cBlk : List (Fin (c + 1)) := (List.finRange c).map Fin.castSucc

/-- successors in scan order: the other block nodes in index order; t = c has none -/
def cliqueSucc (v : Fin (c + 1)) : List (Fin (c + 1)) := if v.val < c then (cBlk c).filter (· ≠ v) else []

def cliquePred (v : Fin (c + 1)) : List (Fin (c + 1)) := (List.finRange (c + 1)).filter (fun u => v ∈ cliqueSucc c u)

/-- the clique trap G_c: the complete digraph on c nodes and an isolated target -/
def clique : Graph (c + 1) := ⟨cliqueSucc c, cliquePred c⟩

def cS : Fin (c + 1) := ⟨0, by omega⟩
def cT : Fin (c + 1) := ⟨c, by omega⟩

theorem cBlk_length : (cBlk c).length = c := by simp [cBlk]

theorem cBlk_val (i : Nat) (hi : i < (cBlk c).length) : ((cBlk c)[i]).val = i := by simp [cBlk]

theorem cBlk_nodup : (cBlk c).Nodup :=
  List.Pairwise.map Fin.castSucc (fun a b hab he => hab (by simpa [Fin.ext_iff] using he)) (List.nodup_finRange c)

theorem mem_cBlk (z : Fin (c + 1)) : z ∈ cBlk c ↔ z.val < c := by
  simp only [cBlk, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩; simp
  · intro h; exact ⟨⟨z.val, h⟩, by ext; simp⟩

theorem cT_not_blk : cT c ∉ cBlk c := by simp [mem_cBlk, cT]

theorem cS_eq (hc : 1 ≤ c) : cS c = (cBlk c)[0]'(by rw [cBlk_length]; omega) := by ext; simp [cS, cBlk_val]

theorem clique_succ_B (i : Nat) (hi : i < (cBlk c).length) : (clique c).succ (cBlk c)[i] = (cBlk c).take i ++ (cBlk c).drop (i + 1) ++ [] := by
  show cliqueSucc c (cBlk c)[i] = _
  have hv : ((cBlk c)[i]).val < c := by rw [cBlk_val]; rw [cBlk_length] at hi; exact hi
  rw [cliqueSucc, ite_eq_left hv, List.append_nil]
  exact (cBlk_nodup c).filter_ne_getElem hi

theorem clique_wf : (clique c).WF where
  succ_nodup := by
    intro u
    show (cliqueSucc c u).Nodup
    unfold cliqueSucc
    split
    · exact (cBlk_nodup c).filter _
    · exact List.nodup_nil
  pred_nodup := fun v => (List.nodup_finRange _).filter _
  rev := by intro u v; simp [clique, cliquePred]

theorem clique_m : (clique c).m = c * (c - 1) := by
  unfold Graph.m
  rw [List.finRange_succ_last, List.map_append, List.sum_append]
  have hb : (((List.finRange c).map Fin.castSucc).map fun v => ((clique c).succ v).length).sum = (c - 1) * c := by
    rw [show (List.finRange c).map Fin.castSucc = cBlk c from rfl, sum_map_const _ _ (c - 1), cBlk_length]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    rw [clique_succ_B c i hi]
    simp [cBlk_length] at hi ⊢
    omega
  have hl : ((clique c).succ (Fin.last c)).length = 0 := by
    show (cliqueSucc c (Fin.last c)).length = 0
    simp [cliqueSucc]
  rw [hb]
  simp [hl, Nat.mul_comm]

/-- n + m of G_c -/
theorem clique_size (hc : 1 ≤ c) : c + 1 + (clique c).m = c * c + 1 := by
  rw [clique_m]
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nat_poly

/-- the clique trap of bsdfs.tex: no output, the term event after c · N(c, k) steps -/
theorem clique_run (k : Nat) (hc : 1 ≤ c) : obsSteps (bsdfs (clique c) (cS c) (cT c) k) = [0, c * sweepCalls c k 0] := by
  have hpos : 0 < (cBlk c).length := by rw [cBlk_length]; omega
  have ctx : SweepCtx (clique c) (cT c) k (cBlk c) [] [] 0 0 k :=
    { nodup := cBlk_nodup c, t_blk := cT_not_blk c, t_X := by simp, succ := clique_succ_B c, X_blk := by simp, P_blk := by simp, P_len := rfl, bound := by omega }
  have hsw := sweep_spec (clique c) (cT c) k (cBlk c) [] [] 0 0 k ctx 0 (Nat.zero_le _) hpos #[] (Vector.replicate (c + 1) 0) 0 [Ev.start 0]
  simp only [Nat.add_zero] at hsw
  refine bsdfs_of_root (fun st => st.S = #[] ∧ st.b = Vector.replicate (c + 1) 0 ∧ st.steps = 0 ∧ st.trace.toList = [Ev.start 0]) (fun T => obsSteps T = [0, c * sweepCalls c k 0]) ⟨rfl, rfl, rfl, rfl⟩ ?_
  refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
  obtain ⟨-, -, -, -, hσ, E, hE, hobs⟩ := (StateM.triple_iff _ _ _).mp hsw st ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2, rfl, fun j hj _ => by simp, by simp⟩
  -- the start event, the sweep, the term event
  rw [cS_eq c hc, hE, hσ, obsSteps_append, obsSteps_append, hobs, cBlk_length]
  simp [obsSteps]

end clique
