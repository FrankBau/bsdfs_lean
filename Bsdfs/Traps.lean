/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.BsdfsExec

/-!
  The example graphs of the lower bounds and the counts in their statements, definitions only.  Together with
  `Bsdfs/BsdfsExec.lean` this is everything the statements in `Bsdfs/Challenge.lean` refer to.  The facts about these
  definitions are proved in `Bsdfs/Sweep.lean`, `Bsdfs/GateRun.lean`, `Bsdfs/Gate.lean`, `Bsdfs/Clique.lean` and
  `Bsdfs/Tightness.lean`.
-/

/-! ## The gate trap Γ_c (gate_family.tex)

  Nodes s, q, t, g = 0 .. 3 and the block B_0 .. B_{c-1} = 4 .. c + 3; successors in scan order: s: q, g; q: t, g, B_0, …;
  g: B_0, q, s; B_i: the other block nodes in index order, then g. -/

section gate
variable (c : Nat)

def gS : Fin (c + 4) := ⟨0, by omega⟩
def gQ : Fin (c + 4) := ⟨1, by omega⟩
def gT : Fin (c + 4) := ⟨2, by omega⟩
def gG : Fin (c + 4) := ⟨3, by omega⟩

/-- the block B_0 .. B_{c-1}: nodes 4 .. c + 3 -/
def gBlk : List (Fin (c + 4)) := (List.finRange c).map (fun i => i.addNat 4)

def gateSucc (v : Fin (c + 4)) : List (Fin (c + 4)) :=
  if v.val = 0 then [gQ c, gG c]
  else if v.val = 1 then gT c :: gG c :: gBlk c
  else if v.val = 2 then []
  else if v.val = 3 then (gBlk c).take 1 ++ [gQ c, gS c]
  else (gBlk c).filter (· ≠ v) ++ [gG c]

def gatePred (v : Fin (c + 4)) : List (Fin (c + 4)) := (List.finRange (c + 4)).filter (fun u => v ∈ gateSucc c u)

/-- the gate trap Γ_c -/
def gate : Graph (c + 4) := ⟨gateSucc c, gatePred c⟩

end gate

/-! ## The clique trap G_c (bsdfs.tex): the complete digraph on c nodes, s among them, t isolated -/

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

end clique

/-! ## The counts -/

/-- the calls of a sweep from the first call at relative depth h: 1 + Σ_{d = h+1}^{min(L, c-1)} (c - d) -/
def sweepCalls (c L h : Nat) : Nat := 1 + ((List.range' (h + 1) (min L (c - 1) - h)).map (fun d => c - d)).sum

/-- o_2 - o_1 on a gate trap with block size c: two sweeps of the block, re-armed by the cascade in between -/
def gateD1 (c k : Nat) : Nat := (c + 1) * (sweepCalls c (k - 3) 0 + sweepCalls c (k - 5) 0) + 3 * c * c + 4 * c + 21
