import Bsdfs.DelayFacts

/-!
  Assembly of the worst-case bound from the per-node and per-edge budgets: the cost of an interval regrouped by nodes and edges
  (sec:work-attribution, (T3) of edge_budget.tex), the sum 2k(n-1) + 2k m + (k+1) ≤ 2k(n+m), and the link from `obsSteps` to
  consecutive observable events.
-/

open Trace

variable {n : Nat}

section sums
variable {α β : Type}

/-- sum of f over a list -/
def lsum (L : List α) (f : α → Nat) : Nat := (L.map f).sum

@[simp] theorem lsum_nil (f : α → Nat) : lsum [] f = 0 := rfl
@[simp] theorem lsum_cons (a : α) (L : List α) (f : α → Nat) : lsum (a :: L) f = f a + lsum L f := by simp [lsum]

theorem lsum_add (L : List α) (f g : α → Nat) : lsum L (fun a => f a + g a) = lsum L f + lsum L g := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [lsum_cons, ih]; omega

theorem lsum_le {L : List α} {f g : α → Nat} (h : ∀ a ∈ L, f a ≤ g a) : lsum L f ≤ lsum L g := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons a L ih => simp only [lsum_cons]; exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem lsum_mul (L : List α) (c : Nat) (f : α → Nat) : lsum L (fun a => c * f a) = c * lsum L f := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [lsum_cons, ih, Nat.mul_add]

theorem lsum_zero (L : List α) : lsum L (fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem lsum_const (L : List α) (c : Nat) : lsum L (fun _ => c) = c * L.length := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [lsum_cons, ih, List.length_cons, Nat.mul_add, Nat.mul_one]; omega

/-- exchange of a double sum -/
theorem lsum_comm (L : List α) (M : List β) (g : α → β → Nat) : lsum L (fun a => lsum M (g a)) = lsum M (fun b => lsum L (fun a => g a b)) := by
  induction L with
  | nil => simp [lsum_zero]
  | cons a L ih => simp only [lsum_cons, ih, lsum_add]

theorem lsum_ite_eq_zero [DecidableEq α] {M : List α} {x : α} (hx : x ∉ M) (g : α → Nat) : lsum M (fun y => if y = x then g y else 0) = 0 := by
  induction M with
  | nil => rfl
  | cons y M ih =>
    simp only [List.mem_cons, not_or] at hx
    simp [Ne.symm hx.1, ih hx.2]

theorem lsum_ite_eq [DecidableEq α] {M : List α} (hM : M.Nodup) {x : α} (hx : x ∈ M) (g : α → Nat) : lsum M (fun y => if y = x then g y else 0) = g x := by
  induction M with
  | nil => simp at hx
  | cons y M ih =>
    rw [List.nodup_cons] at hM
    simp only [lsum_cons]
    by_cases hyx : y = x
    · subst hyx; simp [lsum_ite_eq_zero hM.1]
    · have : x ∈ M := by simp at hx; rcases hx with h | h; exact absurd h.symm hyx; exact h
      simp [hyx, ih hM.2 this]

/-- a sum over a list without repetitions, as an indicator sum over a larger list without repetitions -/
theorem lsum_eq_ind [DecidableEq α] {L M : List α} (hL : L.Nodup) (hM : M.Nodup) (hLM : ∀ a ∈ L, a ∈ M) (g : α → Nat) : lsum L g = lsum M (fun y => if y ∈ L then g y else 0) := by
  induction L with
  | nil => simp [lsum_zero]
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    have hsplit : (fun y => if y ∈ x :: L then g y else 0) = (fun y => (if y = x then g y else 0) + (if y ∈ L then g y else 0)) := by
      funext y
      by_cases hyx : y = x
      · subst hyx; simp [hL.1]
      · simp [hyx]
    rw [hsplit, lsum_add, lsum_ite_eq hM (hLM x (by simp)), ← ih hL.2 (fun a ha => hLM a (by simp [ha]))]
    simp

end sums

/-- sum over all nodes -/
abbrev nsum (f : Fin n → Nat) : Nat := lsum (List.finRange n) f

theorem nsum_ite_eq (v : Fin n) (f : Fin n → Nat) : nsum (fun z => if z = v then f z else 0) = f v :=
  lsum_ite_eq (List.nodup_finRange n) (List.mem_finRange v) f

/-- double counting of edges: Σ_y |pred y| g(y) = Σ_x Σ_{y ∈ succ x} g(y) -/
theorem pred_sum (G : Graph n) (hG : G.WF) (g : Fin n → Nat) : nsum (fun y => (G.pred y).length * g y) = nsum (fun x => lsum (G.succ x) g) := by
  have h1 : ∀ y, (G.pred y).length * g y = nsum (fun x => if y ∈ G.succ x then g y else 0) := by
    intro y
    have := lsum_eq_ind (hG.pred_nodup y) (List.nodup_finRange n) (fun a _ => List.mem_finRange a) (fun _ => g y)
    rw [lsum_const] at this
    rw [Nat.mul_comm, this]
    congr 1; funext x
    simp only [(hG.rev x y).symm]
  have h2 : ∀ x, lsum (G.succ x) g = nsum (fun y => if y ∈ G.succ x then g y else 0) := fun x => lsum_eq_ind (hG.succ_nodup x) (List.nodup_finRange n) (fun a _ => List.mem_finRange a) g
  simp only [h1, h2]
  exact lsum_comm _ _ _

/-- a count as a sum of indicators -/
theorem lsum_countP (L : List Nat) (P : Nat → Bool) (c : Nat) : lsum L (fun q => if P q then c else 0) = c * L.countP P := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [lsum_cons, ih, List.countP_cons]
    split <;> simp [Nat.mul_add] <;> omega

theorem nsum_ite_ne (t : Fin n) (c : Nat) : nsum (fun z => if z = t then 0 else c) + c = c * n := by
  have h1 : nsum (fun z => if z = t then 0 else c) + nsum (fun z => if z = t then c else 0) = nsum (fun (_ : Fin n) => c) := by
    rw [← lsum_add]; congr 1; funext z; split <;> omega
  have h2 : nsum (fun z => if z = t then c else 0) = c := lsum_ite_eq (List.nodup_finRange n) (List.mem_finRange t) (fun _ => c)
  have h3 : nsum (fun (_ : Fin n) => c) = c * n := by simp [lsum_const]
  omega

/-- cost of the event at position q -/
def posCost (G : Graph n) (tr : List (Ev n)) (q : Nat) : Nat := match tr[q]? with | some e => G.evCost e | none => 0

/-- output cost at position q -/
def outCost (tr : List (Ev n)) (q : Nat) : Nat := match tr[q]? with | some (.output _ P) => P.length | _ => 0

theorem cost_drop_take (G : Graph n) (tr : List (Ev n)) : ∀ (j i : Nat), i + j ≤ tr.length → G.cost ((tr.drop i).take j) = lsum (List.range' i j) (posCost G tr)
  | 0, i, _ => by simp
  | j + 1, i, h => by
    have hi : i < tr.length := by omega
    have e1 : (tr.drop i).take (j + 1) = tr[i] :: (tr.drop (i + 1)).take j := by
      rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
    rw [e1, Graph.cost_cons, cost_drop_take G tr j (i + 1) (by omega), List.range'_succ, lsum_cons]
    simp [posCost, hi]

/-- the cost of one position, split into entry, dequeue and output parts -/
theorem posCost_split (G : Graph n) (tr : List (Ev n)) (q : Nat) : posCost G tr q = nsum (fun z => if enterAt tr z q = true then 1 + (G.succ z).length else 0) + nsum (fun z => if deqAt tr z q = true then 1 + (G.pred z).length else 0) + outCost tr q := by
  have hz : ∀ (c : Fin n → Nat), nsum (fun z => if False then c z else 0) = 0 := fun c => by simp [lsum_zero]
  unfold posCost outCost
  cases hq : tr[q]? with
  | none =>
    have e1 : ∀ z, enterAt tr z q = false := fun z => by simp [enterAt, hq]
    have e2 : ∀ z, deqAt tr z q = false := fun z => by simp [deqAt, hq]
    simp [e1, e2, lsum_zero]
  | some e =>
    cases e with
    | enter σ v h =>
      have e1 : (fun z => if enterAt tr z q = true then 1 + (G.succ z).length else 0) = (fun z => if z = v then 1 + (G.succ z).length else 0) := by
        funext z; by_cases hzv : z = v
        · subst hzv; simp [enterAt, hq]
        · simp [enterAt, hq, hzv, Ne.symm hzv]
      have e2 : ∀ z, deqAt tr z q = false := fun z => by simp [deqAt, hq]
      rw [e1, nsum_ite_eq]
      simp [e2, lsum_zero, Graph.evCost]
    | dequeue σ v d =>
      have e1 : ∀ z, enterAt tr z q = false := fun z => by simp [enterAt, hq]
      have e2 : (fun z => if deqAt tr z q = true then 1 + (G.pred z).length else 0) = (fun z => if z = v then 1 + (G.pred z).length else 0) := by
        funext z; by_cases hzv : z = v
        · subst hzv; simp [deqAt, hq]
        · simp [deqAt, hq, hzv, Ne.symm hzv]
      rw [e2, nsum_ite_eq]
      simp [e1, lsum_zero, Graph.evCost]
    | output σ P =>
      have e1 : ∀ z, enterAt tr z q = false := fun z => by simp [enterAt, hq]
      have e2 : ∀ z, deqAt tr z q = false := fun z => by simp [deqAt, hq]
      simp [e1, e2, lsum_zero, Graph.evCost]
    | _ =>
      have e1 : ∀ z, enterAt tr z q = false := fun z => by simp [enterAt, hq]
      have e2 : ∀ z, deqAt tr z q = false := fun z => by simp [deqAt, hq]
      simp [e1, e2, lsum_zero]

/-- the cost of a segment, regrouped by nodes: Σ_z (1 + |succ z|) E(z) + Σ_z (1 + |pred z|) D(z) + outputs -/
theorem lsum_posCost (G : Graph n) (tr : List (Ev n)) (lo hi : Nat) :
    lsum (List.range' (lo + 1) (hi - lo)) (posCost G tr) = nsum (fun z => (1 + (G.succ z).length) * cnt (fun q => enterAt tr z q = true) lo hi) + nsum (fun z => (1 + (G.pred z).length) * cnt (fun q => deqAt tr z q = true) lo hi) + lsum (List.range' (lo + 1) (hi - lo)) (outCost tr) := by
  have hsplit : posCost G tr = fun q => nsum (fun z => if enterAt tr z q = true then 1 + (G.succ z).length else 0) + nsum (fun z => if deqAt tr z q = true then 1 + (G.pred z).length else 0) + outCost tr q := funext (posCost_split G tr)
  rw [hsplit, lsum_add, lsum_add, lsum_comm, lsum_comm (g := fun q z => if deqAt tr z q = true then 1 + (G.pred z).length else 0)]
  congr 2
  · congr 1; funext z; rw [lsum_countP]; simp [cnt]
  · congr 1; funext z; rw [lsum_countP]; simp [cnt]

section bound
variable {G : Graph n} {s t : Fin n} {k : Nat} {tr : List (Ev n)}

/-- only the event at c can be an output in (a, c], and an output costs at most k + 1 -/
theorem out_le (hF : DelayFacts G s t k tr) {a c : Nat} (hC : Consec tr a c) : lsum (List.range' (a + 1) (c - a)) (outCost tr) ≤ k + 1 := by
  have hsplit : List.range' (a + 1) (c - a) = List.range' (a + 1) (c - a - 1) ++ [c] := by
    have := hC.lt
    obtain ⟨d, hd⟩ : ∃ d, c - a = d + 1 := ⟨c - a - 1, by omega⟩
    rw [hd, Nat.add_sub_cancel, List.range'_concat, show a + 1 + 1 * d = c by omega]
  have h0 : lsum (List.range' (a + 1) (c - a - 1)) (outCost tr) = 0 := by
    have : ∀ q ∈ List.range' (a + 1) (c - a - 1), outCost tr q = 0 := by
      intro q hq
      simp only [List.mem_range'_1] at hq
      have := hC.between q (by omega) (by omega)
      unfold outCost
      cases hq' : tr[q]? with
      | none => rfl
      | some e => cases e with
        | output σ P => simp [isObs, hq', Ev.obs] at this
        | _ => rfl
    have := lsum_le (L := List.range' (a + 1) (c - a - 1)) (f := outCost tr) (g := fun _ => 0) (fun q hq => Nat.le_of_eq (this q hq))
    rw [lsum_zero] at this; omega
  have hc : outCost tr c ≤ k + 1 := by
    unfold outCost
    cases hq' : tr[c]? with
    | none => simp
    | some e => cases e with
      | output σ P =>
        obtain ⟨hP, hlen⟩ := hF.output c σ P hq'
        simp [hP]; omega
      | _ => simp
  rw [hsplit, lsum, List.map_append, List.sum_append]
  simp only [lsum] at h0
  simp [h0]; exact hc

/-- the owed scans at an observable event a: the out-degrees of the stack, as an edge sum -/
theorem owed_le (hF : DelayFacts G s t k tr) {a : Nat} (ha : a < tr.length) : G.owed tr[a] ≤ nsum (fun x => lsum (G.succ x) (fun _ => if x ∈ stk tr a then 1 else 0)) := by
  have hrhs : nsum (fun x => lsum (G.succ x) (fun _ => if x ∈ stk tr a then 1 else 0)) = lsum (stk tr a) (fun v => (G.succ v).length) := by
    rw [lsum_eq_ind (hF.stk_nodup a) (List.nodup_finRange n) (fun x _ => List.mem_finRange x)]
    congr 1; funext x
    rw [lsum_const]; split <;> simp
  rw [hrhs]
  cases he : tr[a] with
  | output σ P =>
    obtain ⟨hP, -⟩ := hF.output a σ P (by rw [List.getElem?_eq_getElem ha, he])
    rw [Graph.owed_output, hP, List.dropLast_concat]
    exact Nat.le_refl _
  | _ => simp [Graph.owed]

/-- the interval bound (v3, thm:worst-case-delay): the events of an interval cost at most 2k(n + m), the scans owed by the
    frames open at its left end included -/
theorem interval_bound (hF : DelayFacts G s t k tr) (hG : G.WF) (hk : 1 ≤ k) {a c m β : Nat} (hC : Consec tr a c) (hS : Shape tr a c m β) :
    G.cost ((tr.drop (a + 1)).take (c - a)) + G.owed (tr[a]'(by have := hC.lt; have := hC.bound; omega)) ≤ 2 * k * (n + G.m) := by
  have ha : a < tr.length := by have := hC.lt; have := hC.bound; omega
  rw [cost_drop_take G tr (c - a) (a + 1) (by have := hC.lt; have := hC.bound; omega), lsum_posCost G tr a c]
  have hout := out_le hF hC
  have howed := owed_le hF ha
  -- regroup by nodes and edges
  have hE : nsum (fun z => (1 + (G.succ z).length) * cnt (fun q => enterAt tr z q = true) a c) = nsum (fun z => cnt (fun q => enterAt tr z q = true) a c) + nsum (fun x => lsum (G.succ x) (fun _ => cnt (fun q => enterAt tr x q = true) a c)) := by
    rw [← lsum_add]; congr 1; funext z; rw [lsum_const, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  have hD : nsum (fun z => (1 + (G.pred z).length) * cnt (fun q => deqAt tr z q = true) a c) = nsum (fun z => cnt (fun q => deqAt tr z q = true) a c) + nsum (fun x => lsum (G.succ x) (fun y => cnt (fun q => deqAt tr y q = true) a c)) := by
    rw [← pred_sum G hG, ← lsum_add]; congr 1; funext z; rw [Nat.add_mul, Nat.one_mul]
  -- per node
  have hnode : nsum (fun z => cnt (fun q => enterAt tr z q = true) a c) + nsum (fun z => cnt (fun q => deqAt tr z q = true) a c) ≤ nsum (fun z => if z = t then 0 else 2 * k) := by
    rw [← lsum_add]
    apply lsum_le
    intro z _
    by_cases hzt : z = t
    · subst hzt
      have h1 : cnt (fun q => enterAt tr z q = true) a c = 0 := Trace.cnt_zero _ (fun q _ _ hq => by rw [hF.enterAt_t] at hq; cases hq)
      have h2 := hF.D_le hC hS z
      have h3 : cnt (fun q => dropAt tr z q = true) a β = 0 := Trace.cnt_zero _ (fun q _ _ hq => by rw [hF.dropAt_t] at hq; cases hq)
      have h4 : anyIn (fruitAt tr z) a β = false := by
        cases h : anyIn (fruitAt tr z) a β
        · rfl
        · obtain ⟨q, -, -, hq⟩ := Trace.anyIn_iff.mp h; rw [hF.fruitAt_t] at hq; cases hq
      simp [h4] at h2
      simp; omega
    · simp only [hzt]; exact hF.node_budget hC hS hk z
  -- per edge
  have hedge : nsum (fun x => lsum (G.succ x) (fun _ => cnt (fun q => enterAt tr x q = true) a c)) + nsum (fun x => lsum (G.succ x) (fun y => cnt (fun q => deqAt tr y q = true) a c)) + nsum (fun x => lsum (G.succ x) (fun _ => if x ∈ stk tr a then 1 else 0)) ≤ 2 * k * G.m := by
    rw [← lsum_add, ← lsum_add]
    have : nsum (fun x => lsum (G.succ x) (fun _ => 2 * k)) = 2 * k * G.m := by
      rw [show (fun x => lsum (G.succ x) (fun _ => 2 * k)) = (fun x => 2 * k * (G.succ x).length) from funext fun x => lsum_const _ _]
      show lsum (List.finRange n) (fun x => 2 * k * (G.succ x).length) = _
      rw [lsum_mul]
      rfl
    rw [← this]
    apply lsum_le
    intro x _
    rw [← lsum_add, ← lsum_add]
    apply lsum_le
    intro y hy
    exact hF.edge_budget hC hS hk hy
  have hn := nsum_ite_ne t (2 * k)
  have hmul : 2 * k * (n + G.m) = 2 * k * n + 2 * k * G.m := Nat.mul_add _ _ _
  rw [hE, hD]
  have h2k : 2 * k * n = 2 * k * n := rfl
  rw [Nat.mul_comm (2 * k) n] at hn
  have : n * (2 * k) = 2 * k * n := Nat.mul_comm _ _
  omega

end bound

section consec

theorem filterMap_head_pos {α β : Type} (f : α → Option β) : ∀ (l : List α) (w : β) (F : List β), l.filterMap f = w :: F → ∃ j, ∃ hj : j < l.length, f l[j] = some w ∧ ∀ q (hq : q < l.length), q < j → f l[q] = none
  | [], _, _, h => by simp at h
  | x :: l, w, F, h => by
    cases hx : f x with
    | some b =>
      rw [List.filterMap_cons_some hx] at h
      obtain ⟨rfl, -⟩ := List.cons.inj h
      exact ⟨0, by simp, by simpa using hx, fun q _ hq => absurd hq (Nat.not_lt_zero _)⟩
    | none =>
      rw [List.filterMap_cons_none hx] at h
      obtain ⟨j, hj, hjw, hbefore⟩ := filterMap_head_pos f l w F h
      refine ⟨j + 1, by simp; omega, by simpa using hjw, fun q hq hqj => ?_⟩
      cases q with
      | zero => simpa using hx
      | succ q => simpa using hbefore q (by simp at hq; omega) (by omega)

/-- consecutive elements of l.filterMap f come from positions i < j with nothing in between -/
theorem filterMap_zip {α β : Type} (f : α → Option β) : ∀ (l : List α) (u w : β), (u, w) ∈ (l.filterMap f).zip (l.filterMap f).tail →
    ∃ i j, ∃ hij : i < j, ∃ hj : j < l.length, f (l[i]'(Nat.lt_trans hij hj)) = some u ∧ f l[j] = some w ∧ ∀ q (hq : q < l.length), i < q → q < j → f l[q] = none
  | [], _, _, h => by simp at h
  | x :: l, u, w, h => by
    cases hx : f x with
    | none =>
      rw [List.filterMap_cons_none hx] at h
      obtain ⟨i, j, hij, hj, hu, hw, hbetween⟩ := filterMap_zip f l u w h
      refine ⟨i + 1, j + 1, by omega, by simp; omega, by simpa using hu, by simpa using hw, fun q hq h1 h2 => ?_⟩
      cases q with
      | zero => omega
      | succ q => simpa using hbetween q (by simp at hq; omega) (by omega) (by omega)
    | some b =>
      rw [List.filterMap_cons_some hx] at h
      cases hF : l.filterMap f with
      | nil => rw [hF] at h; simp at h
      | cons w₀ F =>
        rw [hF] at h
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨hub, hww⟩ | h
        · obtain ⟨j, hj, hjw, hbefore⟩ := filterMap_head_pos f l w₀ F hF
          refine ⟨0, j + 1, by omega, by simp; omega, by simpa [hub] using hx, by simpa [hww] using hjw, fun q hq h1 h2 => ?_⟩
          cases q with
          | zero => omega
          | succ q => simpa using hbefore q (by simp at hq; omega) (by omega)
        · have h' : (u, w) ∈ (l.filterMap f).zip (l.filterMap f).tail := by rw [hF]; simpa using h
          obtain ⟨i, j, hij, hj, hu, hw, hbetween⟩ := filterMap_zip f l u w h'
          refine ⟨i + 1, j + 1, by omega, by simp; omega, by simpa using hu, by simpa using hw, fun q hq h1 h2 => ?_⟩
          cases q with
          | zero => omega
          | succ q => simpa using hbetween q (by simp at hq; omega) (by omega) (by omega)

theorem obsSteps_eq (tr : List (Ev n)) : obsSteps tr = tr.filterMap Ev.obs := by
  unfold obsSteps
  congr 1

/-- consecutive entries of obsSteps are the stamps of consecutive observable events -/
theorem obs_consec (tr : List (Ev n)) {u w : Nat} (h : (u, w) ∈ (obsSteps tr).zip (obsSteps tr).tail) : ∃ a c, Consec tr a c ∧ (∃ ha : a < tr.length, tr[a].obs = some u) ∧ ∃ hc : c < tr.length, tr[c].obs = some w := by
  rw [obsSteps_eq] at h
  obtain ⟨a, c, hac, hc, hu, hw, hbetween⟩ := filterMap_zip Ev.obs tr u w h
  refine ⟨a, c, ⟨hac, hc, ?_, ?_, ?_⟩, ⟨Nat.lt_trans hac hc, hu⟩, ⟨hc, hw⟩⟩
  · simp [isObs, List.getElem?_eq_getElem (Nat.lt_trans hac hc), hu]
  · simp [isObs, List.getElem?_eq_getElem hc, hw]
  · intro q h1 h2
    simp [isObs, List.getElem?_eq_getElem (Nat.lt_trans h2 hc), hbetween q (Nat.lt_trans h2 hc) h1 h2]

/-- every interval has a shape: the least stack size m on (a, c], first reached right after β -/
theorem shape_exists {tr : List (Ev n)} {a c : Nat} (hC : Consec tr a c) : ∃ m β, Shape tr a c m β := by
  obtain ⟨q₀, ⟨hq01, hq02⟩, hmin⟩ := Trace.exists_min (P := fun q => a < q ∧ q ≤ c) (fun q => (stk tr q).length) c ⟨hC.lt, Nat.le_refl c⟩
  obtain ⟨q₁, hq11, hq12, ⟨hq13, hq14⟩, hfirst⟩ := Trace.exists_first (P := fun q => q ≤ c ∧ (stk tr q).length = (stk tr q₀).length) (lo := a) q₀ hq01 ⟨hq02, rfl⟩
  refine ⟨(stk tr q₀).length, q₁ - 1, ⟨by omega, by omega, ?_, ?_, ?_⟩⟩
  · rw [show q₁ - 1 + 1 = q₁ by omega]; exact hq14
  · intro q h1 h2; exact hmin q ⟨h1, h2⟩
  · intro q h1 h2
    have := hmin q ⟨h1, by omega⟩
    have := hfirst q h1 (by omega)
    simp only [not_and] at this
    have := this (by omega)
    omega

end consec

/-- Stage 2 result: the worst-case delay 2k(n+m) (v3) follows from `DelayFacts` for the run -/
theorem worst_case_of_facts (G : Graph n) (s t : Fin n) (k : Nat) (hG : G.WF) (hk : 0 < k) (hF : DelayFacts G s t k (bsdfs G s t k)) : ∀ x ∈ (obsSteps (bsdfs G s t k)).zip (obsSteps (bsdfs G s t k)).tail, x.2 - x.1 ≤ 2 * k * (n + G.m) := by
  intro ⟨u, w⟩ hx
  obtain ⟨a, c, hC, ⟨ha, hu⟩, ⟨hc, hw⟩⟩ := obs_consec _ hx
  obtain ⟨m, β, hS⟩ := shape_exists hC
  have htally := tally G s t k hC.lt hc hu hw
  have hbound := interval_bound hF hG hk hC hS
  simp only
  omega
