import Bsdfs.Sweep

/-!
  Lower bounds, part 2: the run of BS-DFS on a gate trap (gate_family.tex) up to its second output, with exact step counts, for
  any graph with the successor and predecessor lists of Γ_c (`GateCtx`); the concrete graph Γ_c is in Bsdfs/Gate.lean.
  Phases between the outputs s q t and s g q t: (a) search(g) at depth 2 sweeps the block from B_0 with bound k - 3; (b) q scans
  the block: B_0 sweeps it once more with bound 1, the other block nodes are leaves; (c) the cascade fruitful(q, 1) re-arms g and
  the block (one drop each); (d) s scans g, search(g) at depth 1 sweeps the block from B_0 with bound k - 5, then reaches q and t.
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

/-! ## Traces with a known observable prefix -/

/-- T extends T0 by events whose first observable stamps are os -/
def ObsPre (T0 : List (Ev n)) (os : List Nat) (T : List (Ev n)) : Prop := ∃ E1 E2, T = T0 ++ E1 ++ E2 ∧ obsSteps E1 = os

theorem ObsPre.ext {T0 T T' : List (Ev n)} {os : List Nat} (h : ObsPre T0 os T) (h' : ∃ E, T' = T ++ E) : ObsPre T0 os T' := by
  obtain ⟨E1, E2, rfl, h1⟩ := h
  obtain ⟨E, rfl⟩ := h'
  exact ⟨E1, E2 ++ E, by simp, h1⟩

theorem ObsPre.of_output {T0 T E : List (Ev n)} {σ σ' : Nat} {P : List (Fin n)} (hT : T = T0 ++ E) (hE : obsSteps E = []) (hσ : σ = σ') :
    ObsPre T0 [σ'] (T ++ [Ev.output σ P]) :=
  ⟨E ++ [Ev.output σ P], [], by simp [hT], by rw [obsSteps_append, hE, hσ]; rfl⟩

theorem ObsPre.trans {T0 T1 T : List (Ev n)} {os os' : List Nat} (h1 : ∃ E, T1 = T0 ++ E ∧ obsSteps E = os) (h2 : ObsPre T1 os' T) : ObsPre T0 (os ++ os') T := by
  obtain ⟨E, rfl, hE⟩ := h1
  obtain ⟨E1, E2, rfl, h⟩ := h2
  exact ⟨E ++ E1, E2, by simp, by rw [obsSteps_append, hE, h]⟩

theorem trace_obs_trans' {T1 L M : List (Ev n)} {os : List Nat} (h1 : ∃ E, M = T1 ++ E ∧ obsSteps E = os) (h2 : ∃ E, L = M ++ E ∧ obsSteps E = []) : ∃ E, L = T1 ++ E ∧ obsSteps E = os := by
  obtain ⟨E1, rfl, h1⟩ := h1
  obtain ⟨E2, rfl, h2⟩ := h2
  exact ⟨E1 ++ E2, by simp, by rw [obsSteps_append, h1, h2, List.append_nil]⟩

/-! ## Positions in short successor lists -/

theorem eq_append_cons_idx {α : Type} {xs pref suff : List α} {cur : α} (h : xs = pref ++ cur :: suff) : ∃ hp : pref.length < xs.length, xs[pref.length] = cur := by
  subst h; exact ⟨by simp, by simp⟩

theorem cons2_idx {α : Type} {a b cur : α} {l : List α} : ∀ (p : Nat) (hp : p < (a :: b :: l).length), (a :: b :: l)[p] = cur →
    (p = 0 ∧ cur = a) ∨ (p = 1 ∧ cur = b) ∨ ∃ j, ∃ hj : j < l.length, p = j + 2 ∧ cur = l[j]
  | 0, _, he => Or.inl ⟨rfl, he.symm⟩
  | 1, _, he => Or.inr (Or.inl ⟨rfl, he.symm⟩)
  | j + 2, hp, he => Or.inr (Or.inr ⟨j, by simp at hp; omega, rfl, he.symm⟩)

theorem split_cons2 {α : Type} {a b cur : α} {l pref suff : List α} (h : a :: b :: l = pref ++ cur :: suff) :
    (pref.length = 0 ∧ cur = a) ∨ (pref.length = 1 ∧ cur = b) ∨ ∃ j, ∃ hj : j < l.length, pref.length = j + 2 ∧ cur = l[j] := by
  obtain ⟨hp, he⟩ := eq_append_cons_idx h
  exact cons2_idx _ hp he

theorem split2 {α : Type} {a b cur : α} {pref suff : List α} (h : [a, b] = pref ++ cur :: suff) : (pref.length = 0 ∧ cur = a) ∨ (pref.length = 1 ∧ cur = b) := by
  rcases split_cons2 h with h1 | h1 | ⟨j, hj, -, -⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · simp at hj

theorem split3 {α : Type} {a b c cur : α} {pref suff : List α} (h : [a, b, c] = pref ++ cur :: suff) :
    (pref.length = 0 ∧ cur = a) ∨ (pref.length = 1 ∧ cur = b) ∨ (pref.length = 2 ∧ cur = c) := by
  rcases split_cons2 h with h1 | h1 | ⟨j, hj, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · simp at hj; subst hj; exact Or.inr (Or.inr ⟨h1, by simpa using h2⟩)

/-! ## The gate context -/

/-- the successor and predecessor lists of Γ_c (gate_family.tex) on nodes s, q, t, g and the block B_0 .. B_{c-1} = blk -/
structure GateCtx (G : Graph n) (s q t g : Fin n) (blk : List (Fin n)) : Prop where
  nodup : blk.Nodup
  pos : 0 < blk.length
  size : blk.length + 2 ≤ n
  s_q : s ≠ q
  s_t : s ≠ t
  s_g : s ≠ g
  q_t : q ≠ t
  q_g : q ≠ g
  t_g : t ≠ g
  s_blk : s ∉ blk
  q_blk : q ∉ blk
  t_blk : t ∉ blk
  g_blk : g ∉ blk
  succ_s : G.succ s = [q, g]
  succ_q : G.succ q = t :: g :: blk
  succ_g : G.succ g = blk.take 1 ++ [q, s]
  succ_B : ∀ i (hi : i < blk.length), G.succ blk[i] = blk.take i ++ blk.drop (i + 1) ++ [g]
  pred_q : G.pred q = [s, g]
  pred_g : G.pred g = s :: q :: blk
  pred_B : ∀ j (hj : j < blk.length), ∀ u ∈ G.pred blk[j], u = q ∨ u = g ∨ u ∈ blk
  pred_B_len : ∀ j (hj : j < blk.length), (G.pred blk[j]).length = blk.length + (if j = 0 then 1 else 0)

section gate
variable {G : Graph n} {s q t g : Fin n} {blk : List (Fin n)}

theorem GateCtx.succ_g' (ctx : GateCtx G s q t g blk) : G.succ g = [blk[0]'ctx.pos, q, s] := by
  rw [ctx.succ_g, List.take_add_one, List.take_zero, List.getElem?_eq_getElem ctx.pos]; rfl

/-- the sweeps of a gate trap: the block, with X = [g] -/
theorem GateCtx.sweep (ctx : GateCtx G s q t g blk) {k : Nat} (P : List (Fin n)) (h0 β L : Nat) (hP : ∀ x ∈ P, x ∉ blk) (hlen : P.length = h0) (hb : β + h0 + L = k) :
    SweepCtx G t k blk [g] P h0 β L where
  nodup := ctx.nodup
  t_blk := ctx.t_blk
  t_X := by simp [ctx.t_g]
  succ := ctx.succ_B
  X_blk := by simp [ctx.g_blk]
  P_blk := hP
  P_len := hlen
  bound := hb

theorem getElem_ne_of_not_mem {x : Fin n} (hx : x ∉ blk) (j : Nat) (hj : j < blk.length) : blk[j] ≠ x :=
  fun he => hx (he ▸ List.getElem_mem hj)

/-! ### (a) search(g) at depth 2 -/

/-- the loop of search(g) at depth 2, after p successors -/
def g2Inv (g : Fin n) (blk : List (Fin n)) (k : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n)) (p sd : Nat) (st : St n) : Prop :=
  st.S = S0.push g ∧ sd = k + 1 ∧ (∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []) ∧
  if p = 0 then st.b = b0 ∧ st.steps = σ0 + 1
  else (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = 0 then k - 2 else k - 3) ∧ (∀ z, z ∉ blk → st.b[z] = b0[z]) ∧
    st.steps = σ0 + 1 + p + (blk.length + 1) * sweepCalls blk.length (k - 3) 0

theorem g2Inv_skip {g : Fin n} {blk : List (Fin n)} {k : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n} {σ0 : Nat} {T0 : List (Ev n)} {p sd : Nat} {st st' : St n}
    (h : g2Inv g blk k S0 b0 σ0 T0 p sd st) (hp : 0 < p) (hS : st'.S = st.S) (hb : st'.b = st.b) (hσ : st'.steps = st.steps + 1) (hT : st'.trace = st.trace) :
    g2Inv g blk k S0 b0 σ0 T0 (p + 1) sd st' := by
  obtain ⟨hS0, hsd, hE, hrest⟩ := h
  rw [ite_eq_right (show ¬ p = 0 by omega)] at hrest
  obtain ⟨hbb, hbz, hσ0⟩ := hrest
  refine ⟨by rw [hS, hS0], hsd, by rw [hT]; exact hE, ?_⟩
  rw [ite_eq_right (show ¬ p + 1 = 0 by omega)]
  exact ⟨fun j hj => by rw [hb, hbb j hj], fun z hz => by rw [hb, hbz z hz], by rw [hσ, hσ0]; omega⟩

theorem mem_stack {S : Array (Fin n)} {L : List (Fin n)} (h : S.toList = L) {x : Fin n} : x ∈ S ↔ x ∈ L := by rw [Array.mem_def, h]

theorem gate_g2 (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n))
    (hS0 : S0.toList = [s, q]) (hB : ∀ j (hj : j < blk.length), b0[blk[j]] = 0) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.steps = σ0 ∧ st.trace.toList = T0⌝⦄
    search G t k g (1 + 1)
    ⦃⇓ r st => ⌜r = k + 1 ∧ st.S = S0 ∧ st.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = 0 then k - 2 else k - 3) ∧
      (∀ z, z ≠ g → z ∉ blk → st.b[z] = b0[z]) ∧ st.steps = σ0 + 4 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 ∧ ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []⌝⦄ := by
  have hcall : ∀ (w : Fin n) (S2 : Array (Fin n)) (b2 : Vector Nat n) (σ2 : Nat) (T2 : List (Ev n)),
      ⦃fun st => ⌜st.S = S2 ∧ st.b = b2 ∧ st.steps = σ2 ∧ st.trace.toList = T2⌝⦄ search G t k w (1 + 1 + 1)
      ⦃⇓ r st => ⌜w = blk[0]'ctx.pos → S2.toList = [s, q, g] → (∀ j (hj : j < blk.length), 0 < j → b2[blk[j]] = 0) →
        r = k + 1 ∧ st.S = S2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = 0 then k - 2 else k - 3) ∧ (∀ z, z ∉ blk → st.b[z] = b2[z]) ∧
        st.steps = σ2 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 ∧ ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = []⌝⦄ := by
    intro w S2 b2 σ2 T2
    refine (StateM.triple_iff _ _ _).mpr fun st hst hw hS2 hb2 => ?_
    subst hw
    have hsw := sweep_spec G t k blk [g] [s, q, g] 3 0 (k - 3) (ctx.sweep _ 3 0 (k - 3) (by simp [ctx.s_blk, ctx.q_blk, ctx.g_blk]) rfl (by omega)) 0 (Nat.zero_le _) ctx.pos S2 b2 σ2 T2
    obtain ⟨hr, hS, hbb, hbz, hσ, hE⟩ := (StateM.triple_iff _ _ _).mp hsw st ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2, by simpa using hS2, fun j hj hj0 => by rw [hb2 j hj hj0], by simp⟩
    refine ⟨hr, hS, fun j hj => ?_, hbz, by simpa using hσ, hE⟩
    rw [hbb j hj]
    by_cases hj0 : j = 0
    · rw [ite_eq_left hj0, ite_eq_left hj0]; omega
    · rw [ite_eq_right hj0, ite_eq_right hj0, ite_eq_left (Nat.pos_of_ne_zero hj0)]; omega
  have hcasc := fruitful_ext G g
  have hpos := ctx.pos
  have hSl : (S0.push g).toList = [s, q, g] := by rw [Array.toList_push, hS0]; rfl
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hcall, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜g2Inv g blk k S0 b0 σ0 T0 xs.prefix.length sd st⌝
  case vc1.step.isTrue.isTrue =>
    -- t is not a successor of g
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hcur := ‹_ = t›
    rw [ctx.succ_g'] at hsplit
    exfalso
    rcases split3 hsplit with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩
    · exact ctx.t_blk (by rw [← hcur, hc]; exact List.getElem_mem _)
    · exact ctx.q_t (hc.symm.trans hcur)
    · exact ctx.s_t (hc.symm.trans hcur)
  case vc2.step.isTrue.isFalse.isTrue.post.success =>
    -- the call at B_0: the first sweep
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hnS := ‹¬_ ∈ _›
    have hpost := ‹_ = blk[0] → _›
    obtain ⟨hS, hsd, hE, hrest⟩ := ‹g2Inv g blk k S0 b0 σ0 T0 _ _ _›
    simp +zetaDelta only at hnS hpost ⊢
    rw [ctx.succ_g'] at hsplit
    rw [hS, mem_stack hSl] at hnS
    rcases split3 hsplit with ⟨hp, hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩
    · rw [ite_eq_left hp] at hrest
      obtain ⟨hb, hσ⟩ := hrest
      obtain ⟨hr, hS', hbb, hbz, hσ', hE'⟩ := hpost hc (by rw [hS, hSl]) (fun j hj _ => by rw [hb]; exact hB j hj)
      refine ⟨by rw [hS', hS], by omega, trace_obs_trans hE hE', ?_⟩
      simp only [List.length_append, List.length_singleton, hp]
      rw [ite_eq_right (show ¬ 0 + 1 = 0 by omega)]
      exact ⟨hbb, fun z hz => by rw [hbz z hz, hb], by omega⟩
    · simp [hc] at hnS
    · simp [hc] at hnS
  case vc3.step.isTrue.isFalse.isFalse =>
    -- q and s are on the stack
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hin := Classical.not_not.mp ‹¬¬_ ∈ _›
    have hinv := ‹g2Inv g blk k S0 b0 σ0 T0 _ _ _›
    simp +zetaDelta only at hin ⊢
    rw [ctx.succ_g'] at hsplit
    rw [hinv.1, mem_stack hSl] at hin
    simp only [List.length_append, List.length_singleton]
    rcases split3 hsplit with ⟨-, hc⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
    · exfalso
      rw [hc] at hin
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hin
      rcases hin with h | h | h
      · exact ctx.s_blk (h ▸ List.getElem_mem _)
      · exact ctx.q_blk (h ▸ List.getElem_mem _)
      · exact ctx.g_blk (h ▸ List.getElem_mem _)
    · exact g2Inv_skip hinv (by omega) rfl rfl rfl rfl
    · exact g2Inv_skip hinv (by omega) rfl rfl rfl rfl
  case vc4.step.isFalse =>
    -- pruned: only q and s
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hng := ‹¬_ + (1 + 1) < k›
    have hinv := ‹g2Inv g blk k S0 b0 σ0 T0 _ _ _›
    simp +zetaDelta only at hng ⊢
    rw [ctx.succ_g'] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split3 hsplit with ⟨hp, hc⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
    · exfalso
      have hrest := hinv.2.2.2
      rw [ite_eq_left hp] at hrest
      rw [hrest.1, hc, hB 0 hpos] at hng
      omega
    · exact g2Inv_skip hinv (by omega) rfl rfl rfl rfl
    · exact g2Inv_skip hinv (by omega) rfl rfl rfl rfl
  case vc5.pre =>
    -- the entry
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = σ0 ∧ _ = T0›
    simp +zetaDelta only
    refine ⟨by rw [hS], rfl, ⟨_, by rw [Array.toList_push, hT], by simp [obsSteps]⟩, ?_⟩
    simp only [List.length_nil, ↓reduceIte]
    exact ⟨hb, by rw [hσ]⟩
  case vc6.post.success.isTrue.post.success =>
    -- no cascade: sd = k + 1
    have hsd := ‹g2Inv g blk k S0 b0 σ0 T0 _ _ _›.2.1
    have hc := ‹_ ≤ k ∧ _›
    omega
  case vc7.post.success.isFalse =>
    -- the raise of g
    obtain ⟨hS, hsd, ⟨E, hE, hobs⟩, hrest⟩ := ‹g2Inv g blk k S0 b0 σ0 T0 _ _ _›
    rw [ctx.succ_g'] at hrest
    simp only [List.length_cons, List.length_nil] at hrest
    rw [ite_eq_right (show ¬ 0 + 1 + 1 + 1 = 0 by omega)] at hrest
    obtain ⟨hbb, hbz, hσ⟩ := hrest
    simp +zetaDelta only
    refine ⟨hsd, by rw [hS]; simp, by rw [vset_fin, ite_eq_left rfl]; omega, fun j hj => ?_, fun z hz1 hz2 => ?_, by omega, ?_⟩
    · rw [vset_fin, ite_eq_right (Ne.symm (getElem_ne_of_not_mem ctx.g_blk j hj)), hbb j hj]
    · rw [vset_fin, ite_eq_right (fun h => hz1 h.symm), hbz z hz2]
    · simp only [Array.toList_push]
      refine ext_obs_push (ext_obs_push ⟨E, hE, hobs⟩ ?_) ?_ <;> simp [obsSteps]

/-! ### (c) the cascade fruitful(q, 1) -/

/-- the queue of fruitful(q, 1): (q, 1), (g, 2), then the block at 3 -/
def cQueue (q g : Fin n) (blk : List (Fin n)) : List (Fin n × Nat) := (q, 1) :: (g, 2) :: blk.map (fun x => (x, 3))

/-- entries enqueued before outer index i -/
def cOutM (c i : Nat) : Nat := if i = 0 then 1 else if i = 1 then 2 else c + 2

/-- steps spent before outer index i -/
def cOutCost (c i : Nat) : Nat := if i = 0 then 0 else if i = 1 then 3 else c + 6 + (min i (c + 2) - 2) * (c + 1) + (if 2 < i then 1 else 0)

/-- entries enqueued while the entry at index i is processed, after p predecessors -/
def cInM (c i p : Nat) : Nat := if i = 0 then (if 2 ≤ p then 2 else 1) else if i = 1 then max 2 p else c + 2

/-- the cascade state after m entries were enqueued -/
def cState (q g : Fin n) (blk : List (Fin n)) (k : Nat) (S1 : Array (Fin n)) (b1 : Vector Nat n) (T1 : List (Ev n)) (m : Nat) (queue : Array (Fin n × Nat)) (st : St n) : Prop :=
  st.S = S1 ∧ queue.toList = (cQueue q g blk).take m ∧ st.b[q] = 1 ∧ st.b[g] = (if 2 ≤ m then 2 else k - 1) ∧
  (∀ j (hj : j < blk.length), st.b[blk[j]] = if j + 2 < m then 3 else k - 1) ∧ (∀ z, z ≠ q → z ≠ g → z ∉ blk → st.b[z] = b1[z]) ∧
  ∃ E, st.trace.toList = T1 ++ E ∧ obsSteps E = []

theorem cQueue_length : (cQueue q g blk).length = blk.length + 2 := by simp [cQueue]

theorem cQueue_cases (i : Nat) (hi : i < (cQueue q g blk).length) :
    (i = 0 ∧ (cQueue q g blk)[i] = (q, 1)) ∨ (i = 1 ∧ (cQueue q g blk)[i] = (g, 2)) ∨ ∃ j, ∃ hj : j < blk.length, i = j + 2 ∧ (cQueue q g blk)[i] = (blk[j], 3) := by
  match i, hi with
  | 0, _ => exact Or.inl ⟨rfl, rfl⟩
  | 1, _ => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | j + 2, hi => exact Or.inr (Or.inr ⟨j, by simp [cQueue] at hi; omega, rfl, by simp [cQueue]⟩)

theorem range_split_idx {pref suff : List Nat} {cur : Nat} (h : List.range n = pref ++ cur :: suff) : cur = pref.length := by
  have h1 : (List.range n)[pref.length]'(by rw [h]; simp) = cur := by simp only [h]; simp
  simp at h1
  exact h1.symm

theorem queue_get {queue : Array (Fin n × Nat)} {L : List (Fin n × Nat)} {m : Nat} (hQ : queue.toList = L.take m) {i : Nat} (hi : i < queue.size) :
    ∃ hc : i < L.length, queue[i] = L[i] := by
  have h1 : i < (L.take m).length := by rw [← hQ]; simpa using hi
  refine ⟨by simp at h1; omega, ?_⟩
  rw [← Array.getElem_toList (by simpa using hi), List.getElem_of_eq hQ, List.getElem_take]

theorem queue_size {queue : Array (Fin n × Nat)} {L : List (Fin n × Nat)} {m : Nat} (hQ : queue.toList = L.take m) : queue.size = min m L.length := by
  rw [← Array.length_toList, hQ, List.length_take]

theorem take_push {α : Type} (L : List α) (m : Nat) (hm : m < L.length) : L.take m ++ [L[m]] = L.take (m + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm]; rfl

theorem cInM_zero (c i : Nat) : cInM c i 0 = cOutM c i := by
  unfold cInM cOutM
  by_cases h0 : i = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h1 : i = 1
    · rw [ite_eq_left h1, ite_eq_left h1]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]

theorem cInM_g (c p : Nat) : cInM c 1 p = max 2 p := by
  unfold cInM; rw [ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl]

theorem cInM_B (c j p : Nat) : cInM c (j + 2) p = c + 2 := by
  unfold cInM; rw [ite_eq_right (show ¬ (j + 2 = 0) by omega), ite_eq_right (show ¬ (j + 2 = 1) by omega)]

theorem cOutM_B (c j : Nat) : cOutM c (j + 2 + 1) = c + 2 := by
  unfold cOutM; rw [ite_eq_right (show ¬ (j + 2 + 1 = 0) by omega), ite_eq_right (show ¬ (j + 2 + 1 = 1) by omega)]

theorem cOutCost_two (c : Nat) : cOutCost c (1 + 1) = c + 6 := by
  unfold cOutCost
  rw [ite_eq_right (show ¬ (1 + 1 = 0) by omega), ite_eq_right (show ¬ (1 + 1 = 1) by omega), show min (1 + 1) (c + 2) - 2 = 0 by omega, ite_eq_right (show ¬ (2 < 1 + 1) by omega)]
  simp

theorem cOutM_ge {c i : Nat} (h : ¬ i < min (cOutM c i) (c + 2)) : c + 2 ≤ i := by
  unfold cOutM at h
  by_cases h0 : i = 0
  · rw [ite_eq_left h0] at h; omega
  · rw [ite_eq_right h0] at h
    by_cases h1 : i = 1
    · rw [ite_eq_left h1] at h; omega
    · rw [ite_eq_right h1] at h; omega

theorem cState_tr {k : Nat} {S1 : Array (Fin n)} {b1 : Vector Nat n} {T1 : List (Ev n)} {m : Nat} {queue : Array (Fin n × Nat)} {st st' : St n}
    (h : cState q g blk k S1 b1 T1 m queue st) (hS : st'.S = st.S) (hb : st'.b = st.b) (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    cState q g blk k S1 b1 T1 m queue st' := by
  obtain ⟨hS0, hQ, hbq, hbg, hbb, hbz, hE⟩ := h
  exact ⟨by rw [hS, hS0], hQ, by rw [hb, hbq], by rw [hb, hbg], fun j hj => by rw [hb, hbb j hj], fun z h1 h2 h3 => by rw [hb, hbz z h1 h2 h3], trace_obs_trans hE hT⟩

theorem cState_relax_g (ctx : GateCtx G s q t g blk) {k : Nat} {S1 : Array (Fin n)} {b1 : Vector Nat n} {T1 : List (Ev n)} {queue : Array (Fin n × Nat)} {st st' : St n}
    (h : cState q g blk k S1 b1 T1 1 queue st) (hS : st'.S = st.S) (hb : st'.b = st.b.set g.1 2 g.2) (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    cState q g blk k S1 b1 T1 2 (queue.push (g, 2)) st' := by
  obtain ⟨hS0, hQ, hbq, hbg, hbb, hbz, hE⟩ := h
  refine ⟨by rw [hS, hS0], by rw [Array.toList_push, hQ]; rfl, by rw [hb, vset_fin, ite_eq_right (Ne.symm ctx.q_g), hbq], by rw [hb, vset_fin, ite_eq_left rfl]; rfl,
    fun j hj => ?_, fun z h1 h2 h3 => ?_, trace_obs_trans hE hT⟩
  · rw [hb, vset_fin, ite_eq_right (Ne.symm (getElem_ne_of_not_mem ctx.g_blk j hj)), hbb j hj, ite_eq_right (show ¬ j + 2 < 1 by omega), ite_eq_right (show ¬ j + 2 < 2 by omega)]
  · rw [hb, vset_fin, ite_eq_right (fun he => h2 he.symm), hbz z h1 h2 h3]

theorem cState_relax_B (ctx : GateCtx G s q t g blk) {k : Nat} {S1 : Array (Fin n)} {b1 : Vector Nat n} {T1 : List (Ev n)} {queue : Array (Fin n × Nat)} {st st' : St n}
    {j : Nat} (hj : j < blk.length) (h : cState q g blk k S1 b1 T1 (j + 2) queue st) (hS : st'.S = st.S) (hb : st'.b = st.b.set blk[j].1 3 blk[j].2)
    (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    cState q g blk k S1 b1 T1 (j + 3) (queue.push (blk[j], 3)) st' := by
  obtain ⟨hS0, hQ, hbq, hbg, hbb, hbz, hE⟩ := h
  refine ⟨by rw [hS, hS0], ?_, by rw [hb, vset_fin, ite_eq_right (getElem_ne_of_not_mem ctx.q_blk j hj), hbq], ?_, fun i hi => ?_, fun z h1 h2 h3 => ?_, trace_obs_trans hE hT⟩
  · have hlt : j + 2 < (cQueue q g blk).length := by rw [cQueue_length]; omega
    have he : (cQueue q g blk)[j + 2] = (blk[j], 3) := by simp [cQueue]
    rw [Array.toList_push, hQ, ← he, take_push _ _ hlt]
  · rw [hb, vset_fin, ite_eq_right (getElem_ne_of_not_mem ctx.g_blk j hj), hbg, ite_eq_left (show 2 ≤ j + 2 by omega), ite_eq_left (show 2 ≤ j + 3 by omega)]
  · rw [hb, vset_fin]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left (show i + 2 < i + 3 by omega)]
    · have hne : blk[j] ≠ blk[i] := fun he => hij ((ctx.nodup.getElem_inj (hi := hj) (hj := hi)).mp he).symm
      rw [ite_eq_right hne, hbb i hi]
      by_cases hlt : i + 2 < j + 2
      · rw [ite_eq_left hlt, ite_eq_left (show i + 2 < j + 3 by omega)]
      · rw [ite_eq_right hlt, ite_eq_right (show ¬ i + 2 < j + 3 by omega)]
  · rw [hb, vset_fin, ite_eq_right (show ¬ (blk[j] = z) from fun he => h3 (he ▸ List.getElem_mem hj)), hbz z h1 h2 h3]

theorem cOutCost_B {c j : Nat} (hj : j < c) : cOutCost c (j + 2 + 1) = cOutCost c (j + 2) + 1 + (c + if j = 0 then 1 else 0) := by
  unfold cOutCost
  rw [ite_eq_right (show ¬ j + 2 + 1 = 0 by omega), ite_eq_right (show ¬ j + 2 + 1 = 1 by omega), ite_eq_right (show ¬ j + 2 = 0 by omega), ite_eq_right (show ¬ j + 2 = 1 by omega),
    show min (j + 2 + 1) (c + 2) - 2 = j + 1 by omega, show min (j + 2) (c + 2) - 2 = j by omega, ite_eq_left (show 2 < j + 2 + 1 by omega), Nat.succ_mul]
  by_cases h0 : j = 0
  · subst h0; simp; omega
  · rw [ite_eq_left (show 2 < j + 2 by omega), ite_eq_right h0]; omega

theorem cOut_final {c i : Nat} (hc : 0 < c) (hi : c + 2 ≤ i) : cOutM c i = c + 2 ∧ cOutCost c i = c * c + 2 * c + 7 := by
  unfold cOutM cOutCost
  rw [ite_eq_right (show ¬ i = 0 by omega), ite_eq_right (show ¬ i = 1 by omega), ite_eq_right (show ¬ i = 0 by omega), ite_eq_right (show ¬ i = 1 by omega),
    show min i (c + 2) - 2 = c by omega, ite_eq_left (show 2 < i by omega), Nat.mul_succ]
  omega

/-- (c) the cascade from q with sd = 1: drops g to 2 and every block node to 3, c² + 2c + 7 steps -/
theorem gate_casc (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) (S1 : Array (Fin n)) (b1 : Vector Nat n) (σ1 : Nat) (T1 : List (Ev n))
    (hS1 : S1.toList = [s, q]) (hg : b1[g] = k - 1) (hB : ∀ j (hj : j < blk.length), b1[blk[j]] = k - 1) :
    ⦃fun st => ⌜st.S = S1 ∧ st.b = b1 ∧ st.steps = σ1 ∧ st.trace.toList = T1⌝⦄
    fruitful G q 1
    ⦃⇓ _ st => ⌜st.S = S1 ∧ st.b[q] = 1 ∧ st.b[g] = 2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = 3) ∧ (∀ z, z ≠ q → z ≠ g → z ∉ blk → st.b[z] = b1[z]) ∧
      st.steps = σ1 + blk.length * blk.length + 2 * blk.length + 7 ∧ ∃ E, st.trace.toList = T1 ++ E ∧ obsSteps E = []⌝⦄ := by
  mvcgen [fruitful, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack] invariants
  | inv1 => ⇓⟨xs, queue⟩ st => ⌜cState q g blk k S1 b1 T1 (cOutM blk.length xs.prefix.length) queue st ∧ st.steps = σ1 + cOutCost blk.length xs.prefix.length⌝
  | inv2 _ cur _ _ qo hcur _ _ _ _ => ⇓⟨xs, queue⟩ st => ⌜cState q g blk k S1 b1 T1 (cInM blk.length cur xs.prefix.length) queue st ∧
      st.steps = σ1 + cOutCost blk.length cur + 1 + xs.prefix.length ∧ ∃ hc : cur < (cQueue q g blk).length, qo[cur]'hcur = (cQueue q g blk)[cur]⌝
  case vc1.step.isTrue =>
    -- a drop: g (from q) or a block node (from g)
    obtain ⟨hst, hσ, hc, hqo⟩ := ‹cState q g blk k S1 b1 T1 _ _ _ ∧ _ ∧ ∃ _, _›
    have hsplit := ‹G.pred _ = _ ++ _ :: _›
    have hcond := ‹¬_ ∈ _ ∧ _ > _›
    simp +zetaDelta only at hcond ⊢
    rw [hqo] at hsplit
    rw [hqo] at hcond
    rw [hqo]
    refine ⟨?_, by simp only [List.length_append, List.length_singleton]; omega, hc, rfl⟩
    rw [hst.1, mem_stack hS1] at hcond
    rcases cQueue_cases _ hc with ⟨hi, he⟩ | ⟨hi, he⟩ | ⟨j, hj, hi, he⟩
    · -- (q, 1): s is on the stack, g drops to 2
      rw [he] at hsplit hcond ⊢
      simp only at hsplit hcond ⊢
      rw [ctx.pred_q] at hsplit
      subst hi
      rcases split2 hsplit with ⟨hp, hpc⟩ | ⟨hp, hpc⟩
      · simp [hpc] at hcond
      · subst hpc
        simp only [List.length_append, List.length_singleton, hp] at hst ⊢
        exact cState_relax_g ctx hst rfl rfl ⟨_, by rw [Array.toList_push], by simp [obsSteps]⟩
    · -- (g, 2): s and q are on the stack, every block node drops to 3
      rw [he] at hsplit hcond ⊢
      simp only at hsplit hcond ⊢
      rw [ctx.pred_g] at hsplit
      subst hi
      rcases split_cons2 hsplit with ⟨hp, hpc⟩ | ⟨hp, hpc⟩ | ⟨j, hj, hp, hpc⟩
      · simp [hpc] at hcond
      · simp [hpc] at hcond
      · subst hpc
        simp only [List.length_append, List.length_singleton, hp, cInM_g] at hst ⊢
        rw [show max 2 (j + 2) = j + 2 by omega] at hst
        rw [show max 2 (j + 2 + 1) = j + 3 by omega]
        exact cState_relax_B ctx hj hst rfl rfl ⟨_, by rw [Array.toList_push], by simp [obsSteps]⟩
    · -- (B_j, 3): nothing drops
      exfalso
      rw [he] at hsplit hcond
      simp only at hsplit hcond
      subst hi
      rw [cInM_B] at hst
      rcases ctx.pred_B j hj _ (mem_split hsplit) with hpc | hpc | hpc
      · simp [hpc] at hcond
      · rw [hpc, hst.2.2.2.1, ite_eq_left (show 2 ≤ blk.length + 2 by omega)] at hcond; omega
      · obtain ⟨i, hi, hpc'⟩ := List.mem_iff_getElem.mp hpc
        rw [← hpc', hst.2.2.2.2.1 i hi, ite_eq_left (show i + 2 < blk.length + 2 by omega)] at hcond; omega
  case vc2.step.isFalse =>
    -- no drop: the queue stays
    obtain ⟨hst, hσ, hc, hqo⟩ := ‹cState q g blk k S1 b1 T1 _ _ _ ∧ _ ∧ ∃ _, _›
    have hsplit := ‹G.pred _ = _ ++ _ :: _›
    have hcond := ‹¬(¬_ ∈ _ ∧ _ > _)›
    simp +zetaDelta only at hcond ⊢
    rw [hqo] at hsplit
    rw [hqo] at hcond
    refine ⟨?_, by simp only [List.length_append, List.length_singleton]; omega, hc, hqo⟩
    rw [hst.1, mem_stack hS1] at hcond
    simp only [List.length_append, List.length_singleton]
    rcases cQueue_cases _ hc with ⟨hi, he⟩ | ⟨hi, he⟩ | ⟨j, hj, hi, he⟩
    · rw [he] at hsplit hcond
      simp only at hsplit hcond
      rw [ctx.pred_q] at hsplit
      subst hi
      rcases split2 hsplit with ⟨hp, hpc⟩ | ⟨hp, hpc⟩
      · rw [hp] at hst ⊢
        exact cState_tr hst rfl rfl ⟨[], by simp, rfl⟩
      · exfalso
        subst hpc
        rw [hp] at hst
        apply hcond
        refine ⟨by simp [Ne.symm ctx.s_g, Ne.symm ctx.q_g], ?_⟩
        rw [hst.2.2.2.1]
        simp [cInM]
        omega
    · rw [he] at hsplit hcond
      simp only at hsplit hcond
      rw [ctx.pred_g] at hsplit
      subst hi
      rw [cInM_g] at hst ⊢
      rcases split_cons2 hsplit with ⟨hp, hpc⟩ | ⟨hp, hpc⟩ | ⟨j, hj, hp, hpc⟩
      · rw [hp] at hst ⊢
        exact cState_tr hst rfl rfl ⟨[], by simp, rfl⟩
      · rw [hp] at hst ⊢
        exact cState_tr hst rfl rfl ⟨[], by simp, rfl⟩
      · exfalso
        subst hpc
        rw [hp] at hst
        apply hcond
        refine ⟨by simp [getElem_ne_of_not_mem ctx.s_blk j hj, getElem_ne_of_not_mem ctx.q_blk j hj], ?_⟩
        rw [hst.2.2.2.2.1 j hj, ite_eq_right (show ¬ j + 2 < max 2 (j + 2) by omega)]
        omega
    · subst hi
      rw [cInM_B] at hst ⊢
      exact cState_tr hst rfl rfl ⟨[], by simp, rfl⟩
  case vc3.step.isTrue.pre =>
    -- dequeue
    obtain ⟨hst, hσ⟩ := ‹cState q g blk k S1 b1 T1 _ _ _ ∧ _›
    have hcur := range_split_idx ‹List.range n = _ ++ _ :: _›
    have hlt := ‹_ < Array.size _›
    simp +zetaDelta only
    subst hcur
    obtain ⟨hc, hq⟩ := queue_get hst.2.1 hlt
    refine ⟨?_, by simp only [List.length_nil]; omega, hc, hq⟩
    simp only [List.length_nil]
    rw [cInM_zero]
    exact cState_tr hst rfl rfl ⟨_, by rw [Array.toList_push], by simp [obsSteps]⟩
  case vc4.step.isTrue.post.success =>
    -- the next entry
    obtain ⟨hst, hσ, hc, hqo⟩ := ‹cState q g blk k S1 b1 T1 _ _ _ ∧ _ ∧ ∃ _, _›
    have hcur := range_split_idx ‹List.range n = _ ++ _ :: _›
    simp only [List.length_append, List.length_singleton]
    rw [← hcur]
    rw [hqo] at hst hσ
    rcases cQueue_cases _ hc with ⟨hi, he⟩ | ⟨hi, he⟩ | ⟨j, hj, hi, he⟩
    · rw [he] at hst hσ
      simp only at hst hσ
      rw [ctx.pred_q] at hst hσ
      subst hi
      exact ⟨hst, by rw [hσ]; rfl⟩
    · rw [he] at hst hσ
      simp only at hst hσ
      rw [ctx.pred_g] at hst hσ
      subst hi
      simp only [List.length_cons, cInM_g] at hst hσ
      rw [show max 2 (blk.length + 1 + 1) = blk.length + 2 by omega] at hst
      rw [cOutCost_two, show cOutM blk.length (1 + 1) = blk.length + 2 from rfl]
      refine ⟨hst, ?_⟩
      rw [hσ, show cOutCost blk.length 1 = 3 from rfl]
      omega
    · rw [he] at hst hσ
      simp only at hst hσ
      subst hi
      rw [ctx.pred_B_len j hj, cInM_B] at hst
      rw [ctx.pred_B_len j hj] at hσ
      rw [cOutM_B, cOutCost_B hj]
      exact ⟨hst, by omega⟩
  case vc5.step.isFalse =>
    -- break: every entry is processed
    obtain ⟨hst, hσ⟩ := ‹cState q g blk k S1 b1 T1 _ _ _ ∧ _›
    have hcur := range_split_idx ‹List.range n = _ ++ _ :: _›
    have hge := ‹¬_ < Array.size _›
    simp only [List.length_range]
    subst hcur
    rw [queue_size hst.2.1, cQueue_length] at hge
    obtain ⟨hm1, hc1⟩ := cOut_final ctx.pos (cOutM_ge hge)
    obtain ⟨hm2, hc2⟩ := cOut_final ctx.pos ctx.size
    rw [hm1] at hst
    rw [hc1] at hσ
    rw [hm2, hc2]
    exact ⟨hst, hσ⟩
  case vc6.pre =>
    -- the fruitful write of q and the queue (q, 1)
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S1 ∧ _ = b1 ∧ _ = σ1 ∧ _ = T1›
    simp +zetaDelta only
    simp only [List.length_nil]
    refine ⟨⟨hS, rfl, by rw [vset_fin, ite_eq_left rfl], ?_, fun j hj => ?_, fun z hz1 hz2 hz3 => ?_, ⟨_, by rw [Array.toList_push, Array.toList_push, hT, List.append_assoc], by simp [obsSteps]⟩⟩, by rw [hσ]; rfl⟩
    · rw [vset_fin, ite_eq_right ctx.q_g, hb, hg]; rfl
    · rw [vset_fin, ite_eq_right (Ne.symm (getElem_ne_of_not_mem ctx.q_blk j hj)), hb, hB j hj]; rfl
    · rw [vset_fin, ite_eq_right (fun h => hz1 h.symm), hb]
  case vc7.post.success =>
    -- all entries processed
    obtain ⟨⟨hS, hQ, hbq, hbg, hbb, hbz, hE⟩, hσ⟩ := ‹cState q g blk k S1 b1 T1 _ _ _ ∧ _›
    simp only [List.length_range] at hbg hbb hσ
    obtain ⟨hm, hc⟩ := cOut_final ctx.pos ctx.size
    rw [hm] at hbg hbb
    rw [hc] at hσ
    refine ⟨hS, hbq, by rw [hbg, ite_eq_left (show 2 ≤ blk.length + 2 by omega)], fun j hj => by rw [hbb j hj, ite_eq_left (show j + 2 < blk.length + 2 by omega)], hbz, by omega, hE⟩

/-! ### search(q) at depth 1: the output s q t, (a), (b), (c) -/

theorem sweepCalls_one {c : Nat} (hc : 0 < c) : sweepCalls c 1 0 = c := by
  unfold sweepCalls
  rcases Nat.lt_or_ge c 2 with h | h
  · rw [show min 1 (c - 1) - 0 = 0 by omega]; simp; omega
  · rw [show min 1 (c - 1) - 0 = 1 by omega]; simp; omega

/-- block barriers in phase (b) after i block nodes: after (a) (i = 0), after the sweep from B_0 and i - 1 leaves -/
def q1Bar (k i j : Nat) : Nat := if i = 0 then (if j = 0 then k - 2 else k - 3) else if j < i then k - 1 else k - 2

/-- steps of phase (b) after i block nodes -/
def q1Cost (c i : Nat) : Nat := if i = 0 then 0 else 1 + (c + 1) * sweepCalls c 1 0 + (i - 1) * (c + 2)

/-- the loop of search(q) at depth 1, after p successors (t, g, B_0, ..) -/
def q1Inv (q t g : Fin n) (blk : List (Fin n)) (k : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n)) (p sd : Nat) (st : St n) : Prop :=
  st.S = S0.push q ∧ st.b[t] = b0[t] ∧ (∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = if p = 0 then [] else [σ0 + 5]) ∧
  if p = 0 then sd = k + 1 ∧ st.b = b0 ∧ st.steps = σ0 + 1
  else if p = 1 then sd = 1 ∧ st.b = b0 ∧ st.steps = σ0 + 5
  else sd = 1 ∧ st.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = q1Bar k (p - 2) j) ∧
    st.steps = σ0 + 10 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 + q1Cost blk.length (p - 2)

theorem q1_arith (c N σ : Nat) (hc : 0 < c) :
    σ + 10 + (c + 1) * N + (1 + (c + 1) * c + (c - 1) * (c + 2)) + c * c + 2 * c + 7 = σ + (c + 1) * N + 3 * c * c + 4 * c + 16 := by
  have h1 : (c + 1) * c = c * c + c := Nat.succ_mul c c
  have h2 : (c - 1) * (c + 2) + 2 = c * c + c := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have h3 : 3 * c * c = 3 * (c * c) := Nat.mul_assoc 3 c c
  omega

theorem q1Inv_leaf {q t g : Fin n} {blk : List (Fin n)} {k : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n} {σ0 : Nat} {T0 : List (Ev n)} {sd r : Nat} {st st' : St n}
    (hnd : blk.Nodup) (hgb : g ∉ blk) {i : Nat} (hi1 : 1 ≤ i) (hi : i < blk.length) (h : q1Inv q t g blk k S0 b0 σ0 T0 (i + 2) sd st) (hk : 6 ≤ k) (htb : t ∉ blk)
    (hr : r = k + 1) (hS : st'.S = st.S) (hb : st'.b = st.b.set blk[i].1 (k - (0 + 1 + 1) + 1) blk[i].2) (hσ : st'.steps = st.steps + 1 + 1 + (blk.length - 1 + 1))
    (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    q1Inv q t g blk k S0 b0 σ0 T0 (i + 2 + 1) (min sd (r + 1)) st' := by
  obtain ⟨hS0, hbt, hE, hrest⟩ := h
  rw [ite_eq_right (show ¬ i + 2 = 0 by omega), ite_eq_right (show ¬ i + 2 = 1 by omega)] at hrest
  obtain ⟨hsd, hbg, hbb, hσ0⟩ := hrest
  refine ⟨by rw [hS, hS0], by rw [hb, vset_fin, ite_eq_right (show ¬ (blk[i] = t) from fun he => htb (he ▸ List.getElem_mem hi)), hbt], ?_, ?_⟩
  · rw [ite_eq_right (show ¬ i + 2 + 1 = 0 by omega)]
    rw [ite_eq_right (show ¬ i + 2 = 0 by omega)] at hE
    exact trace_obs_trans' hE hT
  · rw [ite_eq_right (show ¬ i + 2 + 1 = 0 by omega), ite_eq_right (show ¬ i + 2 + 1 = 1 by omega)]
    refine ⟨by omega, by rw [hb, vset_fin, ite_eq_right (show ¬ (blk[i] = g) from fun he => hgb (he ▸ List.getElem_mem hi)), hbg], fun j hj => ?_, ?_⟩
    · rw [hb, vset_fin]
      rw [show i + 2 + 1 - 2 = i + 1 by omega]
      rw [show i + 2 - 2 = i by omega] at hbb
      unfold q1Bar
      rw [ite_eq_right (show ¬ i + 1 = 0 by omega)]
      by_cases hji : j = i
      · subst hji; rw [ite_eq_left rfl, ite_eq_left (show j < j + 1 by omega)]; omega
      · have hne : blk[i] ≠ blk[j] := fun he => hji ((hnd.getElem_inj (hi := hi) (hj := hj)).mp he).symm
        rw [ite_eq_right hne, hbb j hj]
        unfold q1Bar
        rw [ite_eq_right (show ¬ i = 0 by omega)]
        by_cases hlt : j < i
        · rw [ite_eq_left hlt, ite_eq_left (show j < i + 1 by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (show ¬ j < i + 1 by omega)]
    · rw [hσ, hσ0, show i + 2 + 1 - 2 = i + 1 by omega, show i + 2 - 2 = i by omega]
      unfold q1Cost
      rw [ite_eq_right (show ¬ i + 1 = 0 by omega), ite_eq_right (show ¬ i = 0 by omega), show i + 1 - 1 = (i - 1) + 1 by omega]
      have : (i - 1 + 1) * (blk.length + 2) = (i - 1) * (blk.length + 2) + (blk.length + 2) := Nat.succ_mul _ _
      omega

section q1lemmas
variable {q t g : Fin n} {blk : List (Fin n)} {k : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n} {σ0 : Nat} {T0 : List (Ev n)}

theorem q1Inv_one {sd : Nat} {st : St n} (h : q1Inv q t g blk k S0 b0 σ0 T0 1 sd st) : sd = 1 ∧ st.b = b0 ∧ st.steps = σ0 + 5 := h.2.2.2

theorem q1Inv_two {sd : Nat} {st : St n} (h : q1Inv q t g blk k S0 b0 σ0 T0 2 sd st) :
    sd = 1 ∧ st.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = 0 then k - 2 else k - 3) ∧ st.steps = σ0 + 10 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 := by
  have h' : sd = 1 ∧ st.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = q1Bar k 0 j) ∧
      st.steps = σ0 + 10 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 + q1Cost blk.length 0 := h.2.2.2
  obtain ⟨h1, h2, h3, h4⟩ := h'
  exact ⟨h1, h2, fun j hj => by rw [h3 j hj]; unfold q1Bar; rw [ite_eq_left rfl], by rw [h4, show q1Cost blk.length 0 = 0 from rfl, Nat.add_zero]⟩

theorem q1Inv_out {sd : Nat} {st st' : St n} {P : List (Fin n)} (h : q1Inv q t g blk k S0 b0 σ0 T0 0 sd st)
    (hS : st'.S = st.S) (hb : st'.b = st.b) (hσ : st'.steps = st.steps + 1 + 3) (hT : st'.trace.toList = st.trace.toList ++ [Ev.output (st.steps + 1 + 3) P]) :
    q1Inv q t g blk k S0 b0 σ0 T0 (0 + 1) 1 st' := by
  obtain ⟨hS0, hbt, ⟨E, hE, hobs⟩, hrest⟩ := h
  have hobs' : obsSteps E = [] := hobs
  have hrest' : sd = k + 1 ∧ st.b = b0 ∧ st.steps = σ0 + 1 := hrest
  obtain ⟨-, hb0, hσ0⟩ := hrest'
  show st'.S = S0.push q ∧ st'.b[t] = b0[t] ∧ (∃ E, st'.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 5]) ∧ (1 = 1 ∧ st'.b = b0 ∧ st'.steps = σ0 + 5)
  refine ⟨by rw [hS, hS0], by rw [hb, hbt], ⟨E ++ [Ev.output (st.steps + 1 + 3) P], by rw [hT, hE, List.append_assoc], ?_⟩, rfl, by rw [hb, hb0], by omega⟩
  rw [obsSteps_append, hobs']
  simp [obsSteps, hσ0]

theorem q1Inv_g2 {sd r : Nat} {st st' : St n} (htg : t ≠ g) (htb : t ∉ blk) (h : q1Inv q t g blk k S0 b0 σ0 T0 1 sd st)
    (hr : r = k + 1) (hS : st'.S = st.S) (hbg : st'.b[g] = k - 1) (hbb : ∀ j (hj : j < blk.length), st'.b[blk[j]] = if j = 0 then k - 2 else k - 3)
    (hbz : ∀ z, z ≠ g → z ∉ blk → st'.b[z] = st.b[z]) (hσ : st'.steps = st.steps + 1 + 4 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0)
    (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) :
    q1Inv q t g blk k S0 b0 σ0 T0 (1 + 1) (min sd (r + 1)) st' := by
  obtain ⟨hsd, hb0, hσ0⟩ := q1Inv_one h
  obtain ⟨hS0, hbt, hE, -⟩ := h
  have hE' : ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 5] := hE
  show st'.S = S0.push q ∧ st'.b[t] = b0[t] ∧ (∃ E, st'.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 5]) ∧
    (min sd (r + 1) = 1 ∧ st'.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st'.b[blk[j]] = q1Bar k 0 j) ∧
      st'.steps = σ0 + 10 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 + q1Cost blk.length 0)
  refine ⟨by rw [hS, hS0], by rw [hbz t htg htb, hbt], trace_obs_trans' hE' hT, by omega, hbg, fun j hj => ?_, ?_⟩
  · rw [hbb j hj]; unfold q1Bar; rw [ite_eq_left rfl]
  · rw [show q1Cost blk.length 0 = 0 from rfl]; omega

theorem q1Inv_sweep {sd r : Nat} {st st' : St n} (htb : t ∉ blk) (h : q1Inv q t g blk k S0 b0 σ0 T0 2 sd st)
    (hr : r = k + 1) (hS : st'.S = st.S) (hbb : ∀ j (hj : j < blk.length), st'.b[blk[j]] = if j = 0 then k - 1 else k - 2) (hbz : ∀ z, z ∉ blk → st'.b[z] = st.b[z])
    (hσ : st'.steps = st.steps + 1 + (blk.length + 1) * sweepCalls blk.length 1 0) (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E ∧ obsSteps E = []) (hgb : g ∉ blk) :
    q1Inv q t g blk k S0 b0 σ0 T0 (2 + 1) (min sd (r + 1)) st' := by
  obtain ⟨hsd, hbg, -, hσ0⟩ := q1Inv_two h
  obtain ⟨hS0, hbt, hE, -⟩ := h
  have hE' : ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 5] := hE
  show st'.S = S0.push q ∧ st'.b[t] = b0[t] ∧ (∃ E, st'.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 5]) ∧
    (min sd (r + 1) = 1 ∧ st'.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st'.b[blk[j]] = q1Bar k 1 j) ∧
      st'.steps = σ0 + 10 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 + q1Cost blk.length 1)
  refine ⟨by rw [hS, hS0], by rw [hbz t htb, hbt], trace_obs_trans' hE' hT, by omega, by rw [hbz g hgb, hbg], fun j hj => ?_, ?_⟩
  · rw [hbb j hj]; unfold q1Bar; rw [ite_eq_right (show ¬ (1 = 0) by omega)]
    by_cases hj0 : j = 0
    · rw [ite_eq_left hj0, ite_eq_left (show j < 1 by omega)]
    · rw [ite_eq_right hj0, ite_eq_right (show ¬ j < 1 by omega)]
  · have hc1 : q1Cost blk.length 1 = 1 + (blk.length + 1) * sweepCalls blk.length 1 0 := by unfold q1Cost; simp
    rw [hc1]; omega

end q1lemmas

/-- in phase (b), a later block node B_i (i ≥ 1) is a leaf at depth 2 -/
theorem q1_leaf_cond {G : Graph n} {s q t g : Fin n} {blk : List (Fin n)} (ctx : GateCtx G s q t g blk) {k : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n} {σ0 : Nat} {T0 : List (Ev n)} {sd : Nat} {st : St n}
    {i : Nat} (hi1 : 1 ≤ i) (hi : i < blk.length) (h : q1Inv q t g blk k S0 b0 σ0 T0 (i + 2) sd st) (hk : 6 ≤ k) :
    ∀ u ∈ G.succ blk[i], k ≤ st.b[u] + (0 + 1 + 1) ∨ (u ≠ t ∧ u ∈ (st.S.push blk[i]).toList) := by
  obtain ⟨-, -, -, hrest⟩ := h
  rw [ite_eq_right (show ¬ i + 2 = 0 by omega), ite_eq_right (show ¬ i + 2 = 1 by omega)] at hrest
  obtain ⟨-, hbg, hbb, -⟩ := hrest
  intro u hu
  left
  rw [ctx.succ_B i hi] at hu
  simp only [List.mem_append, List.mem_singleton] at hu
  rcases hu with (hu | hu) | rfl
  · obtain ⟨m, hm, hm1, rfl⟩ := List.exists_of_mem_take hu
    rw [hbb m hm, show i + 2 - 2 = i by omega]
    unfold q1Bar
    rw [ite_eq_right (show ¬ i = 0 by omega), ite_eq_left hm1]
    omega
  · obtain ⟨m, hm, hm1, rfl⟩ := List.exists_of_mem_drop hu
    rw [hbb m hm, show i + 2 - 2 = i by omega]
    unfold q1Bar
    rw [ite_eq_right (show ¬ i = 0 by omega), ite_eq_right (show ¬ m < i by omega)]
    omega
  · rw [hbg]; omega

/-- search(q) at depth 1 below s: the output s q t at σ0 + 5, then (a), (b) and the cascade (c) -/
theorem gate_q1 (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n))
    (hS0 : S0.toList = [s]) (ht : b0[t] = 0) (hg : b0[g] = 0) (hB : ∀ j (hj : j < blk.length), b0[blk[j]] = 0) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.steps = σ0 ∧ st.trace.toList = T0⌝⦄
    search G t k q (0 + 1)
    ⦃⇓ r st => ⌜r = 1 ∧ st.S = S0 ∧ st.b[q] = 1 ∧ st.b[g] = 2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = 3) ∧ st.b[t] = 0 ∧
      st.steps = σ0 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 + 3 * blk.length * blk.length + 4 * blk.length + 16 ∧
      ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 5]⌝⦄ := by
  have hpos := ctx.pos
  have hSl : (S0.push q).toList = [s, q] := by rw [Array.toList_push, hS0]; rfl
  have hcall : ∀ (w : Fin n) (S2 : Array (Fin n)) (b2 : Vector Nat n) (σ2 : Nat) (T2 : List (Ev n)),
      ⦃fun st => ⌜st.S = S2 ∧ st.b = b2 ∧ st.steps = σ2 ∧ st.trace.toList = T2⌝⦄ search G t k w (0 + 1 + 1)
      ⦃⇓ r st => ⌜(w = g → S2.toList = [s, q] → (∀ j (hj : j < blk.length), b2[blk[j]] = 0) →
          r = k + 1 ∧ st.S = S2 ∧ st.b[g] = k - 1 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = 0 then k - 2 else k - 3) ∧
          (∀ z, z ≠ g → z ∉ blk → st.b[z] = b2[z]) ∧ st.steps = σ2 + 4 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 ∧ ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = []) ∧
        (w = blk[0] → S2.toList = [s, q] → (∀ j (hj : j < blk.length), 0 < j → b2[blk[j]] = k - 3) → k ≤ b2[g] + 2 →
          r = k + 1 ∧ st.S = S2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = if j = 0 then k - 1 else k - 2) ∧ (∀ z, z ∉ blk → st.b[z] = b2[z]) ∧
          st.steps = σ2 + (blk.length + 1) * sweepCalls blk.length 1 0 ∧ ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = []) ∧
        ((∀ u ∈ G.succ w, k ≤ b2[u] + (0 + 1 + 1) ∨ (u ≠ t ∧ u ∈ (S2.push w).toList)) →
          r = k + 1 ∧ st.S = S2 ∧ st.b = b2.set w.1 (k - (0 + 1 + 1) + 1) w.2 ∧ st.steps = σ2 + 1 + (G.succ w).length ∧ ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = [])⌝⦄ := by
    intro w S2 b2 σ2 T2
    refine (StateM.triple_iff _ _ _).mpr fun st hst => ⟨fun hw hS2 hb2 => ?_, fun hw hS2 hb2 hg2 => ?_, fun hleaf => ?_⟩
    · subst hw
      exact (StateM.triple_iff _ _ _).mp (gate_g2 ctx k hk S2 b2 σ2 T2 hS2 hb2) st hst
    · subst hw
      have hsw := sweep_spec G t k blk [g] [s, q] 2 (k - 3) 1 (ctx.sweep _ 2 (k - 3) 1 (by simp [ctx.s_blk, ctx.q_blk]) rfl (by omega)) 0 (Nat.zero_le _) ctx.pos S2 b2 σ2 T2
      obtain ⟨hr, hS, hbb, hbz, hσ, hE⟩ := (StateM.triple_iff _ _ _).mp hsw st ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2, by simpa using hS2, fun j hj hj0 => hb2 j hj hj0, by simp only [List.mem_singleton, forall_eq]; exact Or.inr hg2⟩
      refine ⟨hr, hS, fun j hj => ?_, hbz, by simpa using hσ, hE⟩
      rw [hbb j hj]
      by_cases hj0 : j = 0
      · rw [ite_eq_left hj0, ite_eq_left hj0]; omega
      · rw [ite_eq_right hj0, ite_eq_right hj0, ite_eq_left (Nat.pos_of_ne_zero hj0)]; omega
    · exact (StateM.triple_iff _ _ _).mp (search_leaf G t k (0 + 1 + 1) w S2 b2 σ2 T2 hleaf) st hst
  have hcasc : ∀ (sd : Nat) (S1 : Array (Fin n)) (b1 : Vector Nat n) (σ1 : Nat) (T1 : List (Ev n)),
      ⦃fun st => ⌜st.S = S1 ∧ st.b = b1 ∧ st.steps = σ1 ∧ st.trace.toList = T1⌝⦄ fruitful G q sd
      ⦃⇓ _ st => ⌜sd = 1 → S1.toList = [s, q] → b1[g] = k - 1 → (∀ j (hj : j < blk.length), b1[blk[j]] = k - 1) →
        st.S = S1 ∧ st.b[q] = 1 ∧ st.b[g] = 2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = 3) ∧ (∀ z, z ≠ q → z ≠ g → z ∉ blk → st.b[z] = b1[z]) ∧
        st.steps = σ1 + blk.length * blk.length + 2 * blk.length + 7 ∧ ∃ E, st.trace.toList = T1 ++ E ∧ obsSteps E = []⌝⦄ := by
    intro sd S1 b1 σ1 T1
    refine (StateM.triple_iff _ _ _).mpr fun st hst hsd hS1 hg1 hB1 => ?_
    subst hsd
    exact (StateM.triple_iff _ _ _).mp (gate_casc ctx k hk S1 b1 σ1 T1 hS1 hg1 hB1) st hst
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hcall, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜q1Inv q t g blk k S0 b0 σ0 T0 xs.prefix.length sd st⌝
  case vc1.step.isTrue.isTrue =>
    -- the output s q t
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hcur := ‹_ = t›
    have hinv := ‹q1Inv q t g blk k S0 b0 σ0 T0 _ _ _›
    simp +zetaDelta only
    rw [ctx.succ_q] at hsplit
    rcases split_cons2 hsplit with ⟨hp, -⟩ | ⟨-, hc⟩ | ⟨j, hj, -, hc⟩
    · rw [hp] at hinv
      simp only [List.length_append, List.length_singleton, hp]
      exact q1Inv_out hinv rfl rfl rfl (by rw [Array.toList_push])
    · exact absurd (hc.symm.trans hcur) (Ne.symm ctx.t_g)
    · exact absurd (hcur ▸ hc ▸ List.getElem_mem hj) ctx.t_blk
  case vc2.step.isTrue.isFalse.isTrue.post.success =>
    -- the calls at g (phase (a)), at B_0 (the sweep with bound 1) and at the later block nodes (leaves)
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hinv := ‹q1Inv q t g blk k S0 b0 σ0 T0 _ _ _›
    have hnt := ‹¬_ = t›
    have hpost := ‹(_ = g → _) ∧ _›
    simp +zetaDelta only at hpost ⊢
    rw [ctx.succ_q] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split_cons2 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩ | ⟨j, hj, hp, hc⟩
    · exact absurd hc hnt
    · rw [hp] at hinv ⊢
      have hb0 := (q1Inv_one hinv).2.1
      obtain ⟨hr, hS', hbg, hbb, hbz, hσ, hE⟩ := hpost.1 hc (by rw [hinv.1, hSl]) (fun j hj => by rw [hb0]; exact hB j hj)
      exact q1Inv_g2 ctx.t_g ctx.t_blk hinv hr hS' hbg hbb hbz hσ hE
    · rw [hp] at hinv ⊢
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        obtain ⟨-, hbg, hbb, -⟩ := q1Inv_two hinv
        obtain ⟨hr, hS', hbb', hbz, hσ, hE⟩ := hpost.2.1 hc (by rw [hinv.1, hSl]) (fun j hj hj0 => by rw [hbb j hj, ite_eq_right (show ¬ j = 0 by omega)]) (by rw [hbg]; omega)
        exact q1Inv_sweep ctx.t_blk hinv hr hS' hbb' hbz hσ hE ctx.g_blk
      · subst hc
        obtain ⟨hr, hS', hb', hσ', hE'⟩ := hpost.2.2 (q1_leaf_cond ctx hj0 hj hinv hk)
        have hlen : (G.succ blk[j]).length = blk.length - 1 + 1 := by rw [ctx.succ_B j hj]; simp; omega
        exact q1Inv_leaf ctx.nodup ctx.g_blk hj0 hj hinv hk ctx.t_blk hr hS' hb' (by rw [hσ', hlen]) hE'
  case vc3.step.isTrue.isFalse.isFalse =>
    -- no successor of q is on the stack
    exfalso
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hin := Classical.not_not.mp ‹¬¬_ ∈ _›
    have hinv := ‹q1Inv q t g blk k S0 b0 σ0 T0 _ _ _›
    simp +zetaDelta only at hin
    rw [hinv.1, mem_stack hSl] at hin
    rw [ctx.succ_q] at hsplit
    rcases split_cons2 hsplit with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨j, hj, -, hc⟩
    · rw [hc] at hin; simp [Ne.symm ctx.s_t, Ne.symm ctx.q_t] at hin
    · rw [hc] at hin; simp [Ne.symm ctx.s_g, Ne.symm ctx.q_g] at hin
    · rw [hc] at hin; simp [getElem_ne_of_not_mem ctx.s_blk j hj, getElem_ne_of_not_mem ctx.q_blk j hj] at hin
  case vc4.step.isFalse =>
    -- no successor of q is pruned
    exfalso
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hng := ‹¬_ + (0 + 1) < k›
    have hinv := ‹q1Inv q t g blk k S0 b0 σ0 T0 _ _ _›
    simp +zetaDelta only at hng
    rw [ctx.succ_q] at hsplit
    rcases split_cons2 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩ | ⟨j, hj, hp, hc⟩
    · rw [hc, hinv.2.1, ht] at hng; omega
    · rw [hp] at hinv
      rw [hc, (q1Inv_one hinv).2.1, hg] at hng; omega
    · rw [hp] at hinv
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        rw [hc, (q1Inv_two hinv).2.2.1 0 hj, ite_eq_left rfl] at hng; omega
      · have hrest := hinv.2.2.2
        rw [ite_eq_right (show ¬ j + 2 = 0 by omega), ite_eq_right (show ¬ j + 2 = 1 by omega)] at hrest
        rw [hc, hrest.2.2.1 j hj, show j + 2 - 2 = j by omega] at hng
        unfold q1Bar at hng
        rw [ite_eq_right (show ¬ j = 0 by omega), ite_eq_right (show ¬ j < j by omega)] at hng
        omega
  case vc5.pre =>
    -- the entry
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = σ0 ∧ _ = T0›
    simp +zetaDelta only
    refine ⟨by rw [hS], by rw [hb], ⟨_, by rw [Array.toList_push, hT], by simp [obsSteps]⟩, ?_⟩
    show k + 1 = k + 1 ∧ _ ∧ _
    exact ⟨rfl, hb, by rw [hσ]⟩
  case vc6.post.success.isTrue.post.success =>
    -- the cascade (c)
    have hinv := ‹q1Inv q t g blk k S0 b0 σ0 T0 _ _ _›
    have hpost := ‹_ = 1 → _›
    rw [ctx.succ_q] at hinv
    obtain ⟨hS, hbt, ⟨E, hE, hobs⟩, hrest⟩ := hinv
    simp only [List.length_cons] at hobs hrest
    rw [ite_eq_right (show ¬ blk.length + 1 + 1 = 0 by omega)] at hobs
    rw [ite_eq_right (show ¬ blk.length + 1 + 1 = 0 by omega), ite_eq_right (show ¬ blk.length + 1 + 1 = 1 by omega)] at hrest
    obtain ⟨hsd, hbg, hbb, hσ⟩ := hrest
    have hbk : ∀ j (hj : j < blk.length), q1Bar k (blk.length + 1 + 1 - 2) j = k - 1 := fun j hj => by
      rw [show blk.length + 1 + 1 - 2 = blk.length by omega]
      unfold q1Bar
      rw [ite_eq_right (show ¬ blk.length = 0 by omega), ite_eq_left hj]
    obtain ⟨hS', hbq', hbg', hbb', hbz', hσ', E', hE', hobs'⟩ := hpost hsd (by rw [hS, hSl]) hbg (fun j hj => by rw [hbb j hj, hbk j hj])
    simp +zetaDelta only
    refine ⟨hsd, by rw [hS', hS]; simp, hbq', hbg', hbb', by rw [hbz' t ctx.q_t.symm ctx.t_g ctx.t_blk, hbt, ht], ?_, ?_⟩
    · rw [hσ', hσ, show blk.length + 1 + 1 - 2 = blk.length by omega]
      unfold q1Cost
      rw [ite_eq_right (show ¬ blk.length = 0 by omega), sweepCalls_one ctx.pos]
      have := q1_arith blk.length (sweepCalls blk.length (k - 3) 0) σ0 ctx.pos
      omega
    · exact trace_obs_trans' (trace_obs_trans' ⟨E, hE, hobs⟩ ⟨E', hE', hobs'⟩) ⟨_, by rw [Array.toList_push], by simp [obsSteps]⟩
  case vc7.post.success.isFalse =>
    -- no raise: sd = 1
    exfalso
    have hinv := ‹q1Inv q t g blk k S0 b0 σ0 T0 _ _ _›
    have hc := ‹¬(_ ≤ k ∧ _)›
    rw [ctx.succ_q] at hinv
    have hrest := hinv.2.2.2
    simp only [List.length_cons] at hrest
    rw [ite_eq_right (show ¬ blk.length + 1 + 1 = 0 by omega), ite_eq_right (show ¬ blk.length + 1 + 1 = 1 by omega)] at hrest
    have hsd := hrest.1
    exact hc ⟨by omega, by omega⟩

/-! ### (d) search(q) at depth 2: the output s g q t -/

/-- the loop of search(q) at depth 2, after p successors: before t, then the output is in the trace -/
def q2Inv (q : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n)) (p : Nat) (st : St n) : Prop :=
  if p = 0 then st.S = S0.push q ∧ st.b = b0 ∧ st.steps = σ0 + 1 ∧ ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []
  else ObsPre T0 [σ0 + 6] st.trace.toList

theorem q2Inv_ext {q : Fin n} {S0 : Array (Fin n)} {b0 : Vector Nat n} {σ0 : Nat} {T0 : List (Ev n)} {p : Nat} {st st' : St n} (h : q2Inv q S0 b0 σ0 T0 p st) (hp : 0 < p)
    (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E) : q2Inv q S0 b0 σ0 T0 (p + 1) st' := by
  unfold q2Inv at h ⊢
  rw [ite_eq_right (show ¬ p = 0 by omega)] at h
  rw [ite_eq_right (show ¬ p + 1 = 0 by omega)]
  exact h.ext hT

theorem gate_q2 (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n))
    (hS0 : S0.toList = [s, g]) (ht : b0[t] = 0) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.steps = σ0 ∧ st.trace.toList = T0⌝⦄
    search G t k q (0 + 1 + 1)
    ⦃⇓ _ st => ⌜ObsPre T0 [σ0 + 6] st.trace.toList⌝⦄ := by
  have hrec := search_ext G t k (0 + 1 + 1 + 1)
  have hcasc := fruitful_ext G q
  have hSl : (S0.push q).toList = [s, g, q] := by rw [Array.toList_push, hS0]; rfl
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hrec, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜q2Inv q S0 b0 σ0 T0 xs.prefix.length st⌝
  case vc1.step.isTrue.isTrue =>
    -- the output s g q t
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hcur := ‹_ = t›
    have hinv := ‹q2Inv q S0 b0 σ0 T0 _ _›
    simp +zetaDelta only
    rw [ctx.succ_q] at hsplit
    rcases split_cons2 hsplit with ⟨hp, -⟩ | ⟨-, hc⟩ | ⟨j, hj, -, hc⟩
    · unfold q2Inv at hinv ⊢
      rw [ite_eq_left hp] at hinv
      obtain ⟨-, -, hσ, E, hE, hobs⟩ := hinv
      simp only [List.length_append, List.length_singleton]
      rw [ite_eq_right (Nat.add_one_ne_zero _)]
      rw [Array.toList_push]
      exact ObsPre.of_output hE hobs (by omega)
    · exact absurd (hc.symm.trans hcur) (Ne.symm ctx.t_g)
    · exact absurd (hcur ▸ hc ▸ List.getElem_mem hj) ctx.t_blk
  case vc2.step.isTrue.isFalse.isTrue.post.success =>
    -- a call after the output: the trace grows
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hinv := ‹q2Inv q S0 b0 σ0 T0 _ _›
    have hnt := ‹¬_ = t›
    have hpost := ‹∃ E, _ = _ ++ E›
    simp +zetaDelta only at hpost ⊢
    rw [ctx.succ_q] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split_cons2 hsplit with ⟨hp, hc⟩ | ⟨hp, -⟩ | ⟨j, hj, hp, -⟩
    · exact absurd hc hnt
    · exact q2Inv_ext hinv (by omega) hpost
    · exact q2Inv_ext hinv (by omega) hpost
  case vc3.step.isTrue.isFalse.isFalse =>
    -- on the stack: not t
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hin := Classical.not_not.mp ‹¬¬_ ∈ _›
    have hinv := ‹q2Inv q S0 b0 σ0 T0 _ _›
    simp +zetaDelta only at hin ⊢
    rw [ctx.succ_q] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split_cons2 hsplit with ⟨hp, hc⟩ | ⟨hp, -⟩ | ⟨j, hj, hp, -⟩
    · exfalso
      unfold q2Inv at hinv
      rw [ite_eq_left hp] at hinv
      rw [hinv.1, mem_stack hSl, hc] at hin
      simp [Ne.symm ctx.s_t, ctx.t_g, Ne.symm ctx.q_t] at hin
    · exact q2Inv_ext hinv (by omega) ⟨[], by simp⟩
    · exact q2Inv_ext hinv (by omega) ⟨[], by simp⟩
  case vc4.step.isFalse =>
    -- pruned: not t
    have hsplit := ‹G.succ q = _ ++ _ :: _›
    have hng := ‹¬_ + (0 + 1 + 1) < k›
    have hinv := ‹q2Inv q S0 b0 σ0 T0 _ _›
    simp +zetaDelta only at hng ⊢
    rw [ctx.succ_q] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split_cons2 hsplit with ⟨hp, hc⟩ | ⟨hp, -⟩ | ⟨j, hj, hp, -⟩
    · exfalso
      unfold q2Inv at hinv
      rw [ite_eq_left hp] at hinv
      rw [hinv.2.1, hc, ht] at hng
      omega
    · exact q2Inv_ext hinv (by omega) ⟨[], by simp⟩
    · exact q2Inv_ext hinv (by omega) ⟨[], by simp⟩
  case vc5.pre =>
    -- the entry
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = σ0 ∧ _ = T0›
    simp +zetaDelta only
    unfold q2Inv
    rw [ite_eq_left (show ([] : List (Fin n)).length = 0 from rfl)]
    exact ⟨by rw [hS], hb, by rw [hσ], _, by rw [Array.toList_push, hT], by simp [obsSteps]⟩
  case vc6.post.success.isTrue.post.success =>
    -- the cascade
    have hinv := ‹q2Inv q S0 b0 σ0 T0 _ _›
    have hpost := ‹∃ E, _ = _ ++ E›
    rw [ctx.succ_q] at hinv
    unfold q2Inv at hinv
    rw [ite_eq_right (show ¬ (t :: g :: blk).length = 0 by simp)] at hinv
    simp +zetaDelta only
    exact (hinv.ext hpost).ext ⟨_, by rw [Array.toList_push]⟩
  case vc7.post.success.isFalse =>
    -- the raise
    have hinv := ‹q2Inv q S0 b0 σ0 T0 _ _›
    rw [ctx.succ_q] at hinv
    unfold q2Inv at hinv
    rw [ite_eq_right (show ¬ (t :: g :: blk).length = 0 by simp)] at hinv
    simp +zetaDelta only
    exact hinv.ext ⟨_, by rw [Array.toList_push, Array.toList_push, List.append_assoc]⟩

/-! ### (d) search(g) at depth 1: the second sweep (bound k - 5), then q -/

/-- the loop of search(g) at depth 1, after p successors (B_0, q, s) -/
def g1Inv (q t g : Fin n) (blk : List (Fin n)) (k : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n)) (p : Nat) (st : St n) : Prop :=
  if p = 0 then st.S = S0.push g ∧ st.b = b0 ∧ st.steps = σ0 + 1 ∧ ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []
  else if p = 1 then st.S = S0.push g ∧ st.b[q] = b0[q] ∧ st.b[t] = b0[t] ∧ st.steps = σ0 + 2 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 ∧
    ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []
  else ObsPre T0 [σ0 + 3 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 + 6] st.trace.toList

theorem g1Inv_ext {q t g : Fin n} {blk : List (Fin n)} {k : Nat} {S0 : Array (Fin n)} {b0 : Vector Nat n} {σ0 : Nat} {T0 : List (Ev n)} {p : Nat} {st st' : St n}
    (h : g1Inv q t g blk k S0 b0 σ0 T0 p st) (hp : 2 ≤ p) (hT : ∃ E, st'.trace.toList = st.trace.toList ++ E) : g1Inv q t g blk k S0 b0 σ0 T0 (p + 1) st' := by
  unfold g1Inv at h ⊢
  rw [ite_eq_right (show ¬ p = 0 by omega), ite_eq_right (show ¬ p = 1 by omega)] at h
  rw [ite_eq_right (show ¬ p + 1 = 0 by omega), ite_eq_right (show ¬ p + 1 = 1 by omega)]
  exact h.ext hT

theorem gate_g1 (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n))
    (hS0 : S0.toList = [s]) (hq : b0[q] = 1) (ht : b0[t] = 0) (hB : ∀ j (hj : j < blk.length), b0[blk[j]] = 3) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.steps = σ0 ∧ st.trace.toList = T0⌝⦄
    search G t k g (0 + 1)
    ⦃⇓ _ st => ⌜ObsPre T0 [σ0 + 3 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 + 6] st.trace.toList⌝⦄ := by
  have hpos := ctx.pos
  have hSl : (S0.push g).toList = [s, g] := by rw [Array.toList_push, hS0]; rfl
  have hcall : ∀ (w : Fin n) (S2 : Array (Fin n)) (b2 : Vector Nat n) (σ2 : Nat) (T2 : List (Ev n)),
      ⦃fun st => ⌜st.S = S2 ∧ st.b = b2 ∧ st.steps = σ2 ∧ st.trace.toList = T2⌝⦄ search G t k w (0 + 1 + 1)
      ⦃⇓ r st => ⌜(w = blk[0] → S2.toList = [s, g] → (∀ j (hj : j < blk.length), 0 < j → b2[blk[j]] = 3) →
          r = k + 1 ∧ st.S = S2 ∧ (∀ z, z ∉ blk → st.b[z] = b2[z]) ∧ st.steps = σ2 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 ∧
          ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = []) ∧
        (w = q → S2.toList = [s, g] → b2[t] = 0 → ObsPre T2 [σ2 + 6] st.trace.toList) ∧ ∃ E, st.trace.toList = T2 ++ E⌝⦄ := by
    intro w S2 b2 σ2 T2
    refine (StateM.triple_iff _ _ _).mpr fun st hst => ⟨fun hw hS2 hb2 => ?_, fun hw hS2 ht2 => ?_, ?_⟩
    · subst hw
      have hsw := sweep_spec G t k blk [g] [s, g] 2 3 (k - 5) (ctx.sweep _ 2 3 (k - 5) (by simp [ctx.s_blk, ctx.g_blk]) rfl (by omega)) 0 (Nat.zero_le _) ctx.pos S2 b2 σ2 T2
      obtain ⟨hr, hS, -, hbz, hσ, hE⟩ := (StateM.triple_iff _ _ _).mp hsw st ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2, by simpa using hS2, fun j hj hj0 => hb2 j hj hj0, by simp⟩
      exact ⟨hr, hS, hbz, by simpa using hσ, hE⟩
    · subst hw
      exact (StateM.triple_iff _ _ _).mp (gate_q2 ctx k hk S2 b2 σ2 T2 hS2 ht2) st hst
    · exact (StateM.triple_iff _ _ _).mp (search_ext G t k (0 + 1 + 1) w T2) st hst.2.2.2
  have hcasc := fruitful_ext G g
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hcall, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜g1Inv q t g blk k S0 b0 σ0 T0 xs.prefix.length st⌝
  case vc1.step.isTrue.isTrue =>
    -- t is not a successor of g
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hcur := ‹_ = t›
    rw [ctx.succ_g'] at hsplit
    exfalso
    rcases split3 hsplit with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩
    · exact ctx.t_blk (by rw [← hcur, hc]; exact List.getElem_mem _)
    · exact ctx.q_t (hc.symm.trans hcur)
    · exact ctx.s_t (hc.symm.trans hcur)
  case vc2.step.isTrue.isFalse.isTrue.post.success =>
    -- the calls at B_0 (the second sweep) and at q (the output); s is on the stack
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hinv := ‹g1Inv q t g blk k S0 b0 σ0 T0 _ _›
    have hpost := ‹(_ = blk[0] → _) ∧ _›
    simp +zetaDelta only at hpost ⊢
    rw [ctx.succ_g'] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split3 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩ | ⟨hp, -⟩
    · unfold g1Inv at hinv ⊢
      rw [ite_eq_left hp] at hinv
      obtain ⟨hS, hb, hσ, hE⟩ := hinv
      obtain ⟨-, hS', hbz, hσ', hE'⟩ := hpost.1 hc (by rw [hS, hSl]) (fun j hj _ => by rw [hb]; exact hB j hj)
      rw [hp, ite_eq_right (show ¬ 0 + 1 = 0 by omega), ite_eq_left rfl]
      exact ⟨by rw [hS', hS], by rw [hbz q ctx.q_blk, hb], by rw [hbz t ctx.t_blk, hb], by omega, trace_obs_trans hE hE'⟩
    · unfold g1Inv at hinv ⊢
      rw [hp, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl] at hinv
      obtain ⟨hS, hbq, hbt, hσ, hE⟩ := hinv
      have hO := hpost.2.1 hc (by rw [hS, hSl]) (by rw [hbt, ht])
      rw [hp, ite_eq_right (show ¬ 1 + 1 = 0 by omega), ite_eq_right (show ¬ 1 + 1 = 1 by omega)]
      have := ObsPre.trans hE hO
      rw [List.nil_append, hσ, show σ0 + 2 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 + 1 + 6 = σ0 + 3 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 + 6 by omega] at this
      exact this
    · exact g1Inv_ext hinv (by omega) hpost.2.2
  case vc3.step.isTrue.isFalse.isFalse =>
    -- on the stack: only s
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hin := Classical.not_not.mp ‹¬¬_ ∈ _›
    have hinv := ‹g1Inv q t g blk k S0 b0 σ0 T0 _ _›
    simp +zetaDelta only at hin ⊢
    rw [ctx.succ_g'] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split3 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩ | ⟨hp, -⟩
    · exfalso
      unfold g1Inv at hinv
      rw [ite_eq_left hp] at hinv
      rw [hinv.1, mem_stack hSl, hc] at hin
      simp [getElem_ne_of_not_mem ctx.s_blk 0 hpos, getElem_ne_of_not_mem ctx.g_blk 0 hpos] at hin
    · exfalso
      unfold g1Inv at hinv
      rw [hp, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl] at hinv
      rw [hinv.1, mem_stack hSl, hc] at hin
      simp [Ne.symm ctx.s_q, ctx.q_g] at hin
    · exact g1Inv_ext hinv (by omega) ⟨[], by simp⟩
  case vc4.step.isFalse =>
    -- pruned: only s
    have hsplit := ‹G.succ g = _ ++ _ :: _›
    have hng := ‹¬_ + (0 + 1) < k›
    have hinv := ‹g1Inv q t g blk k S0 b0 σ0 T0 _ _›
    simp +zetaDelta only at hng ⊢
    rw [ctx.succ_g'] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split3 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩ | ⟨hp, -⟩
    · exfalso
      unfold g1Inv at hinv
      rw [ite_eq_left hp] at hinv
      rw [hinv.2.1, hc, hB 0 hpos] at hng
      omega
    · exfalso
      unfold g1Inv at hinv
      rw [hp, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl] at hinv
      rw [hc, hinv.2.1, hq] at hng
      omega
    · exact g1Inv_ext hinv (by omega) ⟨[], by simp⟩
  case vc5.pre =>
    -- the entry
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = σ0 ∧ _ = T0›
    simp +zetaDelta only
    unfold g1Inv
    rw [ite_eq_left (show ([] : List (Fin n)).length = 0 from rfl)]
    exact ⟨by rw [hS], hb, by rw [hσ], _, by rw [Array.toList_push, hT], by simp [obsSteps]⟩
  case vc6.post.success.isTrue.post.success =>
    -- the cascade
    have hinv := ‹g1Inv q t g blk k S0 b0 σ0 T0 _ _›
    have hpost := ‹∃ E, _ = _ ++ E›
    rw [ctx.succ_g'] at hinv
    unfold g1Inv at hinv
    rw [ite_eq_right (show ¬ [blk[0], q, s].length = 0 by simp), ite_eq_right (show ¬ [blk[0], q, s].length = 1 by simp)] at hinv
    simp +zetaDelta only
    exact (hinv.ext hpost).ext ⟨_, by rw [Array.toList_push]⟩
  case vc7.post.success.isFalse =>
    -- the raise
    have hinv := ‹g1Inv q t g blk k S0 b0 σ0 T0 _ _›
    rw [ctx.succ_g'] at hinv
    unfold g1Inv at hinv
    rw [ite_eq_right (show ¬ [blk[0], q, s].length = 0 by simp), ite_eq_right (show ¬ [blk[0], q, s].length = 1 by simp)] at hinv
    simp +zetaDelta only
    exact hinv.ext ⟨_, by rw [Array.toList_push, Array.toList_push, List.append_assoc]⟩

/-! ### The root call and the run -/

/-- o_2 - o_1 on a gate trap with block size c: two sweeps of the block, re-armed by the cascade in between -/
def gateD1 (c k : Nat) : Nat := (c + 1) * (sweepCalls c (k - 3) 0 + sweepCalls c (k - 5) 0) + 3 * c * c + 4 * c + 21

theorem ObsPre.congr {T0 T : List (Ev n)} {os os' : List Nat} (h : ObsPre T0 os T) (heq : os = os') : ObsPre T0 os' T := heq ▸ h

/-- the loop of search(s) at depth 0, after p successors (q, g) -/
def s0Inv (s q t g : Fin n) (blk : List (Fin n)) (k : Nat) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n)) (p : Nat) (st : St n) : Prop :=
  if p = 0 then st.S = S0.push s ∧ st.b = b0 ∧ st.steps = σ0 + 1 ∧ ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = []
  else if p = 1 then st.S = S0.push s ∧ st.b[q] = 1 ∧ st.b[g] = 2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = 3) ∧ st.b[t] = 0 ∧
    st.steps = σ0 + 2 + ((blk.length + 1) * sweepCalls blk.length (k - 3) 0 + 3 * blk.length * blk.length + 4 * blk.length + 16) ∧
    ∃ E, st.trace.toList = T0 ++ E ∧ obsSteps E = [σ0 + 7]
  else ObsPre T0 [σ0 + 7, σ0 + 7 + gateD1 blk.length k] st.trace.toList

/-- the root call: the outputs s q t at σ0 + 7 and s g q t at σ0 + 7 + D1, with nothing observable in between -/
theorem gate_s0 (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) (S0 : Array (Fin n)) (b0 : Vector Nat n) (σ0 : Nat) (T0 : List (Ev n))
    (hS0 : S0.toList = []) (hq : b0[q] = 0) (ht : b0[t] = 0) (hg : b0[g] = 0) (hB : ∀ j (hj : j < blk.length), b0[blk[j]] = 0) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ st.steps = σ0 ∧ st.trace.toList = T0⌝⦄
    search G t k s 0
    ⦃⇓ _ st => ⌜ObsPre T0 [σ0 + 7, σ0 + 7 + gateD1 blk.length k] st.trace.toList⌝⦄ := by
  have hSl : (S0.push s).toList = [s] := by rw [Array.toList_push, hS0]; rfl
  have hcall : ∀ (w : Fin n) (S2 : Array (Fin n)) (b2 : Vector Nat n) (σ2 : Nat) (T2 : List (Ev n)),
      ⦃fun st => ⌜st.S = S2 ∧ st.b = b2 ∧ st.steps = σ2 ∧ st.trace.toList = T2⌝⦄ search G t k w (0 + 1)
      ⦃⇓ r st => ⌜(w = q → S2.toList = [s] → b2[t] = 0 → b2[g] = 0 → (∀ j (hj : j < blk.length), b2[blk[j]] = 0) →
          r = 1 ∧ st.S = S2 ∧ st.b[q] = 1 ∧ st.b[g] = 2 ∧ (∀ j (hj : j < blk.length), st.b[blk[j]] = 3) ∧ st.b[t] = 0 ∧
          st.steps = σ2 + (blk.length + 1) * sweepCalls blk.length (k - 3) 0 + 3 * blk.length * blk.length + 4 * blk.length + 16 ∧
          ∃ E, st.trace.toList = T2 ++ E ∧ obsSteps E = [σ2 + 5]) ∧
        (w = g → S2.toList = [s] → b2[q] = 1 → b2[t] = 0 → (∀ j (hj : j < blk.length), b2[blk[j]] = 3) →
          ObsPre T2 [σ2 + 3 + (blk.length + 1) * sweepCalls blk.length (k - 5) 0 + 6] st.trace.toList) ∧
        ∃ E, st.trace.toList = T2 ++ E⌝⦄ := by
    intro w S2 b2 σ2 T2
    refine (StateM.triple_iff _ _ _).mpr fun st hst => ⟨fun hw hS2 ht2 hg2 hB2 => ?_, fun hw hS2 hq2 ht2 hB2 => ?_, ?_⟩
    · subst hw
      exact (StateM.triple_iff _ _ _).mp (gate_q1 ctx k hk S2 b2 σ2 T2 hS2 ht2 hg2 hB2) st hst
    · subst hw
      exact (StateM.triple_iff _ _ _).mp (gate_g1 ctx k hk S2 b2 σ2 T2 hS2 hq2 ht2 hB2) st hst
    · exact (StateM.triple_iff _ _ _).mp (search_ext G t k (0 + 1) w T2) st hst.2.2.2
  have hcasc := fruitful_ext G s
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, hcall, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜s0Inv s q t g blk k S0 b0 σ0 T0 xs.prefix.length st⌝
  case vc1.step.isTrue.isTrue =>
    -- t is not a successor of s
    have hsplit := ‹G.succ s = _ ++ _ :: _›
    have hcur := ‹_ = t›
    rw [ctx.succ_s] at hsplit
    exfalso
    rcases split2 hsplit with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact ctx.q_t (hc.symm.trans hcur)
    · exact ctx.t_g (hc.symm.trans hcur).symm
  case vc2.step.isTrue.isFalse.isTrue.post.success =>
    -- the calls at q (the output s q t, (a), (b), (c)) and at g ((d), the output s g q t)
    have hsplit := ‹G.succ s = _ ++ _ :: _›
    have hinv := ‹s0Inv s q t g blk k S0 b0 σ0 T0 _ _›
    have hpost := ‹(_ = q → _) ∧ _›
    simp +zetaDelta only at hpost ⊢
    rw [ctx.succ_s] at hsplit
    simp only [List.length_append, List.length_singleton]
    rcases split2 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩
    · unfold s0Inv at hinv ⊢
      rw [ite_eq_left hp] at hinv
      obtain ⟨hS, hb, hσ, E, hE, hobs⟩ := hinv
      obtain ⟨-, hS', hbq, hbg, hbb, hbt, hσ', E', hE', hobs'⟩ := hpost.1 hc (by rw [hS, hSl]) (by rw [hb, ht]) (by rw [hb, hg]) (fun j hj => by rw [hb]; exact hB j hj)
      rw [hp, ite_eq_right (show ¬ 0 + 1 = 0 by omega), ite_eq_left rfl]
      refine ⟨by rw [hS', hS], hbq, hbg, hbb, hbt, by omega, E ++ E', by rw [hE', hE, List.append_assoc], ?_⟩
      rw [obsSteps_append, hobs, hobs', hσ]
      rfl
    · unfold s0Inv at hinv ⊢
      rw [hp, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl] at hinv
      obtain ⟨hS, hbq, hbg, hbb, hbt, hσ, E, hE, hobs⟩ := hinv
      have hO := hpost.2.1 hc (by rw [hS, hSl]) hbq hbt hbb
      rw [hp, ite_eq_right (show ¬ 1 + 1 = 0 by omega), ite_eq_right (show ¬ 1 + 1 = 1 by omega)]
      refine (ObsPre.trans ⟨E, hE, hobs⟩ hO).congr ?_
      have hmul := Nat.mul_add (blk.length + 1) (sweepCalls blk.length (k - 3) 0) (sweepCalls blk.length (k - 5) 0)
      unfold gateD1
      simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
      omega
  case vc3.step.isTrue.isFalse.isFalse =>
    -- q and g are not on the stack
    exfalso
    have hsplit := ‹G.succ s = _ ++ _ :: _›
    have hin := Classical.not_not.mp ‹¬¬_ ∈ _›
    have hinv := ‹s0Inv s q t g blk k S0 b0 σ0 T0 _ _›
    simp +zetaDelta only at hin
    rw [ctx.succ_s] at hsplit
    unfold s0Inv at hinv
    rcases split2 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩
    · rw [ite_eq_left hp] at hinv
      rw [hinv.1, mem_stack hSl, hc] at hin
      simp [Ne.symm ctx.s_q] at hin
    · rw [hp, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl] at hinv
      rw [hinv.1, mem_stack hSl, hc] at hin
      simp [Ne.symm ctx.s_g] at hin
  case vc4.step.isFalse =>
    -- q and g are not pruned
    exfalso
    have hsplit := ‹G.succ s = _ ++ _ :: _›
    have hng := ‹¬_ + 0 < k›
    have hinv := ‹s0Inv s q t g blk k S0 b0 σ0 T0 _ _›
    simp +zetaDelta only at hng
    rw [ctx.succ_s] at hsplit
    unfold s0Inv at hinv
    rcases split2 hsplit with ⟨hp, hc⟩ | ⟨hp, hc⟩
    · rw [ite_eq_left hp] at hinv
      rw [hinv.2.1, hc, hq] at hng
      omega
    · rw [hp, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl] at hinv
      rw [hc, hinv.2.2.1] at hng
      omega
  case vc5.pre =>
    -- the entry
    obtain ⟨hS, hb, hσ, hT⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ = σ0 ∧ _ = T0›
    simp +zetaDelta only
    unfold s0Inv
    rw [ite_eq_left (show ([] : List (Fin n)).length = 0 from rfl)]
    exact ⟨by rw [hS], hb, by rw [hσ], _, by rw [Array.toList_push, hT], by simp [obsSteps]⟩
  case vc6.post.success.isTrue.post.success =>
    -- no cascade at the root
    have hc := ‹_ ≤ k ∧ _›
    omega
  case vc7.post.success.isFalse =>
    -- the raise of s
    have hinv := ‹s0Inv s q t g blk k S0 b0 σ0 T0 _ _›
    rw [ctx.succ_s] at hinv
    unfold s0Inv at hinv
    rw [ite_eq_right (show ¬ [q, g].length = 0 by simp), ite_eq_right (show ¬ [q, g].length = 1 by simp)] at hinv
    simp +zetaDelta only
    exact hinv.ext ⟨_, by rw [Array.toList_push, Array.toList_push, List.append_assoc]⟩

/-- the run of BS-DFS on a gate trap: the first three observable events are the start at step 0 and the outputs s q t at step 7
    and s g q t at step 7 + D1 -/
theorem gate_run (ctx : GateCtx G s q t g blk) (k : Nat) (hk : 6 ≤ k) :
    ∃ rest, obsSteps (bsdfs G s t k) = [0, 7, 7 + gateD1 blk.length k] ++ rest := by
  have hroot := gate_s0 ctx k hk #[] (Vector.replicate n 0) 0 [Ev.start 0] rfl (by simp) (by simp) (by simp) (fun j hj => by simp)
  unfold bsdfs
  dsimp only
  generalize hx : StateT.run _ _ = x
  have key : ObsPre [] [0, 7, 7 + gateD1 blk.length k] x.2.trace.toList := by
    refine StateM.of_wp_run_eq hx (fun x => ObsPre [] [0, 7, 7 + gateD1 blk.length k] x.2.trace.toList) ?_
    mvcgen [M.tick, M.emit, M.steps, hroot]
    case vc2.post.success =>
      -- the start event, the root call, the term event
      obtain ⟨E1, E2, hT, hE1⟩ := ‹ObsPre [Ev.start 0] _ _›
      simp +zetaDelta only
      refine ObsPre.ext ?_ ⟨_, by rw [Array.toList_push]⟩
      rw [hT]
      refine ⟨[Ev.start 0] ++ E1, E2, by simp, ?_⟩
      rw [obsSteps_append, hE1]
      simp [obsSteps]
  obtain ⟨E1, E2, hT, hE1⟩ := key
  refine ⟨obsSteps E2, ?_⟩
  have hx' : x.run.snd.trace.toList = x.2.trace.toList := rfl
  rw [hx', hT, obsSteps_append, obsSteps_append, hE1]
  rfl

end gate
