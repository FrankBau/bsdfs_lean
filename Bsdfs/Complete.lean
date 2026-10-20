/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Bsdfs.Cascade

/-!
  Proof of `bsdfs_complete_once`: in path mode, every simple s-t path with at most k edges is output exactly once.

  One spec for `search v h` carries the two clauses of the joint induction of sec45_rewrite.tex (Call Completeness, and
  Search Preserves for h > 0, where the early exit at s skips the cascade), together with the facts their proofs use:
  Return Value (lem:return-value), the final barrier write, Fruitless Monotonicity, and the persistence of lower bounds
  (`mon`: a barrier only drops to a value witnessed by a walk avoiding the stack).  No-duplicate output comes from the prefixes:
  outputs of different successors differ at position h + 1.
-/

open Std.Do

set_option mvcgen.warning false

variable {n : Nat}

/-! ## The spec of `search` -/

section
variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- precondition of `search v h` with stack S0 and barriers b0 -/
structure SearchPre (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) : Prop where
  stack : StackPath G s t (S0.toList ++ [v])
  size : S0.size = h
  guard : b0[v] + h ≤ k
  target : b0[t] = 0
  ec : EC G b0 S0.toList

/-- what `search v h` guarantees: N are its outputs, r its return value, b the barriers at exit -/
structure SearchPost (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (r : Nat) (b : Vector Nat n) (N : List (List (Fin n))) : Prop where
  nodup : N.Nodup                                                                    -- obs:no-duplicate-output
  sound : ∀ p ∈ N, G.BoundedPath k s t p ∧ (S0.toList ++ [v]) <+: p                    -- thm:bsdfs-soundness
  complete : ∀ p, G.BoundedPath k s t p → (S0.toList ++ [v]) <+: p → p ∈ N             -- lem:call-complete
  ret_pos : 1 ≤ r                                                                    -- lem:return-value: r is the shortest suffix, or k + 1
  ret_le : r ≤ k + 1
  ret_min : ∀ p ∈ N, r + h + 1 ≤ p.length
  ret_wit : r ≤ k → ∃ p ∈ N, r + h + 1 = p.length
  write_fruitful : r ≤ k → 0 < h → b[v] = r                                           -- the final assignment of search
  write_raise : ¬(r ≤ k ∧ 0 < h) → b[v] = k - h + 1                                    -- fruitless, or the early exit at s
  stack : ∀ x, x ∈ S0.toList → b[x] = b0[x]                                           -- obs:path-barrier-fixed
  target : b[t] = 0                                                                  -- obs:target-barrier
  mon : ∀ y, b0[y] ≤ b[y] ∨ G.WalkLE S0.toList t y b[y]                               -- b[y] drops only to values ≥ dist_{S0}(y, t)
  fruitless : r = k + 1 → (∀ x : Fin n, b0[x] ≤ b[x]) ∧ ∀ x, x ≠ v → b[x] ≤ max b0[x] (k - h)   -- lem:fruitless-monotonicity
  ec : 0 < h → EC G b S0.toList                                                       -- lem:search-preserves-consistency

/-- invariant of the for-loop of `search v h` after the successors pref, with current sd, barriers b and outputs N -/
structure LoopInv (h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (pref : List (Fin n)) (sd : Nat) (b : Vector Nat n) (N : List (List (Fin n))) : Prop where
  nodup : N.Nodup
  sound : ∀ p ∈ N, G.BoundedPath k s t p ∧ ∃ w ∈ pref, (S0.toList ++ [v, w]) <+: p
  complete : ∀ p, G.BoundedPath k s t p → ∀ w ∈ pref, (S0.toList ++ [v, w]) <+: p → p ∈ N
  ret_pos : 1 ≤ sd
  ret_le : sd ≤ k + 1
  ret_min : ∀ p ∈ N, sd + h + 1 ≤ p.length
  ret_wit : sd ≤ k → ∃ p ∈ N, sd + h + 1 = p.length
  bv : b[v] = b0[v]
  stack : ∀ x, x ∈ S0.toList → b[x] = b0[x]
  target : b[t] = 0
  ec : EC G b (S0.toList ++ [v])
  mon : ∀ y, b0[y] ≤ b[y] ∨ G.WalkLE (S0.toList ++ [v]) t y b[y]
  fruitless : sd = k + 1 → (∀ x : Fin n, b0[x] ≤ b[x]) ∧ (∀ x, x ≠ v → b[x] ≤ max b0[x] (k - h)) ∧ ∀ y ∈ pref, y ∉ S0.toList → y ≠ v → k - h ≤ b[y]
  close : ∀ y ∈ pref, y ∉ S0.toList → y ≠ v → y ≠ t → min (k - h) (sd - 1) ≤ b[y] ∨ G.WalkLE (S0.toList ++ [v]) t y b[y]   -- case (III), fruitful
  tgt : t ∈ pref → sd = 1 ∨ k ≤ h                                                     -- the closing edge (v, t)

end

section steps
variable {G : Graph n} {s t : Fin n} {k h : Nat} {v : Fin n} {S0 : Array (Fin n)} {b0 : Vector Nat n}

theorem SearchPre.v_not_mem (pre : SearchPre G s t k h v S0 b0) : v ∉ S0.toList := by
  have := (List.nodup_append.mp pre.stack.2.1).2.2
  exact fun hv => this v hv v (by simp) rfl

theorem SearchPre.t_not_mem (pre : SearchPre G s t k h v S0 b0) : t ∉ S0.toList ++ [v] := pre.stack.2.2.1

theorem SearchPre.length (pre : SearchPre G s t k h v S0 b0) : S0.toList.length = h := by simpa using pre.size

theorem loop_init (pre : SearchPre G s t k h v S0 b0) : LoopInv G s t k h v S0 b0 [] (k + 1) b0 [] where
  nodup := List.nodup_nil
  sound := by simp
  complete := by simp
  ret_pos := by omega
  ret_le := by omega
  ret_min := by simp
  ret_wit := by omega
  bv := rfl
  stack := fun _ _ => rfl
  target := pre.target
  ec := EC.mono (fun z hz => by simp [hz]) pre.ec
  mon := fun _ => Or.inl (Nat.le_refl _)
  fruitless := fun _ => ⟨fun _ => Nat.le_refl _, fun _ _ => Nat.le_max_left _ _, by simp⟩
  close := by simp
  tgt := by simp

/-- Fruitful Return (cor:fruitful-return) -/
theorem SearchPost.fruitful_return {r : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hpost : SearchPost G s t k h v S0 b0 r b N) (hr : r ≤ k) : r + h ≤ k := by
  obtain ⟨p, hp, hlen⟩ := hpost.ret_wit hr
  have := (hpost.sound p hp).1.2.2.2.1
  omega

theorem LoopInv.fruitful_return {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (hsd : sd ≤ k) : sd + h ≤ k := by
  obtain ⟨p, hp, hlen⟩ := hinv.ret_wit hsd
  have := (hinv.sound p hp).1.2.2.2.1
  omega

theorem push_append (S0 : Array (Fin n)) (v w : Fin n) : (S0.push v).toList ++ [w] = S0.toList ++ [v, w] := by simp

theorem loop_prune (pre : SearchPre G s t k h v S0 b0) {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} {w : Fin n} (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (hw : ¬ b[w] + h < k) : LoopInv G s t k h v S0 b0 (pref ++ [w]) sd b N := by
  refine { hinv with sound := ?_, complete := ?_, fruitless := ?_, close := ?_, tgt := ?_ }
  · intro p hp
    obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
    exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact hinv.complete p hp w' hw' hpre
    · simp at hw'; subst hw'
      have := pruning_permissive hinv.ec hinv.target hp hpre
      rw [pre.length] at this
      exact absurd this hw
  · intro hsd
    obtain ⟨h1, h2, h3⟩ := hinv.fruitless hsd
    refine ⟨h1, h2, ?_⟩
    intro y hy hyL hyv
    rcases List.mem_append.mp hy with hy | hy
    · exact h3 y hy hyL hyv
    · simp at hy; subst hy; omega
  · intro y hy hyL hyv hyt
    rcases List.mem_append.mp hy with hy | hy
    · exact hinv.close y hy hyL hyv hyt
    · simp at hy; subst hy; left; omega
  · intro ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hinv.tgt ht
    · simp at ht; subst ht; right; have := hinv.target; omega

theorem loop_output (pre : SearchPre G s t k h v S0 b0) {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (hmem : t ∈ G.succ v) (htp : t ∉ pref) (htest : b[t] + h < k) :
    LoopInv G s t k h v S0 b0 (pref ++ [t]) 1 b (N ++ [S0.toList ++ [v, t]]) := by
  have hhk : h < k := by have := hinv.target; omega
  have hb0 : G.BoundedPath k s t (S0.toList ++ [v, t]) := by
    have := StackPath.bounded pre.stack hmem (by rw [pre.length]; exact hhk)
    simpa using this
  have hlen : (S0.toList ++ [v, t]).length = h + 2 := by simp [pre.length]
  have hnotin : S0.toList ++ [v, t] ∉ N := by
    intro hin
    obtain ⟨_, w', hw', hpre⟩ := hinv.sound _ hin
    have := eq_of_prefix_pair hpre (List.prefix_refl _)
    subst this; exact htp hw'
  refine { hinv with nodup := ?_, sound := ?_, complete := ?_, ret_pos := by omega, ret_le := by omega, ret_min := ?_, ret_wit := ?_, fruitless := ?_, close := ?_, tgt := ?_ }
  · refine List.nodup_append.mpr ⟨hinv.nodup, by simp, ?_⟩
    intro a ha c hc
    simp at hc; subst hc
    exact fun heq => hnotin (heq ▸ ha)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
      exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
    · simp at hp; subst hp
      exact ⟨hb0, t, by simp, List.prefix_refl _⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact List.mem_append_left _ (hinv.complete p hp w' hw' hpre)
    · simp at hw'; subst hw'
      rw [hp.eq_of_prefix_t hpre]; simp
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨_, w', _, hpre⟩ := hinv.sound p hp
      have := prefix_pair_length hpre
      rw [pre.length] at this; omega
    · simp at hp; subst hp; omega
  · intro _
    exact ⟨S0.toList ++ [v, t], by simp, by omega⟩
  · intro h1; omega
  · intro y _ _ _ _; left; omega
  · intro _; left; rfl

theorem loop_onstack {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} {w : Fin n} (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (hws : w ∈ S0.toList ++ [v]) (hwt : w ≠ t) : LoopInv G s t k h v S0 b0 (pref ++ [w]) sd b N := by
  have hws' : w ∈ S0.toList ∨ w = v := by simpa using hws
  refine { hinv with sound := ?_, complete := ?_, fruitless := ?_, close := ?_, tgt := ?_ }
  · intro p hp
    obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
    exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact hinv.complete p hp w' hw' hpre
    · simp at hw'; subst hw'
      exact absurd hpre (hp.not_prefix_of_mem hws)
  · intro hsd
    obtain ⟨h1, h2, h3⟩ := hinv.fruitless hsd
    refine ⟨h1, h2, ?_⟩
    intro y hy hyL hyv
    rcases List.mem_append.mp hy with hy | hy
    · exact h3 y hy hyL hyv
    · simp at hy; subst hy; rcases hws' with h' | h'
      · exact absurd h' hyL
      · exact absurd h' hyv
  · intro y hy hyL hyv hyt
    rcases List.mem_append.mp hy with hy | hy
    · exact hinv.close y hy hyL hyv hyt
    · simp at hy; subst hy; rcases hws' with h' | h'
      · exact absurd h' hyL
      · exact absurd h' hyv
  · intro ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hinv.tgt ht
    · simp at ht; exact absurd ht.symm hwt

theorem loop_child_pre (pre : SearchPre G s t k h v S0 b0) {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} {w : Fin n} (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (hmem : w ∈ G.succ v) (htest : b[w] + h < k) (hwt : w ≠ t) (hwS : w ∉ S0.toList ++ [v]) :
    SearchPre G s t k (h + 1) w (S0.push v) b where
  stack := by rw [Array.toList_push]; exact StackPath.snoc pre.stack hmem hwS hwt
  size := by simp [pre.size]
  guard := by omega
  target := hinv.target
  ec := by rw [Array.toList_push]; exact hinv.ec

theorem loop_child_post {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} {w : Fin n} {d : Nat} {b' : Vector Nat n} {Nc : List (List (Fin n))}
    (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (htest : b[w] + h < k) (hwt : w ≠ t) (hwp : w ∉ pref) (hpost : SearchPost G s t k (h + 1) w (S0.push v) b d b' Nc) :
    LoopInv G s t k h v S0 b0 (pref ++ [w]) (min sd (d + 1)) b' (N ++ Nc) := by
  have hhk : h < k := by omega
  have hsnd : ∀ p ∈ Nc, G.BoundedPath k s t p ∧ (S0.toList ++ [v, w]) <+: p := by
    intro p hp; have := hpost.sound p hp; rw [push_append] at this; exact this
  have hst : ∀ x, x ∈ S0.toList ++ [v] → b'[x] = b[x] := by
    intro x hx; exact hpost.stack x (by rw [Array.toList_push]; exact hx)
  have hmon : ∀ y, b[y] ≤ b'[y] ∨ G.WalkLE (S0.toList ++ [v]) t y b'[y] := by
    intro y; have := hpost.mon y; rw [Array.toList_push] at this; exact this
  have hpos := hinv.ret_pos
  have hle := hinv.ret_le
  have hdpos := hpost.ret_pos
  have hdle := hpost.ret_le
  have hdfr : d ≤ k → d + (h + 1) ≤ k := hpost.fruitful_return
  refine { nodup := ?_, sound := ?_, complete := ?_, ret_pos := by omega, ret_le := by omega, ret_min := ?_, ret_wit := ?_, bv := ?_, stack := ?_, target := hpost.target, ec := ?_, mon := ?_, fruitless := ?_, close := ?_, tgt := ?_ }
  · refine List.nodup_append.mpr ⟨hinv.nodup, hpost.nodup, ?_⟩
    intro a ha c hc heq
    subst heq
    obtain ⟨_, w', hw', hpre⟩ := hinv.sound a ha
    have := eq_of_prefix_pair hpre (hsnd a hc).2
    subst this; exact hwp hw'
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hb, w', hw', hpre⟩ := hinv.sound p hp
      exact ⟨hb, w', List.mem_append_left _ hw', hpre⟩
    · exact ⟨(hsnd p hp).1, w, by simp, (hsnd p hp).2⟩
  · intro p hp w' hw' hpre
    rcases List.mem_append.mp hw' with hw' | hw'
    · exact List.mem_append_left _ (hinv.complete p hp w' hw' hpre)
    · simp at hw'; subst hw'
      exact List.mem_append_right _ (hpost.complete p hp (by rw [push_append]; exact hpre))
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hinv.ret_min p hp; omega
    · have := hpost.ret_min p hp; omega
  · intro hmin
    by_cases hsd : sd ≤ d + 1
    · obtain ⟨p, hp, hlen⟩ := hinv.ret_wit (by omega)
      exact ⟨p, List.mem_append_left _ hp, by omega⟩
    · obtain ⟨p, hp, hlen⟩ := hpost.ret_wit (by omega)
      exact ⟨p, List.mem_append_right _ hp, by omega⟩
  · rw [hst v (by simp)]; exact hinv.bv
  · intro x hx; rw [hst x (by simp [hx])]; exact hinv.stack x hx
  · have := hpost.ec (by omega); rw [Array.toList_push] at this; exact this
  · intro y
    rcases hmon y with h2 | h2
    · rcases hinv.mon y with h1 | h1
      · exact Or.inl (Nat.le_trans h1 h2)
      · exact Or.inr (h1.mono (fun z hz => hz) h2)
    · exact Or.inr h2
  · intro hsd'
    have hsdk : sd = k + 1 := by omega
    have hdk : d = k + 1 := by omega
    obtain ⟨f1, f2, f3⟩ := hinv.fruitless hsdk
    obtain ⟨g1, g2⟩ := hpost.fruitless hdk
    have hbw : b'[w] = k - h := by have := hpost.write_raise (by omega); omega
    refine ⟨fun x => Nat.le_trans (f1 x) (g1 x), ?_, ?_⟩
    · intro x hxv
      by_cases hxw : x = w
      · subst hxw; rw [hbw]; exact Nat.le_max_right _ _
      · have := g2 x hxw; have := f2 x hxv; omega
    · intro y hy hyL hyv
      rcases List.mem_append.mp hy with hy | hy
      · exact Nat.le_trans (f3 y hy hyL hyv) (g1 y)
      · simp at hy; subst hy; omega
  · intro y hy hyL hyv hyt
    rcases List.mem_append.mp hy with hy | hy
    · rcases hmon y with h2 | h2
      · rcases hinv.close y hy hyL hyv hyt with h1 | h1
        · left; omega
        · exact Or.inr (h1.mono (fun z hz => hz) h2)
      · exact Or.inr h2
    · simp at hy; subst hy
      left
      by_cases hd : d ≤ k
      · have := hpost.write_fruitful hd (by omega); omega
      · have := hpost.write_raise (by omega); omega
  · intro ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases hinv.tgt ht with h1 | h1
      · left; omega
      · right; exact h1
    · simp at ht; exact absurd ht.symm hwt

/-- a fruitful sd is the length of a walk from v avoiding the stack below v (lem:fruitful-lower-bound) -/
theorem LoopInv.walk_sd (pre : SearchPre G s t k h v S0 b0) {pref : List (Fin n)} {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 pref sd b N) (hsd : sd ≤ k) : G.WalkLE S0.toList t v sd := by
  obtain ⟨p, hp, hlen⟩ := hinv.ret_wit hsd
  obtain ⟨hb, w, _, hpre⟩ := hinv.sound p hp
  have hw := hb.suffix_walk (prefix_of_pair hpre)
  exact ⟨p.length - S0.toList.length - 1, by rw [pre.length]; omega, hw.mono (fun z hz => by simp [hz])⟩

/-- every bounded path with prefix S0 ++ [v] continues with a successor of v -/
theorem LoopInv.complete' (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (p : List (Fin n)) (hp : G.BoundedPath k s t p) (hpre : (S0.toList ++ [v]) <+: p) : p ∈ N := by
  obtain ⟨w, rest, rfl, hw⟩ := hp.cont hpre pre.t_not_mem
  exact hinv.complete _ hp w hw ⟨rest, by simp⟩

/-- Strict Barrier Invariant (lem:strict-bar-invariant): a fruitful sd is at most the length of every walk from v avoiding S0 -/
theorem LoopInv.strict (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (hsd : sd ≤ k) {l : Nat} (hw : G.Walk S0.toList t v l) : sd ≤ l := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hfr := hinv.fruitful_return hsd
  obtain ⟨R, hRh, hRl, hRe, hRnd, hRX, hRlen⟩ := hw.path
  cases R with
  | nil => simp at hRh
  | cons v' R =>
    simp only [List.head?_cons, Option.some.injEq] at hRh
    subst v'
    have hLv : (S0.toList ++ [v]).Nodup := pre.stack.2.1
    have hvL := pre.v_not_mem
    have hb : G.BoundedPath k s t (S0.toList ++ v :: R) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [head_append_cons]; exact pre.stack.1
      · rw [List.getLast?_append, hRl]; simp
      · refine List.nodup_append.mpr ⟨(List.nodup_append.mp hLv).1, hRnd, ?_⟩
        intro a ha c hc hac
        subst hac
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hvL ha
        · exact hRX a (by simpa using hc) ha
      · simp [pre.length] at hRlen ⊢; omega
      · rw [← Graph.edges_iff_zip]; exact Graph.Edges.append_cons (Graph.edges_of_stack pre.stack) hRe
    have hin := hinv.complete' pre _ hb ⟨R, by simp⟩
    have := hinv.ret_min _ hin
    simp [pre.length] at this hRlen
    omega

/-- exit of a fruitful call: the cascade runs (h > 0) -/
theorem post_fruitful (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b b' : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (hsd : sd ≤ k) (hh : 0 < h) (hc : CascPost G t v sd S0 b b') :
    SearchPost G s t k h v S0 b0 sd b' N := by
  have hfr := hinv.fruitful_return hsd
  have hvL := pre.v_not_mem
  have htv : t ≠ v := fun h' => pre.t_not_mem (by simp [h'])
  refine { nodup := hinv.nodup, sound := ?_, complete := hinv.complete' pre, ret_pos := hinv.ret_pos, ret_le := hinv.ret_le, ret_min := hinv.ret_min, ret_wit := hinv.ret_wit, write_fruitful := fun _ _ => hc.bv, write_raise := ?_, stack := ?_, target := ?_, mon := ?_, fruitless := ?_, ec := ?_ }
  · intro p hp
    obtain ⟨hb, w, _, hpre⟩ := hinv.sound p hp
    exact ⟨hb, prefix_of_pair hpre⟩
  · intro hno; exact absurd ⟨hsd, hh⟩ hno
  · intro x hx; rw [hc.stack x hx]; exact hinv.stack x hx
  · have := hc.low t htv; have := hinv.target; omega
  · intro y
    rcases hc.mon y with h2 | h2
    · rcases hinv.mon y with h1 | h1
      · exact Or.inl (Nat.le_trans h1 h2)
      · exact Or.inr (h1.mono (fun z hz => by simp [hz]) h2)
    · exact Or.inr h2
  · intro h1; omega
  · intro _ x y hxy hx hy
    by_cases hxv : x = v
    · subst hxv
      rw [hc.bv]
      by_cases hyx : y = x
      · subst hyx; rw [hc.bv] at *; omega
      by_cases hyt : y = t
      · subst hyt
        have h1 := hinv.target
        have h2 := hc.low y hyx
        rcases hinv.tgt hxy with h3 | h3
        · omega
        · omega
      -- y off the stack: b'[y] ≥ sd - 1 (case (III) of Search Preserves)
      have hstep : ∀ l, G.Walk S0.toList t y l → sd ≤ l + 1 := fun l hw => hinv.strict pre hsd (.step hxy hy hw)
      rcases hc.mon y with h2 | h2
      · rcases hinv.close y hxy hy hyx hyt with h1 | h1
        · omega
        · obtain ⟨l, hl, hw⟩ := h1
          have := hstep l (hw.mono (fun z hz => by simp [hz]))
          omega
      · obtain ⟨l, hl, hw⟩ := h2
        have := hstep l hw
        omega
    · exact hc.repair hinv.ec x y hxy hx hy hxv

/-- exit of a call without cascade: fruitless, or the early exit at s (h = 0) -/
theorem post_raise (pre : SearchPre G s t k h v S0 b0) {sd : Nat} {b : Vector Nat n} {N : List (List (Fin n))} (hinv : LoopInv G s t k h v S0 b0 (G.succ v) sd b N) (hno : ¬(sd ≤ k ∧ 0 < h)) :
    SearchPost G s t k h v S0 b0 sd (b.set v.1 (k - h + 1) v.2) N := by
  have hvL := pre.v_not_mem
  have htv : t ≠ v := fun h' => pre.t_not_mem (by simp [h'])
  have hguard := pre.guard
  have hbv := hinv.bv
  have hget : ∀ x, x ≠ v → (b.set v.1 (k - h + 1) v.2)[x] = b[x] := by intro x hx; simp [Fin.val_inj, Ne.symm hx]
  have hgetv : (b.set v.1 (k - h + 1) v.2)[v] = k - h + 1 := by simp
  refine { nodup := hinv.nodup, sound := ?_, complete := hinv.complete' pre, ret_pos := hinv.ret_pos, ret_le := hinv.ret_le, ret_min := hinv.ret_min, ret_wit := hinv.ret_wit, write_fruitful := fun h1 h2 => absurd ⟨h1, h2⟩ hno, write_raise := fun _ => hgetv, stack := ?_, target := ?_, mon := ?_, fruitless := ?_, ec := ?_ }
  · intro p hp
    obtain ⟨hb, w, _, hpre⟩ := hinv.sound p hp
    exact ⟨hb, prefix_of_pair hpre⟩
  · intro x hx
    have hxv : x ≠ v := fun h' => hvL (h' ▸ hx)
    rw [hget x hxv]; exact hinv.stack x hx
  · rw [hget t htv]; exact hinv.target
  · intro y
    by_cases hyv : y = v
    · subst hyv; left; rw [hgetv]; omega
    · rw [hget y hyv]
      rcases hinv.mon y with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.mono (fun z hz => by simp [hz]) (Nat.le_refl _))
  · intro hsd
    obtain ⟨f1, f2, _⟩ := hinv.fruitless hsd
    refine ⟨?_, ?_⟩
    · intro x
      by_cases hxv : x = v
      · subst hxv; rw [hgetv]; omega
      · rw [hget x hxv]; exact f1 x
    · intro x hxv; rw [hget x hxv]; exact f2 x hxv
  · intro hh x y hxy hx hy
    have hsd : sd = k + 1 := by have := hinv.ret_le; omega
    obtain ⟨f1, f2, f3⟩ := hinv.fruitless hsd
    by_cases hxv : x = v
    · subst hxv
      rw [hgetv]
      by_cases hyx : y = x
      · subst hyx; rw [hgetv]; omega
      · rw [hget y hyx]; have := f3 y hxy hy hyx; omega
    · rw [hget x hxv]
      by_cases hyv : y = v
      · subst hyv
        rw [hgetv]
        have h1 := f2 x hxv
        have h2 := pre.ec x y hxy hx hy
        omega
      · rw [hget y hyv]
        exact hinv.ec x y hxy (by simp [hx, hxv]) (by simp [hy, hyv])

end steps

/-! ## The joint induction -/

/-- spec of `search v h` (Call Completeness and Search Preserves, with the facts their proofs use); induction on k - h -/
theorem search_spec (G : Graph n) (hG : G.WF) (s t : Fin n) (k h : Nat) (v : Fin n) (S0 : Array (Fin n)) (b0 : Vector Nat n) (O0 : List (List (Fin n))) :
    ⦃fun st => ⌜st.S = S0 ∧ st.b = b0 ∧ outputs st.trace.toList = O0 ∧ SearchPre G s t k h v S0 b0⌝⦄
    search G t k v h
    ⦃⇓ r st => ⌜st.S = S0 ∧ ∃ N, outputs st.trace.toList = O0 ++ N ∧ SearchPost G s t k h v S0 b0 r st.b N⌝⦄ := by
  -- spec of the recursive call; vacuous unless h < k
  have ih : ∀ w (S1 : Array (Fin n)) (b1 : Vector Nat n) (O1 : List (List (Fin n))), ⦃fun st => ⌜st.S = S1 ∧ st.b = b1 ∧ outputs st.trace.toList = O1 ∧ SearchPre G s t k (h + 1) w S1 b1⌝⦄ search G t k w (h + 1) ⦃⇓ r st => ⌜st.S = S1 ∧ ∃ N, outputs st.trace.toList = O1 ++ N ∧ SearchPost G s t k (h + 1) w S1 b1 r st.b N⌝⦄ := by
    intro w S1 b1 O1
    by_cases hk : h < k
    · exact search_spec G hG s t k (h + 1) w S1 b1 O1
    · intro st hP
      exact absurd hP.2.2.2.guard (by omega)
  have hcasc := fruitful_spec G hG t v S0
  rw [search]
  mvcgen [M.push, M.pop, M.tick, M.emit, M.steps, M.bar, M.setBar, M.stack, ih, hcasc] invariants
  · ⇓⟨xs, sd⟩ st => ⌜st.S = S0.push v ∧ ∃ N, outputs st.trace.toList = O0 ++ N ∧ LoopInv G s t k h v S0 b0 xs.prefix sd st.b N⌝
  case vc1.step.isTrue.isTrue =>
    -- closing edge (v, t): output S0 ++ [v, t]
    obtain ⟨-, -, -, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    have hmem := mem_of_eq_append_cons hsplit
    have hnp := not_mem_of_nodup_split (hG.succ_nodup v) hsplit
    have htest := ‹_ + h < k›
    have hcur := ‹_ = t›
    simp +zetaDelta only at htest ⊢
    subst hcur
    refine ⟨hS, N ++ [S0.toList ++ [v, _]], ?_, loop_output pre hinv hmem hnp htest⟩
    simp [hN, hS]
  case vc2.step.isTrue.isFalse.isTrue.pre =>
    -- recursive call: its precondition
    obtain ⟨-, -, -, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hmem := mem_of_eq_append_cons ‹G.succ v = _ ++ _ :: _›
    have htest := ‹_ + h < k›
    have hnt := ‹¬_ = t›
    have hnS := ‹¬_ ∈ _›
    simp +zetaDelta only at htest hnS ⊢
    rw [hS] at hnS ⊢
    exact ⟨trivial, trivial, trivial, loop_child_pre pre hinv hmem htest hnt (by simpa using hnS)⟩
  case vc3.step.isTrue.isFalse.isTrue.post.success =>
    -- recursive call: back in the loop
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    obtain ⟨hS', Nc, hNc, hpost⟩ := ‹_ ∧ ∃ N, _ ∧ SearchPost G s t k (h + 1) _ _ _ _ _ N›
    have hsplit := ‹G.succ v = _ ++ _ :: _›
    have hnp := not_mem_of_nodup_split (hG.succ_nodup v) hsplit
    have htest := ‹_ + h < k›
    have hnt := ‹¬_ = t›
    simp +zetaDelta only at hS' hNc hpost htest
    rw [hS] at hS' hpost
    exact ⟨hS', N ++ Nc, by rw [hNc, hN, List.append_assoc], loop_child_post hinv htest hnt hnp hpost⟩
  case vc4.step.isTrue.isFalse.isFalse =>
    -- successor on the stack
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hnt := ‹¬_ = t›
    have hin := ‹¬¬_ ∈ _›
    simp +zetaDelta only at hin ⊢
    rw [hS] at hin
    have hin' := Classical.not_not.mp hin
    exact ⟨hS, N, hN, loop_onstack hinv (by simpa using hin') hnt⟩
  case vc5.step.isFalse =>
    -- pruned successor
    obtain ⟨-, -, -, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hpr := ‹¬_ + h < k›
    simp +zetaDelta only at hpr ⊢
    exact ⟨hS, N, hN, loop_prune pre hinv hpr⟩
  case vc6.pre =>
    -- entry: push v
    obtain ⟨hS, hb, hout, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    simp +zetaDelta only
    rw [hS, hb]
    exact ⟨rfl, [], by simp [hout], loop_init pre⟩
  case vc7.post.success.isTrue.pre =>
    -- fruitful (h > 0): precondition of the cascade
    obtain ⟨-, -, -, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hc := ‹_ ≤ k ∧ h > 0›
    exact ⟨trivial, trivial, hS, pre.v_not_mem, hinv.walk_sd pre hc.1⟩
  case vc8.post.success.isTrue.post.success =>
    -- fruitful (h > 0): after the cascade, exit and pop
    obtain ⟨-, -, -, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hc := ‹_ ≤ k ∧ h > 0›
    obtain ⟨hS', hout', hcp⟩ := ‹_ = S0.push v ∧ _ ∧ CascPost G t v _ S0 _ _›
    simp +zetaDelta only
    rw [hS']
    exact ⟨by simp, N, by simp [hout', hN], post_fruitful pre hinv hc.1 hc.2 hcp⟩
  case vc9.post.success.isFalse =>
    -- fruitless, or the early exit at s: raise, exit and pop
    obtain ⟨-, -, -, pre⟩ := ‹_ = S0 ∧ _ = b0 ∧ _ ∧ SearchPre G s t k h v S0 b0›
    obtain ⟨hS, N, hN, hinv⟩ := ‹_ = S0.push v ∧ ∃ N, _ ∧ LoopInv G s t k h v S0 b0 _ _ _ N›
    have hc := ‹¬(_ ≤ k ∧ h > 0)›
    simp +zetaDelta only
    rw [hS]
    exact ⟨by simp, N, by simp [hN], post_raise pre hinv hc⟩
termination_by k - h

/-! ## The theorem -/

theorem root_pre {G : Graph n} {s t : Fin n} {k : Nat} (hst : s ≠ t) : SearchPre G s t k 0 s #[] (Vector.replicate n 0) where
  stack := ⟨rfl, by simp, by simpa using Ne.symm hst, by simp⟩
  size := rfl
  guard := by simp
  target := by simp
  ec := by intro x y _ _ _; simp

variable (G : Graph n) (s t : Fin n) (k : Nat)

/-- path mode: every such path is output exactly once -/
theorem bsdfs_complete_once (hG : G.WF) (hst : s ≠ t) : ∀ p, G.BoundedPath k s t p → (outputs (bsdfs G s t k)).count p = 1 := by
  have key : ∃ N, outputs (bsdfs G s t k) = N ∧ N.Nodup ∧ ∀ q, G.BoundedPath k s t q → q ∈ N := by
    refine bsdfs_of_root (fun st => st.S = #[] ∧ st.b = Vector.replicate n 0 ∧ outputs st.trace.toList = [] ∧ SearchPre G s t k 0 s #[] (Vector.replicate n 0))
      (fun T => ∃ N, outputs T = N ∧ N.Nodup ∧ ∀ q, G.BoundedPath k s t q → q ∈ N) ⟨rfl, rfl, rfl, root_pre hst⟩ ?_
    refine (StateM.triple_iff _ _ _).mpr fun st hpre => ?_
    obtain ⟨-, N, hN, hpost⟩ := (StateM.triple_iff _ _ _).mp (search_spec G hG s t k 0 s #[] (Vector.replicate n 0) []) st hpre
    -- every bounded path starts with s, so it has the prefix [s] of the root call
    exact ⟨N, by simp [hN], hpost.nodup, fun q hq => hpost.complete q hq (prefix_of_head hq.1)⟩
  intro p hp
  obtain ⟨N, hN, hnd, hall⟩ := key
  rw [hN]
  exact hnd.count_of_mem (hall p hp)
