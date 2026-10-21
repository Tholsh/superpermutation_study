/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Defs
import Coeff2.Helpers
import Coeff2.Auxiliary

/-!
# Every numbered display fact and every Lemma / Proposition / Theorem / Corollary of the
paper, as Lean statements (all proved)

Statements appear in paper order.  Each docstring names the paper item; displays are
cited by their number ((1)–(15), (prop), (†), (6a), (6b)), results by their LaTeX label
(e.g. `lem:hpv`) and headline name.  A handful of clearly marked *prose facts* — claims
asserted in the paper's running text that the numbered results lean on — are also
included.

The paper assumes `n ≥ 4` throughout its Sections 3–5; the statements below instead
carry sharp per-statement thresholds (`n ≥ 1`, `n ≥ 2`, `n ≥ 3`, or `n ≥ 4` as each
proof actually requires), so several results are slightly more general than the paper's.
-/

namespace Coeff2

open List Walk

/-! ## §1 Introduction -/

/-! The parts of **Theorem [thm:intromain]** are stated at the end of this file: their
proofs consume the §6–§7 results, and Lean requires declaration before use.  (See
`intromain` and `intromain_points` below; the theorem's uniform factorial clause is
`uniform_form` in §7.) -/

/-- Prose fact (§1, intro table): the values of `HPV(n)` for `5 ≤ n ≤ 11`. -/
theorem hpv_point_values :
    HPV 5 = 152 ∧ HPV 6 = 867 ∧ HPV 7 = 5884 ∧ HPV 8 = 46085 ∧
    HPV 9 = 408246 ∧ HPV 10 = 4032007 ∧ HPV 11 = 43908488 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [HPV, Nat.factorial]

/-! ## §2 The graph -/

/-- **Display (prop)** (§2): writing `σ = s_{d+1}⋯s_n t₁⋯t_d` from `π = s₁⋯s_n`
(`d = wt(π,σ)`), the edge is proper precisely when
`{t₁,…,t_h} ≠ {s₁,…,s_h}` for all `1 ≤ h < d`. -/
theorem properStep_iff_prop (n : ℕ) (u v : List ℕ) (hu : IsPermWord n u)
    (hv : IsPermWord n v) :
    ProperStep n u v ↔
      ∀ h, 1 ≤ h → h < wt n u v →
        ((v.drop (n - wt n u v)).take h).toFinset ≠ (u.take h).toFinset := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · constructor
    · intro _ h h1 h2
      rw [wt_eq_zero_of_n_zero] at h2
      omega
    · rintro _ ⟨h, hh1, hh2, -⟩
      rw [wt_eq_zero_of_n_zero] at hh2
      omega
  · obtain ⟨hd1, hdn, hover⟩ := wt_spec (u := u) (v := v) hn (le_of_eq hu.length)
    have hulen := hu.length
    have hvlen := hv.length
    -- the intermediate window at offset `h` in split form
    have hwin : ∀ h, h ≤ n → ((overlapWord n u v).drop h).take n =
        u.drop h ++ (v.drop (n - wt n u v)).take h := by
      intro h hh
      show ((u ++ v.drop (n - wt n u v)).drop h).take n = _
      rw [List.drop_append_of_le_length (by omega : h ≤ u.length), List.take_append]
      congr 1
      · exact List.take_of_length_le (by rw [List.length_drop]; omega)
      · congr 1
        rw [List.length_drop, hulen]
        omega
    -- per-offset: the window is a permutation iff the prefix symbol sets agree
    have hkey : ∀ h, 1 ≤ h → h < wt n u v →
        (IsPermWord n (((overlapWord n u v).drop h).take n) ↔
          ((v.drop (n - wt n u v)).take h).toFinset = (u.take h).toFinset) := by
      intro h hh1 hh2
      rw [hwin h (by omega)]
      have hdisj_ud : ∀ a, a ∈ u.take h → a ∈ u.drop h → False := by
        intro a ha1 ha2
        exact List.disjoint_take_drop hu.nodup (le_refl h) ha1 ha2
      have hndt : ((v.drop (n - wt n u v)).take h).Nodup :=
        (hv.nodup.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)
      have hndu : (u.drop h).Nodup := hu.nodup.sublist (List.drop_sublist _ _)
      have hcup : (u.take h).toFinset ∪ (u.drop h).toFinset = Finset.Icc 1 n := by
        rw [← List.toFinset_append, List.take_append_drop]
        exact hu.toFinset_eq
      constructor
      · rintro ⟨hndw, hfinw⟩
        rw [List.toFinset_append] at hfinw
        have hdisj1 : Disjoint (u.drop h).toFinset
            ((v.drop (n - wt n u v)).take h).toFinset := by
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          rw [List.mem_toFinset] at ha1 ha2
          rw [List.nodup_append] at hndw
          exact hndw.2.2 a ha1 a ha2 rfl
        have hdisj2 : Disjoint (u.drop h).toFinset (u.take h).toFinset := by
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          rw [List.mem_toFinset] at ha1 ha2
          exact hdisj_ud a ha2 ha1
        have h1 : ((v.drop (n - wt n u v)).take h).toFinset =
            ((u.drop h).toFinset ∪ ((v.drop (n - wt n u v)).take h).toFinset) \
              (u.drop h).toFinset := (Finset.union_sdiff_cancel_left hdisj1).symm
        rw [h1, hfinw, ← hcup, Finset.union_comm]
        exact Finset.union_sdiff_cancel_left hdisj2
      · intro hfeq
        constructor
        · rw [List.nodup_append]
          refine ⟨hndu, hndt, ?_⟩
          intro a ha b hb hab
          subst hab
          have hmem : a ∈ (u.take h).toFinset := by
            rw [← hfeq, List.mem_toFinset]
            exact hb
          rw [List.mem_toFinset] at hmem
          exact hdisj_ud a hmem ha
        · rw [List.toFinset_append, hfeq, Finset.union_comm]
          exact hcup
    constructor
    · intro hproper h hh1 hh2 hcon
      exact hproper ⟨h, hh1, hh2, (hkey h hh1 hh2).mpr hcon⟩
    · rintro hne ⟨h, hh1, hh2, hperm⟩
      exact hne h hh1 hh2 ((hkey h hh1 hh2).mp hperm)

/-- Prose fact (§2): every superpermutation gives a covering walk in the proper overlap
graph of length at most the word length (record the permutation windows left to right
and refine improper overlap edges into proper paths). -/
theorem superperm_gives_walk (n : ℕ) (w : List ℕ) (hw : IsSuperperm n w) :
    ∃ W : Walk n, W.Covering ∧ W.len ≤ w.length := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- over the empty alphabet the one-vertex walk on `[]` covers
    refine ⟨⟨[[]], by simp, ?_, List.isChain_singleton _⟩, ?_, ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨List.nodup_nil, by simp⟩
    · intro x hx
      have hlen : x = [] := List.length_eq_zero_iff.mp hx.length
      rw [hlen]
      exact List.mem_singleton_self _
    · show 0 + (List.zipWith (wt 0) [[]] [] ).sum ≤ w.length
      simp
  · -- record the permutation windows, and refine the edges into proper paths
    set Q := (List.range (w.length + 1 - n)).filter
      (fun p => decide (((w.drop p).take n).Nodup ∧
        ((w.drop p).take n).toFinset = Finset.Icc 1 n)) with hQ
    have hQmem : ∀ p, p ∈ Q ↔
        p < w.length + 1 - n ∧ IsPermWord n ((w.drop p).take n) := by
      intro p
      rw [hQ, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact Iff.rfl
    have hwinQ : ∀ v, IsPermWord n v → ∃ p ∈ Q, (w.drop p).take n = v := by
      intro v hv
      obtain ⟨s, t, hst⟩ := hw v hv
      have hdrop : w.drop s.length = v ++ t := by
        rw [← hst, List.append_assoc, List.drop_left]
      have hwin : (w.drop s.length).take n = v := by
        rw [hdrop, List.take_left' hv.length]
      have hlen_w : w.length = s.length + n + t.length := by
        have h := congrArg List.length hst
        simp only [List.length_append, hv.length] at h
        omega
      refine ⟨s.length, (hQmem _).mpr ⟨by omega, by rw [hwin]; exact hv⟩, hwin⟩
    have hQpair : Q.Pairwise (· < ·) := by
      rw [hQ]
      exact List.Pairwise.sublist List.filter_sublist List.pairwise_lt_range
    have hQbound : ∀ p ∈ Q, p + n ≤ w.length ∧ IsPermWord n ((w.drop p).take n) := by
      intro p hp
      obtain ⟨h1, h2⟩ := (hQmem p).mp hp
      exact ⟨by omega, h2⟩
    -- build a proper covering walk over the window positions
    have hbuild : ∀ (tl : List ℕ) (a : ℕ), (a :: tl).Pairwise (· < ·) →
        (∀ p ∈ a :: tl, p + n ≤ w.length ∧ IsPermWord n ((w.drop p).take n)) →
        ∃ W : Walk n, (∀ p ∈ a :: tl, (w.drop p).take n ∈ W.verts) ∧
          W.vert 0 = (w.drop a).take n ∧
          W.wtW + a ≤ (a :: tl).getLast (List.cons_ne_nil a tl) := by
      intro tl
      induction tl with
      | nil =>
        intro a _ hprops
        obtain ⟨-, hperm⟩ := hprops a List.mem_cons_self
        refine ⟨⟨[(w.drop a).take n], by simp, ?_, List.isChain_singleton _⟩,
          ?_, rfl, ?_⟩
        · intro x hx
          rw [List.mem_singleton] at hx
          subst hx
          exact hperm
        · intro p hp
          rw [List.mem_singleton] at hp
          subst hp
          exact List.mem_singleton_self _
        · show (List.zipWith (wt n) [(w.drop a).take n] []).sum + a ≤ a
          simp
      | cons b tl' ih =>
        intro a hpair hprops
        have hab : a < b := (List.pairwise_cons.mp hpair).1 b List.mem_cons_self
        have hpair' : (b :: tl').Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
        have hprops' : ∀ p ∈ b :: tl',
            p + n ≤ w.length ∧ IsPermWord n ((w.drop p).take n) :=
          fun p hp => hprops p (List.mem_cons_of_mem a hp)
        obtain ⟨W₂, hW₂mem, hW₂0, hW₂w⟩ := ih b hpair' hprops'
        obtain ⟨hbounda, hperma⟩ := hprops a List.mem_cons_self
        obtain ⟨hboundb, hpermb⟩ := hprops' b List.mem_cons_self
        have hwt := wt_le_pos_gap (w := w) hn hab hboundb hperma
        obtain ⟨W₁, hW₁0, hW₁l, hW₁w⟩ := exists_proper_path hn
          (wt n ((w.drop a).take n) ((w.drop b).take n)) _ _ hperma hpermb (le_refl _)
        have hseam : W₁.verts.getLastD [] = W₂.vert 0 := by
          rw [hW₁l, hW₂0]
        refine ⟨W₁.glue W₂ hseam, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · refine Walk.glue_mem_left W₁ W₂ hseam ?_
            rw [← hW₁0]
            exact W₁.vert_mem W₁.numVerts_pos
          · exact Walk.glue_mem_right W₁ W₂ hseam (hW₂mem p hp)
        · rw [Walk.glue_vert_zero]
          exact hW₁0
        · rw [Walk.glue_wtW]
          have hlast : (a :: b :: tl').getLast (List.cons_ne_nil _ _) =
              (b :: tl').getLast (List.cons_ne_nil _ _) := List.getLast_cons _
          rw [hlast]
          omega
    -- `Q` is nonempty (the reference permutation is a window)
    have hQne : Q ≠ [] := by
      obtain ⟨p, hp, -⟩ := hwinQ (refList n)
        ⟨refList_nodup n, refList_toFinset n⟩
      exact List.ne_nil_of_mem hp
    obtain ⟨q0, Q', hQeq⟩ := List.exists_cons_of_ne_nil hQne
    have hpair0 : (q0 :: Q').Pairwise (· < ·) := by rw [← hQeq]; exact hQpair
    have hbound0 : ∀ p ∈ q0 :: Q',
        p + n ≤ w.length ∧ IsPermWord n ((w.drop p).take n) := by
      intro p hp
      exact hQbound p (by rw [hQeq]; exact hp)
    obtain ⟨W, hWmem, -, hWw⟩ := hbuild Q' q0 hpair0 hbound0
    refine ⟨W, ?_, ?_⟩
    · intro v hv
      obtain ⟨p, hpQ, hpv⟩ := hwinQ v hv
      rw [← hpv]
      exact hWmem p (by rw [← hQeq]; exact hpQ)
    · have hlastQ : (q0 :: Q').getLast (List.cons_ne_nil _ _) + n ≤ w.length := by
        have hmem := List.getLast_mem (List.cons_ne_nil q0 Q')
        exact (hbound0 _ hmem).1
      show n + W.wtW ≤ w.length
      omega

/-- Prose fact (§2), displayed: `Λ(n) ≤ S(n)`. -/
theorem lam_le_S (n : ℕ) : Lam n ≤ S n := by
  have hne : {m | ∃ w : List ℕ, IsSuperperm n w ∧ w.length = m}.Nonempty :=
    ⟨(trivialSuperperm n).length, trivialSuperperm n,
      isSuperperm_trivialSuperperm n, rfl⟩
  refine le_csInf hne ?_
  rintro m ⟨w, hw, rfl⟩
  obtain ⟨W, hcov, hlen⟩ := superperm_gives_walk n w hw
  exact le_trans (Nat.sInf_le ⟨W, hcov, rfl⟩) hlen

/-- **Proposition [prop:exactmodel] (The walk model is exact)**: `Λ(n) = S(n)` for all
`n ≥ 1`. -/
theorem lam_eq_S (n : ℕ) (hn : 1 ≤ n) : Lam n = S n := by
  refine le_antisymm (lam_le_S n) ?_
  -- an optimal covering walk exists; its word is a superpermutation of length `Λ(n)`
  have hne : {m | ∃ W : Walk n, W.Covering ∧ W.len = m}.Nonempty := by
    obtain ⟨W, hW⟩ := covering_walk_exists n
    exact ⟨W.len, W, hW, rfl⟩
  obtain ⟨W, hWcov, hWlen⟩ := Nat.sInf_mem hne
  change W.len = Lam n at hWlen
  have hsuper : IsSuperperm n (wordOf n W.verts) := by
    intro v hv
    exact word_infix_wordOf hn W.verts v (hWcov v hv) W.isPerm
  have hlen : (wordOf n W.verts).length = W.len :=
    wordOf_length hn W.verts W.ne W.isPerm
  calc S n ≤ (wordOf n W.verts).length := Nat.sInf_le ⟨wordOf n W.verts, hsuper, rfl⟩
    _ = Lam n := by rw [hlen, hWlen]

/-! ## §3 The HPV accounting — prose facts -/

/-- Prose fact (§3): there are `(n−1)!` cyclic classes of permutations of `[n]`. -/
theorem card_perm_rotClasses (n : ℕ) :
    {O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O}.ncard =
      (n - 1).factorial := by
  have h1 : n + 1 - 1 - 1 = n - 1 := by omega
  rw [permClasses_eq_coe, Set.ncard_coe_finset, card_classesOf, Nat.card_Icc, h1]

/-- Prose fact (§3): each cyclic class of permutations of `[n]` has size `n`.
(The paper states this for the orbits of the rotation; `n ≥ 1` is implicit.) -/
theorem card_rotClass_members (n : ℕ) (hn : 1 ≤ n) (O : RotClass)
    (hO : ∃ w, IsPermWord n w ∧ rotClass w = O) :
    {w | rotClass w = O}.ncard = n := by
  obtain ⟨w, hw, rfl⟩ := hO
  rw [ncard_classMembers hw.nodup (hw.ne_nil hn), hw.length]

/-- Prose fact (§3): the weight-2 door always leaves the current cyclic class.
(False at `n = 2`, where the door `12 → 21` is the rotation; stated for `n ≥ 3`,
sharper than the paper's standing `n ≥ 4`.) -/
theorem door_leaves_class (n : ℕ) (hn : 3 ≤ n) (σ : List ℕ) (hσ : IsPermWord n σ) :
    rotClass (door σ) ≠ rotClass σ := by
  intro hcon
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hσ.ne_nil (by omega))
  obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
    rcases t with _ | ⟨b, s⟩
    · have := hσ.length; simp at this; omega
    · exact ⟨b, s, rfl⟩
  have hslen : s.length = n - 2 := by
    have := hσ.length
    simp at this
    omega
  have hsne : s ≠ [] := by
    intro h0
    rw [h0] at hslen
    simp at hslen
    omega
  have hnd := hσ.nodup
  have has : a ∉ b :: s := (List.nodup_cons.mp hnd).1
  have hbs : b ∉ s := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hsnd : s.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
  -- rewrite both sides as `⋯ ++ [a]` and use last-symbol rigidity
  have hd1 : door (a :: b :: s) = (s ++ [b]) ++ [a] := by
    show (a :: b :: s).drop 2 ++ [(a :: b :: s).getD 1 0, (a :: b :: s).getD 0 0] = _
    simp
  have hr1 : rotClass (a :: b :: s) = rotClass ((b :: s) ++ [a]) :=
    rotClass_eq_iff.mpr ⟨1, by simp⟩
  have hkey : rotClass ((s ++ [b]) ++ [a]) = rotClass ((b :: s) ++ [a]) := by
    rw [← hd1, hcon, hr1]
  have hndsb : ((s ++ [b]) ++ [a]).Nodup := by
    rw [← hd1]
    have hperm : door (a :: b :: s) ~ a :: b :: s := by
      rw [hd1]
      calc (s ++ [b]) ++ [a] ~ [a] ++ (s ++ [b]) := List.perm_append_comm
        _ ~ [a] ++ ([b] ++ s) := (List.Perm.append_left [a] List.perm_append_comm)
        _ = a :: b :: s := rfl
    exact hperm.nodup_iff.mpr hnd
  have heq : s ++ [b] = b :: s :=
    isRotated_concat_inj hndsb (rotClass_eq_iff.mp hkey)
  -- but `s ++ [b]` and `b :: s` differ in their head for nonempty `s`
  obtain ⟨c, s', rfl⟩ := List.exists_cons_of_ne_nil hsne
  have hhead : c = b := by
    have := congrArg (fun l => l.getD 0 0) heq
    simpa using this
  rw [hhead] at hbs
  simp at hbs

/-- Prose fact (§3): `V(L)` is closed under cyclic rotation (deleting `α` from `ρ(σ)`
yields a cyclic rotation of `del_α(σ)`). -/
theorem V_closed_rotation {n : ℕ} (L : MarkedLoop) (σ : List ℕ) (hσ : σ ∈ V n L) :
    rho σ ∈ V n L :=
  V_closed_rotate L hσ 1

/-- Prose fact (§3): a permutation lies in the marked 2-loop it generates. -/
theorem mem_V_genLoop (n : ℕ) (σ : List ℕ) (hσ : IsPermWord n σ) :
    σ ∈ V n (genLoop σ) := by
  refine ⟨hσ, ?_⟩
  show rotClass (σ.erase (σ.getLastD 0)) = rotClass σ.dropLast
  rw [erase_getLastD hσ.nodup]

/-- Prose fact (§3): each marked 2-loop contains `n(n−1)` permutations.
(Paper text; stated for `n ≥ 2` — at `n = 1` the unique loop has a single vertex.) -/
theorem card_V (n : ℕ) (hn : 2 ≤ n) (L : MarkedLoop) (hL : IsMarkedLoop n L) :
    (V n L).ncard = n * (n - 1) := by
  classical
  obtain ⟨u₀, hu₀K⟩ := Quotient.exists_rep L.2
  have hu₀K' : rotClass u₀ = L.2 := hu₀K
  have hu₀ : u₀.Nodup ∧ u₀.toFinset = Finset.Icc 1 n \ {L.1} := hL.2 u₀ hu₀K'
  have hαIcc : L.1 ∈ Finset.Icc 1 n := hL.1
  have hlen : u₀.length = n - 1 := by
    rw [← List.toFinset_card_of_nodup hu₀.1, hu₀.2, Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hαIcc, Nat.card_Icc]
    omega
  have hαu₀ : L.1 ∉ u₀ := by
    intro h
    rw [← List.mem_toFinset, hu₀.2] at h
    simp at h
  -- the parametrization by (rotation amount, insertion position)
  set f : ℕ × ℕ → List ℕ :=
    fun p => (u₀.rotate p.1).take p.2 ++ L.1 :: (u₀.rotate p.1).drop p.2 with hf
  have huk : ∀ k : ℕ, (u₀.rotate k).Nodup ∧ (u₀.rotate k).length = n - 1 ∧
      L.1 ∉ u₀.rotate k ∧ (u₀.rotate k).toFinset = Finset.Icc 1 n \ {L.1} := by
    intro k
    refine ⟨(List.rotate_perm u₀ k).nodup_iff.mpr hu₀.1,
      by rw [List.length_rotate]; exact hlen, ?_, ?_⟩
    · intro h
      exact hαu₀ ((List.rotate_perm u₀ k).mem_iff.mp h)
    · rw [List.toFinset_eq_of_perm _ _ (List.rotate_perm u₀ k), hu₀.2]
  have hfperm : ∀ p : ℕ × ℕ, f p ~ L.1 :: u₀.rotate p.1 := by
    intro p
    show (u₀.rotate p.1).take p.2 ++ L.1 :: (u₀.rotate p.1).drop p.2 ~ _
    calc (u₀.rotate p.1).take p.2 ++ L.1 :: (u₀.rotate p.1).drop p.2
        ~ L.1 :: ((u₀.rotate p.1).take p.2 ++ (u₀.rotate p.1).drop p.2) :=
          List.perm_middle
      _ = L.1 :: u₀.rotate p.1 := by rw [List.take_append_drop]
  have hfisPerm : ∀ p : ℕ × ℕ, IsPermWord n (f p) := by
    intro p
    obtain ⟨hnd, hlen', hnotmem, hfin⟩ := huk p.1
    constructor
    · exact (hfperm p).nodup_iff.mpr (List.nodup_cons.mpr ⟨hnotmem, hnd⟩)
    · rw [List.toFinset_eq_of_perm _ _ (hfperm p), List.toFinset_cons, hfin,
        Finset.sdiff_singleton_eq_erase, Finset.insert_erase hαIcc]
  have hferase : ∀ p : ℕ × ℕ, (f p).erase L.1 = u₀.rotate p.1 := by
    intro p
    obtain ⟨hnd, hlen', hnotmem, hfin⟩ := huk p.1
    show ((u₀.rotate p.1).take p.2 ++ L.1 :: (u₀.rotate p.1).drop p.2).erase L.1 = _
    rw [List.erase_append_right _ (fun h => hnotmem (List.mem_of_mem_take h)),
      List.erase_cons_head, List.take_append_drop]
  have hfmem : ∀ p ∈ (Finset.range (n - 1)) ×ˢ (Finset.range n), f p ∈ V n L := by
    intro p _
    refine ⟨hfisPerm p, ?_⟩
    rw [hferase p, ← hu₀K']
    exact (rotClass_eq_iff.mpr ⟨p.1, rfl⟩).symm
  -- the parametrization is onto `V(L)`
  have himage : V n L = ↑(((Finset.range (n - 1)) ×ˢ (Finset.range n)).image f) := by
    ext σ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_range]
    constructor
    · rintro ⟨hσ, hσK⟩
      have hασ : L.1 ∈ σ := by
        rw [← List.mem_toFinset, hσ.toFinset_eq]
        exact hαIcc
      obtain ⟨t, r, hsplit⟩ := List.append_of_mem hασ
      have hnd : σ.Nodup := hσ.nodup
      rw [hsplit, List.nodup_append] at hnd
      have hαt : L.1 ∉ t := by
        intro h
        exact hnd.2.2 L.1 h L.1 (List.mem_cons_self) rfl
      have herase2 : σ.erase L.1 = t ++ r := by
        rw [hsplit, List.erase_append_right _ hαt, List.erase_cons_head]
      have hclass : rotClass (t ++ r) = rotClass u₀ := by
        rw [← herase2, hσK, hu₀K']
      obtain ⟨m, hm⟩ := rotClass_eq_iff.mp hclass.symm
      have hlenpos : 0 < u₀.length := by omega
      have hrot : u₀.rotate (m % u₀.length) = t ++ r := by
        rw [List.rotate_mod]
        exact hm
      have hjlen : t.length + 1 + r.length = n := by
        have := hσ.length
        rw [hsplit] at this
        simp at this
        omega
      refine ⟨(m % u₀.length, t.length), ⟨by rw [← hlen]; exact Nat.mod_lt _ hlenpos,
        by omega⟩, ?_⟩
      show (u₀.rotate (m % u₀.length)).take t.length ++
        L.1 :: (u₀.rotate (m % u₀.length)).drop t.length = σ
      rw [hrot, List.take_left, List.drop_left, hsplit]
    · rintro ⟨p, hp, rfl⟩
      exact hfmem p (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp.1,
        Finset.mem_range.mpr hp.2⟩)
  -- injectivity of the parametrization
  have hinj : Set.InjOn f ↑((Finset.range (n - 1)) ×ˢ (Finset.range n)) := by
    rintro ⟨k, j⟩ hp ⟨k', j'⟩ hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hp'
    have hkk' : k = k' := by
      have he := congrArg (fun l => l.erase L.1) heq
      simp only [hferase ⟨k, j⟩, hferase ⟨k', j'⟩] at he
      exact rotate_injOn_lt hu₀.1 (by omega) (by omega) he
    subst hkk'
    have hjj' : j = j' := by
      obtain ⟨hnd, hlen', hnotmem, -⟩ := huk k
      exact insert_pos_inj hnotmem (by omega) (by omega) heq
    rw [hjj']
  rw [himage, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj,
    Finset.card_product, Finset.card_range, Finset.card_range]
  rw [Nat.mul_comm]

/-- Prose fact (§3): there are `n·(n−2)!` marked 2-loops. -/
theorem card_markedLoops (n : ℕ) :
    {L : MarkedLoop | IsMarkedLoop n L}.ncard = n * (n - 2).factorial := by
  classical
  have hset : {L : MarkedLoop | IsMarkedLoop n L} =
      ↑((Finset.Icc 1 n).biUnion
        (fun α => ({α} : Finset ℕ) ×ˢ classesOf (Finset.Icc 1 n \ {α}))) := by
    ext L
    simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Finset.mem_product, Finset.mem_singleton, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨L.1, h1, rfl, mem_classesOf_iff_forall.mpr h2⟩
    · rintro ⟨α, hα, hL1, hK⟩
      refine ⟨by rw [hL1]; exact hα, ?_⟩
      rw [← hL1] at hK
      exact mem_classesOf_iff_forall.mp hK
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · have hterm : ∀ α ∈ Finset.Icc 1 n,
        (({α} : Finset ℕ) ×ˢ classesOf (Finset.Icc 1 n \ {α})).card =
          (n - 2).factorial := by
      intro α hα
      have h2 : n + 1 - 1 - 1 - 1 = n - 2 := by omega
      rw [Finset.card_product, Finset.card_singleton, one_mul, card_classesOf,
        Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hα, Nat.card_Icc, h2]
    have h3 : n + 1 - 1 = n := by omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Nat.card_Icc, h3]
  · intro α hα β hβ hαβ
    show Disjoint (({α} : Finset ℕ) ×ˢ classesOf (Finset.Icc 1 n \ {α}))
      (({β} : Finset ℕ) ×ˢ classesOf (Finset.Icc 1 n \ {β}))
    rw [Finset.disjoint_left]
    rintro ⟨x, K⟩ hx hx'
    rw [Finset.mem_product, Finset.mem_singleton] at hx hx'
    exact hαβ (hx.1 ▸ hx'.1 ▸ rfl)

/-- Prose fact (§3): a single permutation lies in one marked loop for each possible
deleted symbol (`n` of them). -/
theorem card_loops_through (n : ℕ) (σ : List ℕ) (hσ : IsPermWord n σ) :
    {L : MarkedLoop | IsMarkedLoop n L ∧ σ ∈ V n L}.ncard = n := by
  classical
  have hset : {L : MarkedLoop | IsMarkedLoop n L ∧ σ ∈ V n L} =
      ↑((Finset.Icc 1 n).image
        (fun α => ((α, rotClass (σ.erase α)) : MarkedLoop))) := by
    ext L
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨hL, hσV⟩
      exact ⟨L.1, hL.1, Prod.ext rfl hσV.2⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨isMarkedLoop_marker_erase hσ hα, hσ, rfl⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn
    (fun α _ β _ h => congrArg Prod.fst h), Nat.card_Icc]
  omega

/-- Prose fact (§3): with the active-loop convention, every visited permutation lies in
the active marked loop `H_t`. -/
theorem vert_mem_activeLoop {n : ℕ} (W : Walk n) (t : ℕ) (ht : t < W.numVerts) :
    W.vert t ∈ V n (W.activeLoop t) := by
  suffices h : ∀ s, s < W.numVerts → W.vert s ∈ V n (W.activeLoop s) from h t ht
  intro s
  induction s with
  | zero =>
    intro hs
    exact mem_V_genLoop n _ (W.isPerm _ (by
      rw [W.vert_eq_getElem hs]; exact List.getElem_mem _))
  | succ s ih =>
    intro hs
    have hs' : s < W.numVerts := by omega
    have hperm1 : IsPermWord n (W.vert (s + 1)) := W.isPerm _ (by
      rw [W.vert_eq_getElem hs]; exact List.getElem_mem _)
    have hperm0 : IsPermWord n (W.vert s) := W.isPerm _ (by
      rw [W.vert_eq_getElem hs']; exact List.getElem_mem _)
    show W.vert (s + 1) ∈ V n (if 2 ≤ wt n (W.vert s) (W.vert (s + 1)) then
      genLoop (W.vert (s + 1)) else W.activeLoop s)
    split_ifs with hw
    · exact mem_V_genLoop n _ hperm1
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h1 : W.vert (s + 1) = [] := List.length_eq_zero_iff.mp hperm1.length
        have h2 : W.vert s = [] := List.length_eq_zero_iff.mp hperm0.length
        rw [h1, ← h2]
        exact ih hs'
      · have hw1 : wt n (W.vert s) (W.vert (s + 1)) = 1 := by
          have := (wt_spec hn (le_of_eq hperm0.length) (v := W.vert (s + 1))).1
          omega
        rw [eq_rho_of_wt_one hn hperm0 hperm1 hw1]
        exact V_closed_rotation _ _ (ih hs')

/-- Prose fact (§3): a covering walk enters at least `n!/(n(n−1)) = (n−2)!` marked
2-loops. -/
theorem covering_loops_lower {n : ℕ} (W : Walk n) (hW : W.Covering) :
    (n - 2).factorial ≤ W.vStat := by
  classical
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n ≤ 1`: the right side is at least 1 because the initial loop is entered
    have h1 : (n - 2).factorial = 1 := by
      have h2 : n - 2 = 0 := by omega
      rw [h2]
      rfl
    rw [h1]
    have hpos : 0 < W.vStat := by
      rw [Walk.vStat, Set.ncard_pos W.entered_finite]
      exact ⟨W.activeLoop 0, 0, W.numVerts_pos, rfl⟩
    omega
  · -- `n ≥ 2`: every permutation lies in the `V(L)` of some entered loop
    have hcov : {w | IsPermWord n w} ⊆ ⋃ L ∈ W.entered_finite.toFinset, V n L := by
      intro w hw
      obtain ⟨t, ht, hvt⟩ : ∃ t, t < W.numVerts ∧ W.vert t = w := by
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem (hW w hw)
        exact ⟨i, hi, by rw [W.vert_eq_getElem hi, hiw]⟩
      simp only [Set.mem_iUnion, exists_prop, Set.Finite.mem_toFinset]
      exact ⟨W.activeLoop t, ⟨t, ht, rfl⟩, by rw [← hvt]; exact vert_mem_activeLoop W t ht⟩
    have hbound := ncard_le_sum_of_cover W.entered_finite.toFinset (V n) hcov
      (fun L _ => (permWords_finite n).subset (fun σ hσ => hσ.1))
    have hsum : ∑ L ∈ W.entered_finite.toFinset, (V n L).ncard =
        W.vStat * (n * (n - 1)) := by
      rw [Finset.sum_congr rfl (fun L hL => card_V n hn L
        (W.isMarkedLoop_of_entered (by omega) (W.entered_finite.mem_toFinset.mp hL)))]
      rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [Walk.vStat, Set.ncard_eq_toFinset_card _ W.entered_finite]
    rw [ncard_permWords, hsum] at hbound
    have hfact : n.factorial = (n - 2).factorial * (n * (n - 1)) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp only [Nat.add_sub_cancel]
      have e1 : m + 2 - 1 = m + 1 := by omega
      rw [e1, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
      ring
    rw [hfact] at hbound
    exact Nat.le_of_mul_le_mul_right hbound (Nat.mul_pos (by omega) (by omega))

/-! ## §3 The HPV accounting — results -/

/-- **Lemma [lem:deltac] (Increment of `c`)**: appending one edge `π_m → π_{m+1}`
(here: edge `i`, from `vert i` to `vert (i+1)`), the only cyclic class whose completion
status can change is the class of the source; consequently `Δc ∈ {0,1}`, and `Δc = 1`
iff position `m` is the first occurrence of `π_m` and every other vertex of its cyclic
class occurs before it. -/
theorem increment_of_c {n : ℕ} (W : Walk n) (i : ℕ) (hi : i + 1 < W.numVerts) :
    (∀ O : RotClass, O ≠ rotClass (W.vert i) →
      ((W.pre (i + 1)).Completed O ↔ (W.pre i).Completed O)) ∧
    (W.dc i = 0 ∨ W.dc i = 1) ∧
    (W.dc i = 1 ↔
      (∀ s < i, W.vert s ≠ W.vert i) ∧
        ∀ w, rotClass w = rotClass (W.vert i) → w ≠ W.vert i →
          ∃ s < i, W.vert s = w) := by
  have hi0 : i < W.numVerts := by omega
  have hsucc := W.take_succ_vert hi0
  -- Part 1: only the class of the source can change status.
  have part1 : ∀ O : RotClass, O ≠ rotClass (W.vert i) →
      ((W.pre (i + 1)).Completed O ↔ (W.pre i).Completed O) := by
    intro O hO
    rw [W.completed_pre_iff hi, W.completed_pre_iff hi0]
    constructor
    · intro h w hw
      have h2 := h w hw
      rw [hsucc, List.mem_append] at h2
      rcases h2 with h2 | h2
      · exact h2
      · rw [List.mem_singleton] at h2
        subst h2
        exact absurd hw.symm hO
    · intro h w hw
      rw [hsucc, List.mem_append]
      exact Or.inl (h w hw)
  have hfin1 : {O | (W.pre (i + 1)).Completed O}.Finite := (W.pre (i + 1)).completed_finite
  have hfin0 : {O | (W.pre i).Completed O}.Finite := (W.pre i).completed_finite
  have hsub : {O | (W.pre i).Completed O} ⊆ {O | (W.pre (i + 1)).Completed O} := by
    intro O hO
    rw [Set.mem_setOf_eq, W.completed_pre_iff hi]
    rw [Set.mem_setOf_eq, W.completed_pre_iff hi0] at hO
    intro w hw
    rw [hsucc, List.mem_append]
    exact Or.inl (hO w hw)
  have hsub2 : {O | (W.pre (i + 1)).Completed O} ⊆
      insert (rotClass (W.vert i)) {O | (W.pre i).Completed O} := by
    intro O hO
    rw [Set.mem_insert_iff]
    by_cases hO' : O = rotClass (W.vert i)
    · exact Or.inl hO'
    · exact Or.inr ((part1 O hO').mp hO)
  have hc1 : (W.pre (i + 1)).cStat = {O | (W.pre (i + 1)).Completed O}.ncard := rfl
  have hc0 : (W.pre i).cStat = {O | (W.pre i).Completed O}.ncard := rfl
  have hmono : (W.pre i).cStat ≤ (W.pre (i + 1)).cStat := by
    rw [hc0, hc1]
    exact Set.ncard_le_ncard hsub hfin1
  have hbound : (W.pre (i + 1)).cStat ≤ (W.pre i).cStat + 1 := by
    rw [hc0, hc1]
    calc {O | (W.pre (i + 1)).Completed O}.ncard
        ≤ (insert (rotClass (W.vert i)) {O | (W.pre i).Completed O}).ncard :=
          Set.ncard_le_ncard hsub2 (hfin0.insert _)
      _ ≤ {O | (W.pre i).Completed O}.ncard + 1 := Set.ncard_insert_le _ _
  -- Characterization of the newly-completed class.
  have hchar : rotClass (W.vert i) ∈ {O | (W.pre (i + 1)).Completed O} \
        {O | (W.pre i).Completed O} ↔
      ((∀ s < i, W.vert s ≠ W.vert i) ∧
        ∀ w, rotClass w = rotClass (W.vert i) → w ≠ W.vert i →
          ∃ s < i, W.vert s = w) := by
    rw [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_setOf_eq,
      W.completed_pre_iff hi, W.completed_pre_iff hi0]
    constructor
    · rintro ⟨h1, h0⟩
      constructor
      · intro s hs hcon
        apply h0
        intro w hw
        have h2 := h1 w hw
        rw [hsucc, List.mem_append] at h2
        rcases h2 with h2 | h2
        · exact h2
        · rw [List.mem_singleton] at h2
          subst h2
          exact W.mem_take_vert.mpr ⟨s, hs, by omega, hcon⟩
      · intro w hw hne
        have h2 := h1 w hw
        rw [hsucc, List.mem_append] at h2
        rcases h2 with h2 | h2
        · obtain ⟨s, hs1, _, hs3⟩ := W.mem_take_vert.mp h2
          exact ⟨s, hs1, hs3⟩
        · rw [List.mem_singleton] at h2
          exact absurd h2 hne
    · rintro ⟨hfirst, hothers⟩
      constructor
      · intro w hw
        rw [hsucc, List.mem_append]
        by_cases hne : w = W.vert i
        · exact Or.inr (by rw [List.mem_singleton]; exact hne)
        · obtain ⟨s, hs1, hs3⟩ := hothers w hw hne
          exact Or.inl (W.mem_take_vert.mpr ⟨s, hs1, by omega, hs3⟩)
      · intro hcon
        have h2 := hcon (W.vert i) rfl
        obtain ⟨s, hs1, _, hs3⟩ := W.mem_take_vert.mp h2
        exact hfirst s hs1 hs3
  -- dc = 1 iff the source class is newly completed.
  have hdc_iff : W.dc i = 1 ↔ rotClass (W.vert i) ∈
      {O | (W.pre (i + 1)).Completed O} \ {O | (W.pre i).Completed O} := by
    constructor
    · intro hdc
      have hlt : (W.pre i).cStat < (W.pre (i + 1)).cStat := by
        unfold Walk.dc at hdc
        omega
      have hne : {O | (W.pre i).Completed O} ≠ {O | (W.pre (i + 1)).Completed O} := by
        intro he
        rw [hc0, hc1, he] at hlt
        omega
      obtain ⟨O, hO1, hO0⟩ := Set.exists_of_ssubset
        (ssubset_of_subset_of_ne hsub (fun he => hne he))
      by_cases hO' : O = rotClass (W.vert i)
      · rw [← hO']
        exact ⟨hO1, hO0⟩
      · exact absurd ((part1 O hO').mp hO1) hO0
    · rintro ⟨h1, h0⟩
      have heq : {O | (W.pre (i + 1)).Completed O} =
          insert (rotClass (W.vert i)) {O | (W.pre i).Completed O} :=
        Set.Subset.antisymm hsub2 (Set.insert_subset h1 hsub)
      have : (W.pre (i + 1)).cStat = (W.pre i).cStat + 1 := by
        rw [hc0, hc1, heq, Set.ncard_insert_of_notMem h0 hfin0]
      unfold Walk.dc
      omega
  refine ⟨part1, ?_, ?_⟩
  · unfold Walk.dc
    omega
  · rw [hdc_iff, hchar]

/-- **Lemma [lem:hpv] (HPV monovariant), display (1)**: for every walk `W`,
`wt(W) ≥ p(W) + c(W) + v(W) − 2` (stated additively to avoid truncated
subtraction).  Stated for `1 ≤ n`, sharper than the paper's standing `n ≥ 4`: at `n = 0` the
degenerate two-vertex walk `[], []` has `p + c + v = 3 > 2 = wt + 2`. -/
theorem hpv_monovariant {n : ℕ} (hn : 1 ≤ n) (W : Walk n) :
    W.pStat + W.cStat + W.vStat ≤ W.wtW + 2 :=
  W.monovariant_of_pos hn

/-- Prose fact (§3): for a covering walk, `p(W) = n!`. -/
theorem covering_pStat {n : ℕ} (W : Walk n) (hW : W.Covering) :
    W.pStat = n.factorial := by
  have hset : {w | w ∈ W.verts} = {w | IsPermWord n w} := by
    ext w
    exact ⟨fun h => W.isPerm w h, fun h => hW w h⟩
  rw [Walk.pStat, hset, ncard_permWords]

/-- Prose fact (§3): for a covering walk, `c(W) ≥ (n−1)! − 1` (only the class of the
final vertex can fail to be completed before the final vertex). -/
theorem covering_cStat {n : ℕ} (W : Walk n) (hW : W.Covering) :
    (n - 1).factorial - 1 ≤ W.cStat := by
  classical
  -- every permutation class except possibly the class of the final vertex is completed
  have hsub : {O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O} \
      {rotClass (W.verts.getLast W.ne)} ⊆ {O | W.Completed O} := by
    rintro O ⟨⟨w₀, hw₀, rfl⟩, hOne⟩
    intro w hw
    have hwperm : IsPermWord n w :=
      isPermWord_of_isRotated hw₀ (rotClass_eq_iff.mp hw).symm
    have hwverts : w ∈ W.verts := hW w hwperm
    conv at hwverts => rw [← List.dropLast_append_getLast W.ne]
    rw [List.mem_append] at hwverts
    rcases hwverts with h | h
    · exact h
    · rw [List.mem_singleton] at h
      refine absurd ?_ hOne
      rw [← hw, h]
      exact Set.mem_singleton _
  have hle : ({O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O} \
      {rotClass (W.verts.getLast W.ne)}).ncard ≤ W.cStat :=
    Set.ncard_le_ncard hsub W.completed_finite
  have hcard := card_perm_rotClasses n
  by_cases hmem : rotClass (W.verts.getLast W.ne) ∈
      {O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O}
  · rw [Set.ncard_sdiff_singleton_of_mem hmem, hcard] at hle
    exact hle
  · rw [Set.sdiff_singleton_eq_self hmem, hcard] at hle
    omega

/-- Prose fact (§3), displayed: the HPV lower bound `Λ(n) ≥ HPV(n)`. -/
theorem hpv_lower_bound (n : ℕ) : HPV n ≤ Lam n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : HPV 0 = 0 := by decide
    omega
  · have hne : {m | ∃ W : Walk n, W.Covering ∧ W.len = m}.Nonempty := by
      obtain ⟨W, hW⟩ := covering_walk_exists n
      exact ⟨W.len, W, hW, rfl⟩
    obtain ⟨W, hWcov, hWlen⟩ := Nat.sInf_mem hne
    change W.len = Lam n at hWlen
    have h1 := hpv_monovariant hn W
    have hp := covering_pStat W hWcov
    have hc := covering_cStat W hWcov
    have hv := covering_loops_lower W hWcov
    have hfp := n.factorial_pos
    have hfc := (n - 1).factorial_pos
    have hfv := (n - 2).factorial_pos
    have hlen : W.len = n + W.wtW := rfl
    unfold HPV
    omega

/-- Prose fact (§3): the excess statistics are nonnegative for covering walks —
the weight defect `e(W)`.  (With `1 ≤ n`: at `n = 0` this fails for the degenerate
covering walk `[], []` over the empty alphabet.) -/
theorem eStat_nonneg {n : ℕ} (hn : 1 ≤ n) (W : Walk n) (hW : W.Covering) :
    0 ≤ W.eStat := by
  have h := hpv_monovariant hn W
  unfold Walk.eStat
  push_cast
  omega

/-- Prose fact (§3): nonnegativity of the cyclic-class surplus `r(W)` for covering
walks. -/
theorem rStat_nonneg {n : ℕ} (W : Walk n) (hW : W.Covering) : 0 ≤ W.rStat := by
  have h := covering_cStat W hW
  have h1 := (n - 1).factorial_pos
  unfold Walk.rStat
  omega

/-- Prose fact (§3): nonnegativity of the marked-2-loop surplus `ℓ(W)` for covering
walks. -/
theorem ellStat_nonneg {n : ℕ} (W : Walk n) (hW : W.Covering) : 0 ≤ W.ellStat := by
  have h := covering_loops_lower W hW
  unfold Walk.ellStat
  omega

/-- **Display (2)** (§3), the exact excess identity: for a covering walk,
`len(W) = HPV(n) + e(W) + r(W) + ℓ(W)`. -/
theorem excess_identity {n : ℕ} (W : Walk n) (hW : W.Covering) :
    (W.len : ℤ) = HPV n + W.eStat + W.rStat + W.ellStat := by
  have hp := covering_pStat W hW
  have h3 : 3 ≤ n.factorial + (n - 1).factorial + (n - 2).factorial + n := by
    have h1 := n.factorial_pos
    have h2 := (n - 1).factorial_pos
    have h4 := (n - 2).factorial_pos
    omega
  have hHPV : (HPV n : ℤ) = (n.factorial : ℤ) + ((n - 1).factorial : ℤ) +
      ((n - 2).factorial : ℤ) + (n : ℤ) - 3 := by
    rw [HPV, Nat.cast_sub h3]
    push_cast
    ring
  rw [Walk.len]
  push_cast
  rw [hHPV, Walk.eStat, Walk.rStat, Walk.ellStat, hp]
  push_cast
  ring

/-! ## §4 First entries, breaks, and defect positions

Encoding-bridge facts: the paper *lists* the entered loops as `E₀,…,E_{v(W)−1}` in order
of first entry, with pairwise distinct labels.  In this formalization the list is the
enumeration `Efe` along the increasing first-entry times `tauIdx`; the following five
statements say this enumeration behaves as the paper's list does. -/

/-- Encoding bridge (§4): the number of first-entry times is `v(W)`. -/
theorem numFE_eq_vStat {n : ℕ} (W : Walk n) : W.numFE = W.vStat := by
  show (setOf W.IsFirstEntryTime).ncard = {L | W.Entered L}.ncard
  rw [W.entered_eq_image, Set.ncard_image_of_injOn W.activeLoop_injOn_firstEntries]

/-- Encoding bridge (§4): the first-entry times `τ_i` are strictly increasing. -/
theorem tauIdx_strictMono {n : ℕ} (W : Walk n) (i : ℕ) (hi : i + 1 < W.numFE) :
    W.tauIdx i < W.tauIdx (i + 1) :=
  W.tauIdx_lt_tauIdx (Nat.lt_succ_self i) hi

/-- Encoding bridge (§4): the labels `E_i` are pairwise distinct. -/
theorem Efe_injective {n : ℕ} (W : Walk n) (i k : ℕ) (hi : i < W.numFE)
    (hk : k < W.numFE) (hik : i ≠ k) : W.Efe i ≠ W.Efe k := by
  intro heq
  have htne : W.tauIdx i ≠ W.tauIdx k := by
    rcases Nat.lt_or_ge i k with h | h
    · exact Nat.ne_of_lt (W.tauIdx_lt_tauIdx h hk)
    · exact Nat.ne_of_gt (W.tauIdx_lt_tauIdx (by omega) hi)
  exact htne (W.activeLoop_injOn_firstEntries (W.isFirstEntry_tauIdx hi)
    (W.isFirstEntry_tauIdx hk) heq)

/-- Encoding bridge (§4): each `E_i` (`i < v(W)`) is an entered loop. -/
theorem Efe_entered {n : ℕ} (W : Walk n) (i : ℕ) (hi : i < W.numFE) :
    W.Entered (W.Efe i) :=
  ⟨W.tauIdx i, (W.isFirstEntry_tauIdx hi).1, rfl⟩

/-- Encoding bridge (§4): every entered loop occurs in the list `E₀,…,E_{v(W)−1}`. -/
theorem entered_eq_Efe {n : ℕ} (W : Walk n) (L : MarkedLoop) (hL : W.Entered L) :
    ∃ i < W.numFE, W.Efe i = L := by
  have hmem : L ∈ W.activeLoop '' (setOf W.IsFirstEntryTime) := by
    rw [← W.entered_eq_image]; exact hL
  obtain ⟨T, hT, hTL⟩ := hmem
  obtain ⟨i, hi, hnth⟩ :=
    Nat.exists_lt_card_finite_nth_eq W.firstEntrySet_finite hT
  have hi' : i < W.numFE := by rw [W.numFE_eq_card]; exact hi
  refine ⟨i, hi', ?_⟩
  show W.activeLoop (W.tauIdx i) = L
  rw [W.tauIdx_eq_nth i hi', hnth, hTL]

/-- Prose fact (§4): `E_i = L(x_i)` — a first entry is either the start of the walk or
a nonrotation arrival, and in both cases the activated loop is the one generated by the
arriving vertex. -/
theorem Efe_eq_genLoop_xEntry {n : ℕ} (W : Walk n) (i : ℕ) (hi : i < W.numFE) :
    W.Efe i = genLoop (W.xEntry i) :=
  W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx hi)

/-- Prose fact (§4): the phased successor has period exactly `n−2` for fixed final
marker — the periodicity half: `M^{n−2}(x) = x`.  (Stated for `n ≥ 3`, sharper than the
paper's standing `n ≥ 4`; the split `u^{(n−2)} = βγr` needs `n ≥ 3`.) -/
theorem msucc_period (n : ℕ) (hn : 3 ≤ n) (x : List ℕ) (hx : IsPermWord n x) :
    (Msucc n)^[n - 2] x = x := by
  obtain ⟨T, b, α, rfl⟩ : ∃ T b α, x = T ++ [b, α] := by
    rcases List.eq_nil_or_concat x with rfl | ⟨y, α, hy⟩
    · exact absurd hx.length (by simp; omega)
    · rcases List.eq_nil_or_concat y with rfl | ⟨T, b, hT⟩
      · rw [hy] at hx
        exact absurd hx.length (by simp; omega)
      · exact ⟨T, b, α, by rw [hy, hT]; simp⟩
  have hTlen : T.length = n - 2 := by
    have := hx.length
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  have key : ∀ j, (Msucc n)^[j] (T ++ [b, α]) = T.rotate j ++ [b, α] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      have hrotlen : (T.rotate j).length = n - 2 := by
        rw [List.length_rotate]; exact hTlen
      obtain ⟨c, T', hcT⟩ := List.exists_cons_of_ne_nil (l := T.rotate j) (by
        intro h0
        rw [h0] at hrotlen
        simp at hrotlen
        omega)
      have hnd : ((c :: T') ++ [b, α]).Nodup := by
        rw [← hcT]
        exact ((List.rotate_perm T j).append_right [b, α]).nodup_iff.mpr hx.nodup
      rw [hcT, msucc_step c b α T' (by rw [← hcT]; exact hrotlen) hnd]
      have hnext : T' ++ [c] = T.rotate (j + 1) := by
        have h1 : (c :: T').rotate 1 = T' ++ [c] := by simp
        rw [← h1, ← hcT, List.rotate_rotate]
      rw [hnext]
  rw [key (n - 2), ← hTlen, List.rotate_length]

/-- Prose fact (§4): the exactness half of the period claim: no smaller positive
iterate of `M` fixes `x`. -/
theorem msucc_period_exact (n : ℕ) (hn : 3 ≤ n) (x : List ℕ) (hx : IsPermWord n x)
    (k : ℕ) (hk0 : 0 < k) (hk : k < n - 2) : (Msucc n)^[k] x ≠ x := by
  obtain ⟨T, b, α, rfl⟩ : ∃ T b α, x = T ++ [b, α] := by
    rcases List.eq_nil_or_concat x with rfl | ⟨y, α, hy⟩
    · exact absurd hx.length (by simp; omega)
    · rcases List.eq_nil_or_concat y with rfl | ⟨T, b, hT⟩
      · rw [hy] at hx
        exact absurd hx.length (by simp; omega)
      · exact ⟨T, b, α, by rw [hy, hT]; simp⟩
  have hTlen : T.length = n - 2 := by
    have := hx.length
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  have key : ∀ j, (Msucc n)^[j] (T ++ [b, α]) = T.rotate j ++ [b, α] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      have hrotlen : (T.rotate j).length = n - 2 := by
        rw [List.length_rotate]; exact hTlen
      obtain ⟨c, T', hcT⟩ := List.exists_cons_of_ne_nil (l := T.rotate j) (by
        intro h0
        rw [h0] at hrotlen
        simp at hrotlen
        omega)
      have hnd : ((c :: T') ++ [b, α]).Nodup := by
        rw [← hcT]
        exact ((List.rotate_perm T j).append_right [b, α]).nodup_iff.mpr hx.nodup
      rw [hcT, msucc_step c b α T' (by rw [← hcT]; exact hrotlen) hnd]
      have hnext : T' ++ [c] = T.rotate (j + 1) := by
        have h1 : (c :: T').rotate 1 = T' ++ [c] := by simp
        rw [← h1, ← hcT, List.rotate_rotate]
      rw [hnext]
  rw [key k]
  intro hcon
  have hTk : T.rotate k = T := List.append_cancel_right hcon
  have hTnd : T.Nodup := (List.nodup_append.mp hx.nodup).1
  have hklen : k < T.length := by omega
  have h0len : 0 < T.length := by omega
  have h1 : (T.rotate k)[0]? = T[0]? := by rw [hTk]
  rw [List.getElem?_rotate h0len, Nat.zero_add, Nat.mod_eq_of_lt hklen,
    List.getElem?_eq_getElem hklen, List.getElem?_eq_getElem h0len] at h1
  have h2 := Option.some_inj.mp h1
  have := (hTnd.getElem_inj_iff).mp h2
  omega

/-- Prose fact (§4): any consecutive string `E_s, E_{s+1}, …, E_t` with
`x_{j+1} = M(x_j)` for every `s ≤ j < t` has at most `n−2` terms. -/
theorem canonical_run_le {n : ℕ} (W : Walk n) (hW : W.Covering) (hn : 3 ≤ n)
    (s t : ℕ) (hst : s ≤ t) (ht : t < W.numFE)
    (hrun : ∀ j, s ≤ j → j < t → W.xEntry (j + 1) = Msucc n (W.xEntry j)) :
    t - s + 1 ≤ n - 2 := by
  by_contra hcon
  push_neg at hcon
  -- iterate the successor along the run
  have hiter : ∀ k, k ≤ n - 2 → W.xEntry (s + k) = (Msucc n)^[k] (W.xEntry s) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply', ← ih (by omega)]
      exact hrun (s + k) (by omega) (by omega)
  have hxs : IsPermWord n (W.xEntry s) :=
    W.vert_isPerm (W.isFirstEntry_tauIdx (by omega : s < W.numFE)).1
  have hper : W.xEntry (s + (n - 2)) = W.xEntry s := by
    rw [hiter (n - 2) (le_refl _), msucc_period n hn _ hxs]
  have hEfe : W.Efe (s + (n - 2)) = W.Efe s := by
    rw [Efe_eq_genLoop_xEntry W _ (by omega), Efe_eq_genLoop_xEntry W _ (by omega),
      hper]
  exact Efe_injective W _ _ (by omega) (by omega) (by omega) hEfe

/-- **Display (3)** (§4): the breaks cut the entered marked-2-loop sequence into at most
`|A| + 1` blocks, whence `v(W) ≤ (|A|+1)(n−2)`.  (Stated for `n ≥ 3`, sharper than the
paper's standing `n ≥ 4`; the display fails at `n = 2`.) -/
theorem block_bound {n : ℕ} (W : Walk n) (hW : W.Covering) (hn : 3 ≤ n) :
    W.vStat ≤ (W.breakSet.ncard + 1) * (n - 2) := by
  have hrun : ∀ i, i < W.numFE → i - W.blockStart i ≤ n - 3 := by
    intro i hi
    have hb := (W.blockStart_spec i).1
    have hcanon := canonical_run_le W hW hn (W.blockStart i) i hb hi ?_
    · omega
    · intro j hj1 hj2
      have hnb := W.blockStart_no_break hj1 hj2
      by_contra hne
      exact hnb ⟨by omega, hne⟩
  have h := W.numFE_add_le (n - 3) hrun ∅ (fun b hb => absurd hb (Finset.notMem_empty b))
  rw [Finset.card_empty] at h
  have he : n - 3 + 1 = n - 2 := by omega
  rw [he] at h
  rw [← numFE_eq_vStat]
  omega

/-- Prose fact (§4): the local defects are nonnegative, `d_i ≥ 0` (from the proof of
Lemma [lem:hpv]). -/
theorem defect_nonneg {n : ℕ} (W : Walk n) (hn : 1 ≤ n) (i : ℕ)
    (hi : i + 1 < W.numVerts) :
    0 ≤ W.defect i :=
  W.defect_nonneg_of_pos hn hi

/-- Prose fact (§4): `Σ_i d_i = e(W)`. -/
theorem defect_sum {n : ℕ} (W : Walk n) :
    ∑ i ∈ Finset.range (W.numVerts - 1), W.defect i = W.eStat := by
  have key : ∀ t, t < W.numVerts →
      ∑ i ∈ Finset.range t, W.defect i
        = ((W.pre t).wtW : ℤ) + 2 -
            (((W.pre t).pStat : ℤ) + ((W.pre t).cStat : ℤ) + ((W.pre t).vStat : ℤ)) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Finset.range_zero, Finset.sum_empty, W.wtW_pre_zero, W.pStat_pre_zero,
        W.cStat_pre_zero, W.vStat_pre_zero]
      norm_num
    | succ t ih =>
      intro ht
      rw [Finset.sum_range_succ, ih (by omega)]
      unfold Walk.defect Walk.dp Walk.dc Walk.dv
      rw [W.wtW_pre_succ ht]
      push_cast
      ring
  have hfin := key (W.numVerts - 1) (by have := W.numVerts_pos; omega)
  rw [hfin, W.wtW_pre_last, W.pStat_pre_last, W.cStat_pre_last, W.vStat_pre_last]
  unfold Walk.eStat
  push_cast
  ring

/-- **Display (4)** (§4): `|P| ≤ e(W)`. -/
theorem Pset_card_le {n : ℕ} (hn : 1 ≤ n) (W : Walk n) (hW : W.Covering) :
    (W.Pset.ncard : ℤ) ≤ W.eStat :=
  W.pset_ncard_le_eStat hn

/-- **Display (5)** (§4): choosing one positive-defect edge in each nonempty interval
injects `A_meet` into `P`, so `|A| ≤ |A₀| + |P|`. -/
theorem break_card_le {n : ℕ} (W : Walk n) (hW : W.Covering) :
    W.breakSet.ncard ≤ W.A0Set.ncard + W.Pset.ncard := by
  classical
  have hPfin : W.Pset.Finite :=
    (Set.finite_Iio W.numVerts).subset (fun i hi => by
      have h1 := hi.1
      simp only [Set.mem_Iio]
      omega)
  have hsub : W.AmeetSet ⊆ W.breakSet := fun j hj => hj.1
  have hunion : W.breakSet = W.A0Set ∪ W.AmeetSet := by
    show W.breakSet = (W.breakSet \ W.AmeetSet) ∪ W.AmeetSet
    rw [Set.diff_union_self, Set.union_eq_self_of_subset_right hsub]
  have hAm : W.AmeetSet.ncard ≤ W.Pset.ncard := by
    have hmaps : ∀ j ∈ W.AmeetSet,
        (sInf {i | i ∈ W.Pset ∧ W.tauIdx j ≤ i ∧ i < W.tauIdx (j + 1)}) ∈ W.Pset := by
      rintro j ⟨hjA, ij, hijP, hij1, hij2⟩
      exact (Nat.sInf_mem (⟨ij, hijP, hij1, hij2⟩ :
        {i | i ∈ W.Pset ∧ W.tauIdx j ≤ i ∧ i < W.tauIdx (j + 1)}.Nonempty)).1
    have hinj : Set.InjOn
        (fun j => sInf {i | i ∈ W.Pset ∧ W.tauIdx j ≤ i ∧ i < W.tauIdx (j + 1)})
        W.AmeetSet := by
      rintro j hj j' hj' hff
      obtain ⟨hjA, ij, hijP, hij1, hij2⟩ := hj
      obtain ⟨hj'A, ij', hij'P, hij'1, hij'2⟩ := hj'
      have hff' : sInf {i | i ∈ W.Pset ∧ W.tauIdx j ≤ i ∧ i < W.tauIdx (j + 1)}
          = sInf {i | i ∈ W.Pset ∧ W.tauIdx j' ≤ i ∧ i < W.tauIdx (j' + 1)} := hff
      obtain ⟨_, hja, hjb⟩ := Nat.sInf_mem (⟨ij, hijP, hij1, hij2⟩ :
        {i | i ∈ W.Pset ∧ W.tauIdx j ≤ i ∧ i < W.tauIdx (j + 1)}.Nonempty)
      obtain ⟨_, hj'a, hj'b⟩ := Nat.sInf_mem (⟨ij', hij'P, hij'1, hij'2⟩ :
        {i | i ∈ W.Pset ∧ W.tauIdx j' ≤ i ∧ i < W.tauIdx (j' + 1)}.Nonempty)
      by_contra hne
      rcases Nat.lt_or_ge j j' with h | h
      · have hmono : W.tauIdx (j + 1) ≤ W.tauIdx j' :=
          W.tauIdx_le_tauIdx (by omega) (by have := hj'A.1; omega)
        omega
      · have hmono : W.tauIdx (j' + 1) ≤ W.tauIdx j :=
          W.tauIdx_le_tauIdx (by omega : j' + 1 ≤ j) (by have := hjA.1; omega)
        omega
    exact Set.ncard_le_ncard_of_injOn _ hmaps hinj hPfin
  calc W.breakSet.ncard = (W.A0Set ∪ W.AmeetSet).ncard := by rw [← hunion]
    _ ≤ W.A0Set.ncard + W.AmeetSet.ncard := Set.ncard_union_le _ _
    _ ≤ W.A0Set.ncard + W.Pset.ncard := by omega

/-! ## §5 Shared orbits and the charge map -/

/-- Prose fact (§5): incidence of `O` with `L` (`O ⊆ V(L)`) is equivalent to one vertex
of `O` lying in `V(L)`, because `V(L)` is closed under cyclic rotation. -/
theorem incident_iff_exists_mem (n : ℕ) (O : RotClass) (L : MarkedLoop) :
    Incident n O L ↔ ∃ w, rotClass w = O ∧ w ∈ V n L := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Quotient.exists_rep O
    exact ⟨w, hw, h w hw⟩
  · rintro ⟨w, rfl, hw⟩ w' hw'
    have hr : w ~r w' := (rotClass_eq_iff.mp hw').symm
    obtain ⟨k, rfl⟩ := hr
    exact V_closed_rotate L hw k

/-- Prose fact (§5): the first-visit owner `F(O)` lies in `Ω(O)`. -/
theorem fowner_mem_Omega {n : ℕ} (W : Walk n) (hW : W.Covering) (O : RotClass)
    (hO : ∃ w, IsPermWord n w ∧ rotClass w = O) :
    W.Fowner O ∈ W.OmegaSet O := by
  obtain ⟨w, hwperm, hwO⟩ := hO
  obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem (hW w hwperm)
  have hne : {t | t < W.numVerts ∧ rotClass (W.vert t) = O}.Nonempty :=
    ⟨i, hi, by rw [W.vert_eq_getElem hi, hiw]; exact hwO⟩
  obtain ⟨hs1, hs2⟩ := W.sVisit_spec hne
  constructor
  · exact ⟨W.sVisit O, hs1, W.activeLoop_sVisit hne⟩
  · exact (incident_iff_exists_mem n O (W.Fowner O)).mpr
      ⟨W.vert (W.sVisit O), hs2, mem_V_genLoop n _ (W.vert_isPerm hs1)⟩

/-- **Lemma [lem:ownerbook] (Owner bookkeeping)**: if `L` is a pre-entry owner of `O`,
then `O ∈ D`, `L ∈ Ω(O)`, and `L ≠ F(O)`. -/
theorem owner_bookkeeping {n : ℕ} (W : Walk n) (hW : W.Covering) (O : RotClass)
    (L : MarkedLoop) (h : W.PreEntryOwner O L) :
    O ∈ W.Dset ∧ L ∈ W.OmegaSet O ∧ L ≠ W.Fowner O := by
  obtain ⟨hΩ, t, htτ, htO⟩ := h
  have hL : W.Entered L := hΩ.1
  obtain ⟨hτ1, hτ2⟩ := W.tauLoop_spec hL
  have ht : t < W.numVerts := by omega
  have hne : {s | s < W.numVerts ∧ rotClass (W.vert s) = O}.Nonempty := ⟨t, ht, htO⟩
  obtain ⟨hs1, hs2⟩ := W.sVisit_spec hne
  have hsle : W.sVisit O ≤ t := W.sVisit_le ht htO
  have hFent : W.Entered (W.Fowner O) :=
    ⟨W.sVisit O, hs1, W.activeLoop_sVisit hne⟩
  have hFinc : Incident n O (W.Fowner O) :=
    (incident_iff_exists_mem n O (W.Fowner O)).mpr
      ⟨W.vert (W.sVisit O), hs2, mem_V_genLoop n _ (W.vert_isPerm hs1)⟩
  have hFne : L ≠ W.Fowner O := by
    intro heq
    have hτle : W.tauLoop L ≤ W.sVisit O :=
      W.tauLoop_le hs1 (by rw [W.activeLoop_sVisit hne]; exact heq.symm)
    omega
  refine ⟨?_, hΩ, hFne⟩
  show 2 ≤ W.mu O
  exact (Set.one_lt_ncard (W.omega_finite O)).mpr
    ⟨L, hΩ, W.Fowner O, ⟨hFent, hFinc⟩, hFne⟩

/-- **Lemma [lem:incidence] (Incidence count), display (6a)**: if
`v(W) = (n−2)! + ℓ`, then `q = ℓ(n−1)`.  (Stated with `n ≥ 1`, needed to divide the
incidence count by `n`; the paper has no explicit bound.) -/
theorem incidence_count_6a {n : ℕ} (W : Walk n) (hW : W.Covering) (hn : 1 ≤ n)
    (ℓ : ℕ) (hv : W.vStat = (n - 2).factorial + ℓ) :
    W.qStat = ℓ * (n - 1) := by
  classical
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `n = 1`: only one loop can ever be active, so no orbit is shared and `q = 0`
    have hone : n = 1 := by omega
    subst hone
    have hvert : ∀ t, t < W.numVerts → W.vert t = [1] := by
      intro t ht
      have hperm := W.vert_isPerm ht
      have hlen := hperm.length
      obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (hperm.ne_nil (le_refl 1))
      have hl : l = [] := by
        rw [hal] at hlen
        simp at hlen
        exact hlen
      subst hl
      have ha : a = 1 := by
        have := hperm.toFinset_eq
        rw [hal] at this
        simp at this
        exact this
      rw [hal, ha]
    have hDempty : W.Dset = ∅ := by
      ext O
      simp only [Walk.Dset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_le]
      have hsub : W.OmegaSet O ⊆ {genLoop [1]} := by
        rintro L ⟨⟨t, ht, rfl⟩, -⟩
        obtain ⟨s, -, hs2, hs3⟩ := W.activeLoop_eq_genLoop t ht
        rw [Set.mem_singleton_iff, hs3, hvert s hs2]
      calc W.mu O ≤ ({genLoop [1]} : Set MarkedLoop).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
        _ < 2 := by omega
    rw [Walk.qStat, hDempty]
    simp
  · -- `n ≥ 2`: double-count vertex–loop incidences
    set EF := W.entered_finite.toFinset with hEF
    set ΘF := classesOf (Finset.Icc 1 n) with hΘF
    set P : Finset (RotClass × MarkedLoop) :=
      (ΘF ×ˢ EF).filter (fun p => Incident n p.1 p.2) with hP
    have hEFmem : ∀ {L}, L ∈ EF ↔ W.Entered L := fun {L} => W.entered_finite.mem_toFinset
    have hΘFmem : ∀ {O}, O ∈ ΘF ↔ ∃ w, IsPermWord n w ∧ rotClass w = O := by
      intro O
      have := Set.ext_iff.mp (permClasses_eq_coe n) O
      simpa using this.symm
    have hincΘ : ∀ {O L}, Incident n O L → O ∈ ΘF := by
      intro O L h
      obtain ⟨w₀, hw₀⟩ := Quotient.exists_rep O
      have hw₀' : rotClass w₀ = O := hw₀
      exact hΘFmem.mpr ⟨w₀, (h w₀ hw₀').1, hw₀'⟩
    -- count `P` by loops: each entered loop owns `n − 1` orbits
    have hcount1 : P.card = W.vStat * (n - 1) := by
      have hmaps : ∀ p ∈ P, Prod.snd p ∈ EF := by
        intro p hp
        rw [hP, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.1.2
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      have hfib : ∀ L ∈ EF, (P.filter (fun p => p.2 = L)).card = n - 1 := by
        intro L hL
        have hLval : IsMarkedLoop n L :=
          W.isMarkedLoop_of_entered (by omega) (hEFmem.mp hL)
        have himg : P.filter (fun p => p.2 = L) =
            (ΘF.filter (fun O => Incident n O L)).image (fun O => (O, L)) := by
          ext q
          simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨⟨hO', -⟩, hinc⟩, hsnd⟩
            exact ⟨q.1, ⟨hO', by rw [← hsnd]; exact hinc⟩, by
              rw [← hsnd]⟩
          · rintro ⟨O, ⟨hO, hinc⟩, heq⟩
            rw [← heq]
            exact ⟨⟨⟨hO, hL⟩, hinc⟩, rfl⟩
        have hinj : Set.InjOn (fun O => ((O, L) : RotClass × MarkedLoop))
            ↑(ΘF.filter (fun O => Incident n O L)) := by
          intro O _ O' _ h
          exact congrArg Prod.fst h
        have hseteq : (↑(ΘF.filter (fun O => Incident n O L)) : Set RotClass) =
            {O | Incident n O L} := by
          ext O
          simp only [Finset.coe_filter, Set.mem_setOf_eq]
          exact ⟨fun h => h.2, fun h => ⟨hincΘ h, h⟩⟩
        rw [himg, Finset.card_image_of_injOn hinj]
        have hcio := card_incident_orbits hn2 hLval
        rw [← hseteq, Set.ncard_coe_finset] at hcio
        exact hcio
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
      congr 1
      rw [Walk.vStat, Set.ncard_eq_toFinset_card _ W.entered_finite]
    -- count `P` by orbits: `Σ_{O ∈ Θ} μ(O)`
    have hcount2 : P.card = ∑ O ∈ ΘF, W.mu O := by
      have hmaps : ∀ p ∈ P, Prod.fst p ∈ ΘF := by
        intro p hp
        rw [hP, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.1.1
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      refine Finset.sum_congr rfl (fun O hO => ?_)
      have himg : P.filter (fun p => p.1 = O) =
          (EF.filter (fun L => Incident n O L)).image (fun L => (O, L)) := by
        ext q
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨⟨-, hL'⟩, hinc⟩, hfst⟩
          exact ⟨q.2, ⟨hL', by rw [← hfst]; exact hinc⟩, by rw [← hfst]⟩
        · rintro ⟨L, ⟨hL, hinc⟩, heq⟩
          rw [← heq]
          exact ⟨⟨⟨hO, hL⟩, hinc⟩, rfl⟩
      have hinj : Set.InjOn (fun L => ((O, L) : RotClass × MarkedLoop))
          ↑(EF.filter (fun L => Incident n O L)) := by
        intro L _ L' _ h
        exact congrArg Prod.snd h
      have hseteq : (↑(EF.filter (fun L => Incident n O L)) : Set MarkedLoop) =
          W.OmegaSet O := by
        ext L
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Walk.OmegaSet]
        constructor
        · rintro ⟨hL, hinc⟩
          exact ⟨hEFmem.mp hL, hinc⟩
        · rintro ⟨hL, hinc⟩
          exact ⟨hEFmem.mpr hL, hinc⟩
      rw [himg, Finset.card_image_of_injOn hinj, Walk.mu, ← hseteq,
        Set.ncard_coe_finset]
    -- every permutation orbit has an owner
    have hmu1 : ∀ O ∈ ΘF, 1 ≤ W.mu O := by
      intro O hO
      obtain ⟨w, hwperm, hwO⟩ := hΘFmem.mp hO
      obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem (hW w hwperm)
      have hvert : W.vert i = w := by rw [W.vert_eq_getElem hi, hiw]
      exact W.one_le_mu_of_mem (L := W.activeLoop i)
        ⟨⟨i, hi, rfl⟩, incident_of_mem w hwO
          (by rw [← hvert]; exact vert_mem_activeLoop W i hi)⟩
    -- assemble: `q = Σ_Θ μ − (n−1)!`
    have hDsub : W.dset_finite.toFinset ⊆ ΘF := by
      intro O hO
      have := W.dset_subset_permClasses (W.dset_finite.mem_toFinset.mp hO)
      exact hΘFmem.mpr this
    have hqsum : W.qStat = ∑ O ∈ ΘF, (W.mu O - 1) := by
      rw [W.qStat_eq_sum]
      refine Finset.sum_subset hDsub (fun O hO hOD => ?_)
      have : ¬ 2 ≤ W.mu O := by
        intro h2
        exact hOD (W.dset_finite.mem_toFinset.mpr h2)
      omega
    have hsub : ∑ O ∈ ΘF, (W.mu O - 1) = ∑ O ∈ ΘF, W.mu O - ΘF.card := by
      rw [Finset.sum_tsub_distrib ΘF (fun O hO => hmu1 O hO)]
      congr 1
      rw [Finset.card_eq_sum_ones]
    have hΘcard : ΘF.card = (n - 1).factorial := by
      have h1 : n + 1 - 1 - 1 = n - 1 := by omega
      rw [hΘF, card_classesOf, Nat.card_Icc, h1]
    have hfe : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have e1 : m + 2 - 1 = m + 1 := by omega
      have e2 : m + 2 - 2 = m := by omega
      rw [e1, e2, Nat.factorial_succ]
    have hkey : ((n - 2).factorial + ℓ) * (n - 1) =
        ℓ * (n - 1) + (n - 1) * (n - 2).factorial := by ring
    rw [hqsum, hsub, ← hcount2, hcount1, hΘcard, hv, hfe, hkey]
    omega

/-- **Lemma [lem:incidence] (Incidence count), display (6b)**: if
`v(W) = (n−2)! + ℓ`, then `|D| ≤ ℓ(n−1)`. -/
theorem incidence_count_6b {n : ℕ} (W : Walk n) (hW : W.Covering) (hn : 1 ≤ n)
    (ℓ : ℕ) (hv : W.vStat = (n - 2).factorial + ℓ) :
    W.Dset.ncard ≤ ℓ * (n - 1) := by
  rw [← incidence_count_6a W hW hn ℓ hv, W.qStat_eq_sum,
    Set.ncard_eq_toFinset_card _ W.dset_finite]
  calc W.dset_finite.toFinset.card
      = ∑ _O ∈ W.dset_finite.toFinset, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ O ∈ W.dset_finite.toFinset, (W.mu O - 1) := by
        refine Finset.sum_le_sum (fun O hO => ?_)
        have h2 : 2 ≤ W.mu O := W.dset_finite.mem_toFinset.mp hO
        omega

/-- **Display (7)** (§5): the defining property of the charge set `𝒞(j)`. -/
theorem chargeSet_spec {n : ℕ} (W : Walk n) (j : ℕ) (s : RotClass × MarkedLoop) :
    s ∈ W.chargeSet j ↔
      s.1 ∈ W.Dset ∧ Incident n s.1 s.2 ∧
        (s.2 = W.Efe j ∨ s.2 = W.Efe (j + 1)) ∧
        (s.2 = W.Efe (j + 1) → s.2 ≠ W.Fowner s.1) := Iff.rfl

/-- **Lemma [lem:localtight] (Local tight-edge classification)**, headline: if the
local defect vanishes, the edge weight is at most 3. -/
theorem localtight_wt_le_three {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0) :
    wt n (W.vert i) (W.vert (i + 1)) ≤ 3 := by
  have hdp := W.dp_le_one hi
  have hdc := W.dc_le_one hi
  have hdv := W.dv_le_one hi
  unfold Walk.defect at hd
  have : (wt n (W.vert i) (W.vert (i + 1)) : ℤ) ≤ 3 := by omega
  exact_mod_cast this

/-- **Lemma [lem:localtight]**, item 1: a weight-1 edge is the rotation `ρ`; it stays
in the same rotation orbit and does not enter a new marked 2-loop. -/
theorem localtight_w1 {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 1) :
    W.vert (i + 1) = rho (W.vert i) ∧
      rotClass (W.vert (i + 1)) = rotClass (W.vert i) ∧ W.dv i = 0 := by
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm (by omega)
  have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi
  have hn : 1 ≤ n := le_n_of_wt_eq hu hw (le_refl 1)
  have hrho := eq_rho_of_wt_one hn hu hv hw
  refine ⟨hrho, ?_, W.dv_eq_zero_of_wt_one hi (by omega)⟩
  rw [hrho]
  exact (rotClass_eq_iff.mpr ⟨1, rfl⟩).symm

/-- **Lemma [lem:localtight]**, item 2 (word form): a weight-2 edge lands at
`σ₃σ₄⋯σ_nσ₂σ₁`, and the rotation orbit of the source is incident with the landing
loop `L(z)`. -/
theorem localtight_w2 {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 2) :
    W.vert (i + 1) = door (W.vert i) ∧
      Incident n (rotClass (W.vert i)) (genLoop (W.vert (i + 1))) := by
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm (by omega)
  have hn2 : 2 ≤ n := le_n_of_wt_eq hu hw (by omega)
  have hdoor := W.door_of_wt_two hi hw
  refine ⟨hdoor, ?_⟩
  rw [hdoor, genLoop_door_eq_genLoop_rho hn2 hu]
  exact (incident_iff_exists_mem n _ _).mpr ⟨W.vert i, rfl, mem_V_genLoop_rho hn2 hu⟩

/-- **Lemma [lem:localtight]**, item 2 (same-loop door): if `σ ∈ V(L)` and
`L(z) = L`, the edge is the standard HPV door of `L`, leading from the rotation orbit
of `σ` to a different rotation orbit of `L`. -/
theorem localtight_w2_same_loop {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 2) (L : MarkedLoop)
    (hσ : W.vert i ∈ V n L) (hL : genLoop (W.vert (i + 1)) = L) :
    rotClass (W.vert (i + 1)) ≠ rotClass (W.vert i) ∧
      Incident n (rotClass (W.vert (i + 1))) L := by
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm (by omega)
  have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi
  have hn2 : 2 ≤ n := le_n_of_wt_eq hu hw (by omega)
  have hdoor := W.door_of_wt_two hi hw
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · -- `n = 2` is impossible: there the door is the rotation, of weight 1
      exfalso
      have hn2' : n = 2 := by omega
      subst hn2'
      rw [hdoor, door_eq_rho_of_two hu, wt_rho (by omega) hu] at hw
      omega
    · exact h3
  constructor
  · rw [hdoor]
    exact door_leaves_class n hn3 _ hu
  · rw [← hL]
    exact (incident_iff_exists_mem n _ _).mpr
      ⟨W.vert (i + 1), rfl, mem_V_genLoop n _ hv⟩

/-- **Lemma [lem:localtight]**, item 2 (tightness): if in addition the target is not a
first entry of a marked 2-loop, tightness forces `Δp = Δc = 1`, `Δv = 0`. -/
theorem localtight_w2_tight {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 2)
    (hnf : ¬ W.IsFirstEntryTime (i + 1)) :
    W.dp i = 1 ∧ W.dc i = 1 ∧ W.dv i = 0 := by
  have hdv : W.dv i = 0 := by
    rcases W.dv_cases hi with ⟨h, -⟩ | ⟨-, hnone⟩
    · exact h
    · exfalso
      apply hnf
      refine ⟨hi, fun s hs => ?_⟩
      exact hnone s (by omega)
  have hdp := W.dp_le_one hi
  have hdc := W.dc_le_one hi
  have hdp0 := W.dp_nonneg hi
  have hdc0 := W.dc_nonneg hi
  unfold Walk.defect at hd
  rw [hw] at hd
  refine ⟨by omega, by omega, hdv⟩

/-- **Lemma [lem:localtight]**, item 3: if `w = 2`, `σ ∈ V(L)` and `L(z) ≠ L`, the
rotation orbit of `σ` is incident with both `L` and `L(z)`. -/
theorem localtight_w2_cross {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 2) (L : MarkedLoop)
    (hσ : W.vert i ∈ V n L) (hL : genLoop (W.vert (i + 1)) ≠ L) :
    Incident n (rotClass (W.vert i)) L ∧
      Incident n (rotClass (W.vert i)) (genLoop (W.vert (i + 1))) := by
  refine ⟨(incident_iff_exists_mem n _ _).mpr ⟨W.vert i, rfl, hσ⟩, ?_⟩
  exact (localtight_w2 W hW i hi hd hw).2

/-- **Lemma [lem:localtight]**, item 4: a tight weight-3 edge forces
`Δp = Δc = Δv = 1`. -/
theorem localtight_w3 {n : ℕ} (W : Walk n) (hW : W.Covering) (i : ℕ)
    (hi : i + 1 < W.numVerts) (hd : W.defect i = 0)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 3) :
    W.dp i = 1 ∧ W.dc i = 1 ∧ W.dv i = 1 := by
  have hdp := W.dp_le_one hi
  have hdc := W.dc_le_one hi
  have hdv := W.dv_le_one hi
  have hdp0 := W.dp_nonneg hi
  have hdc0 := W.dc_nonneg hi
  have hdv0 := W.dv_nonneg hi
  unfold Walk.defect at hd
  rw [hw] at hd
  refine ⟨by omega, by omega, by omega⟩

/-- **Lemma [lem:immediate] (Immediate charge cases)**: for `j ∈ A₀`, if the terminal
edge has weight 2, or the window is not fresh, or the window contains a switch, then
`𝒞(j) ≠ ∅`. -/
theorem immediate_charge {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set)
    (h : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) = 2 ∨
      ¬ W.FreshWindow j ∨ ∃ i, W.IsSwitchAt j i) :
    (W.chargeSet j).Nonempty := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hj0 : j < W.numFE := by omega
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) := W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hEfeNe : W.Efe j ≠ W.Efe (j + 1) :=
    Efe_injective W j (j + 1) hj0 hj1 (by omega)
  rcases h with hw | hnf | ⟨i, hsw⟩
  · -- (i) terminal weight-2 edge: right charge to `E_{j+1}`
    have hb1 : W.tauIdx (j + 1) - 1 + 1 = W.tauIdx (j + 1) := by omega
    have hd : W.defect (W.tauIdx (j + 1) - 1) = 0 :=
      W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
    obtain ⟨hdoor, hinc⟩ := localtight_w2 W hW (W.tauIdx (j + 1) - 1)
      (by omega) hd (by rwa [hb1])
    rw [hb1] at hdoor hinc
    have hloop : genLoop (W.vert (W.tauIdx (j + 1))) = W.Efe (j + 1) :=
      (Efe_eq_genLoop_xEntry W (j + 1) hj1).symm
    rw [hloop] at hinc
    set O := rotClass (W.vert (W.tauIdx (j + 1) - 1)) with hO
    have hpre : W.PreEntryOwner O (W.Efe (j + 1)) := by
      refine ⟨⟨Efe_entered W (j + 1) hj1, hinc⟩, W.tauIdx (j + 1) - 1, ?_, rfl⟩
      rw [W.tauLoop_Efe hj1]
      omega
    obtain ⟨hD, hΩ, hFne⟩ := owner_bookkeeping W hW _ _ hpre
    exact ⟨(O, W.Efe (j + 1)), hD, hΩ.2, Or.inr rfl, fun _ => hFne⟩
  · -- (ii) non-fresh window: left charge to `E_j`
    unfold Walk.FreshWindow at hnf
    push_neg at hnf
    obtain ⟨t, ht, htV⟩ := hnf
    set O := rotClass (W.vert t) with hO
    have hpre : W.PreEntryOwner O (W.Efe j) := by
      refine ⟨⟨Efe_entered W j hj0, incident_of_mem _ rfl htV⟩, t, ?_, rfl⟩
      rw [W.tauLoop_Efe hj0]
      exact ht
    obtain ⟨hD, hΩ, hFne⟩ := owner_bookkeeping W hW _ _ hpre
    exact ⟨(O, W.Efe j), hD, hΩ.2, Or.inl rfl, fun hcon => absurd hcon hEfeNe⟩
  · -- (iii) a switch: left charge to `E_j`
    obtain ⟨hia, hib, hiV, hiw, -, hlast⟩ := hsw
    have hi1 : i + 1 < W.numVerts := by omega
    set O := rotClass (W.vert i) with hO
    have hd : W.defect i = 0 :=
      W.defect_eq_zero_of_A0 (by omega) hj hia (by omega) hi1
    obtain ⟨-, hinc⟩ := localtight_w2 W hW i hi1 hd hiw
    -- the landing loop is a second entered owner, distinct from `E_j`
    have hentered : W.Entered (genLoop (W.vert (i + 1))) :=
      ⟨i + 1, hi1, W.activeLoop_of_two_le_wt (by omega)⟩
    have hne : genLoop (W.vert (i + 1)) ≠ W.Efe j := fun hcon =>
      hlast (by rw [← hcon]; rfl)
    have hD : O ∈ W.Dset := by
      show 2 ≤ W.mu O
      exact (Set.one_lt_ncard (W.omega_finite O)).mpr
        ⟨W.Efe j, ⟨Efe_entered W j hj0, incident_of_mem _ rfl hiV⟩,
          genLoop (W.vert (i + 1)), ⟨hentered, hinc⟩, fun hcon => hne hcon.symm⟩
    exact ⟨(O, W.Efe j), hD, incident_of_mem _ rfl hiV, Or.inl rfl,
      fun hcon => absurd hcon hEfeNe⟩

/-- **Lemma [lem:orbitendclass] (Internal orbit-end alternatives)**: in a fresh
switch-free window, an internal zero-defect edge from a vertex of `V(L)` whose whole
rotation orbit has appeared is either the closing rotation of that orbit or the
standard same-loop door with a new target; moreover the orbit is not already counted
by `c` before the edge. -/
theorem orbitend_alternatives {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j) (i : ℕ)
    (hia : W.tauIdx j ≤ i) (hib : i + 1 < W.tauIdx (j + 1))
    (hσ : W.vert i ∈ V n (W.Efe j))
    (horb : ∀ w, rotClass w = rotClass (W.vert i) → ∃ s ≤ i, W.vert s = w)
    (hd : W.defect i = 0) :
    ¬ (W.pre i).Completed (rotClass (W.vert i)) ∧
      (W.vert (i + 1) = rho (W.vert i) ∨
        (wt n (W.vert i) (W.vert (i + 1)) = 2 ∧
          W.vert (i + 1) = door (W.vert i) ∧
          genLoop (W.vert (i + 1)) = W.Efe j ∧
          ∀ s ≤ i, W.vert s ≠ W.vert (i + 1))) := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hi1 : i + 1 < W.numVerts := by omega
  have hi0 : i < W.numVerts := by omega
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm hi0
  have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi1
  -- the source class is not yet counted (else the edge could not be tight)
  have hncomp : ¬ (W.pre i).Completed (rotClass (W.vert i)) := fun hcomp =>
    W.defect_ne_zero_of_internal_completed (by omega) hia hib hi1 hcomp hd
  refine ⟨hncomp, ?_⟩
  have hdv : W.dv i = 0 := W.dv_zero_of_internal hia hib hi1
  have hw1 : 1 ≤ wt n (W.vert i) (W.vert (i + 1)) :=
    (wt_spec (u := W.vert i) (v := W.vert (i + 1)) (by omega)
      (le_of_eq hu.length)).1
  have hw3 : wt n (W.vert i) (W.vert (i + 1)) ≤ 3 :=
    localtight_wt_le_three W hW i hi1 hd
  rcases (by omega : wt n (W.vert i) (W.vert (i + 1)) = 1 ∨
      wt n (W.vert i) (W.vert (i + 1)) = 2 ∨
      wt n (W.vert i) (W.vert (i + 1)) = 3) with hw | hw | hw
  · -- weight 1: the closing rotation
    exact Or.inl (eq_rho_of_wt_one (by omega) hu hv hw)
  · -- weight 2: the same-loop door with a new target
    right
    obtain ⟨hp2, hc2, hv2⟩ := localtight_w2_tight W hW i hi1 hd hw
      (W.no_firstEntry_between (j := j) (by omega) hib)
    have hdoor := W.door_of_wt_two hi1 hw
    -- switch-freeness forces the landing marker to be the marker of `L`
    have hlast : (W.vert (i + 1)).getLastD 0 = (W.Efe j).1 := by
      by_contra hne
      refine hsf i ⟨hia, hib, hσ, hw, ?_, hne⟩
      intro hcon
      rw [hcon, wt_rho (by omega) hu] at hw
      omega
    have hloop : genLoop (W.vert (i + 1)) = W.Efe j := by
      rw [hdoor] at hlast ⊢
      exact genLoop_door_of_getLastD hn2 hu hσ hlast
    have hnew : ∀ s ≤ i, W.vert s ≠ W.vert (i + 1) := by
      rcases W.dp_cases hi1 with ⟨hdp, -⟩ | ⟨-, hnone⟩
      · exfalso
        omega
      · exact hnone
    exact ⟨hw, hdoor, hloop, hnew⟩
  · -- weight 3 is impossible on an internal edge
    exfalso
    obtain ⟨-, -, hv3⟩ := localtight_w3 W hW i hi1 hd hw
    omega

/-- **Lemma [lem:orbitendclass]**, final sentence: after the closing rotation, no
further internal zero-defect edge can start from a vertex of that orbit. -/
theorem orbitend_after_close {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j) (i : ℕ)
    (hia : W.tauIdx j ≤ i) (hib : i + 1 < W.tauIdx (j + 1))
    (hσ : W.vert i ∈ V n (W.Efe j))
    (horb : ∀ w, rotClass w = rotClass (W.vert i) → ∃ s ≤ i, W.vert s = w)
    (hd : W.defect i = 0) (hclose : W.vert (i + 1) = rho (W.vert i))
    (i' : ℕ) (hi'a : W.tauIdx j ≤ i') (hi'b : i' + 1 < W.tauIdx (j + 1))
    (hii' : i < i') (hsrc : rotClass (W.vert i') = rotClass (W.vert i)) :
    W.defect i' ≠ 0 := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hi'1 : i' + 1 < W.numVerts := by omega
  have hi'0 : i' < W.numVerts := by omega
  -- by `horb`, the whole orbit has appeared by time `i < i'`, so it is completed
  have hcomp : (W.pre i').Completed (rotClass (W.vert i')) := by
    rw [W.completed_pre_iff hi'0]
    intro w hw
    obtain ⟨s, hs1, hs3⟩ := horb w (by rw [hw, hsrc])
    exact W.mem_take_vert.mpr ⟨s, by omega, by omega, hs3⟩
  exact W.defect_ne_zero_of_internal_completed
    (by have := W.two_le_n_of_lt_numFE hj1; omega) hi'a hi'b hi'1 hcomp

/-- **Lemma [lem:boundary] (Anchored boundary edge)**: a zero-defect edge into `V(L)`
whose active loop before the edge is not `L`, taken after `L` was already entered,
produces a shared rotation orbit owned by `L`. -/
theorem anchored_boundary {n : ℕ} (W : Walk n) (hW : W.Covering) (L : MarkedLoop)
    (i : ℕ) (hi : i + 1 < W.numVerts) (hL : W.EnteredBefore i L)
    (hz : W.vert (i + 1) ∈ V n L) (hd : W.defect i = 0)
    (hH : W.activeLoop i ≠ L) :
    ∃ O', O' ∈ W.Dset ∧ L ∈ W.OmegaSet O' := by
  have hi0 : i < W.numVerts := by omega
  have hσH : W.vert i ∈ V n (W.activeLoop i) := vert_mem_activeLoop W i hi0
  have hLent : W.Entered L := by
    obtain ⟨s, hs, hact⟩ := hL
    exact ⟨s, by omega, hact⟩
  by_cases hσL : W.vert i ∈ V n L
  · -- σ ∈ V(L): the source's own orbit is shared between `L` and `H`
    refine ⟨rotClass (W.vert i), ?_, hLent, incident_of_mem _ rfl hσL⟩
    show 2 ≤ W.mu _
    exact (Set.one_lt_ncard (W.omega_finite _)).mpr
      ⟨L, ⟨hLent, incident_of_mem _ rfl hσL⟩,
        W.activeLoop i, ⟨⟨i, hi0, rfl⟩, incident_of_mem _ rfl hσH⟩,
        fun hcon => hH hcon.symm⟩
  · -- σ ∉ V(L): the edge is a nonrotation activation of `L(z) ≠ L`
    have hn1 : 1 ≤ n := by
      by_contra h0
      push_neg at h0
      have heq : W.vert i = W.vert (i + 1) :=
        eq_of_isPermWord_le_one (by omega) (W.vert_isPerm hi0) (W.vert_isPerm hi)
      rw [heq] at hσL
      exact hσL hz
    have hu : IsPermWord n (W.vert i) := W.vert_isPerm hi0
    have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi
    have hw1 : 1 ≤ wt n (W.vert i) (W.vert (i + 1)) :=
      (wt_spec (u := W.vert i) (v := W.vert (i + 1)) hn1 (le_of_eq hu.length)).1
    have hw3 : wt n (W.vert i) (W.vert (i + 1)) ≤ 3 :=
      localtight_wt_le_three W hW i hi hd
    -- weight 1 is impossible: rotation-closure of `V(L)` would put `σ` in `V(L)`
    have hwne1 : wt n (W.vert i) (W.vert (i + 1)) ≠ 1 := by
      intro hw
      apply hσL
      have hrho := eq_rho_of_wt_one hn1 hu hv hw
      have hback : W.vert i = (W.vert (i + 1)).rotate (n - 1) := by
        rw [hrho]
        show W.vert i = ((W.vert i).rotate 1).rotate (n - 1)
        rw [List.rotate_rotate]
        have h1 : 1 + (n - 1) = (W.vert i).length := by
          rw [hu.length]
          omega
        rw [h1, List.rotate_length]
      rw [hback]
      exact V_closed_rotate L hz (n - 1)
    -- the landing loop is not `L`
    have hgz : genLoop (W.vert (i + 1)) ≠ L := by
      rcases (by omega : wt n (W.vert i) (W.vert (i + 1)) = 2 ∨
          wt n (W.vert i) (W.vert (i + 1)) = 3) with hw | hw
      · intro hcon
        obtain ⟨-, hinc⟩ := localtight_w2 W hW i hi hd hw
        rw [hcon] at hinc
        exact hσL (hinc _ rfl)
      · intro hcon
        obtain ⟨-, -, hv3⟩ := localtight_w3 W hW i hi hd hw
        rcases W.dv_cases hi with ⟨h0, -⟩ | ⟨-, hnone⟩
        · omega
        · obtain ⟨s, hs, hact⟩ := hL
          apply hnone s (by omega)
          rw [W.activeLoop_of_two_le_wt (by omega), hcon]
          exact hact
    -- the orbit of `z` is shared, owned by `L` and by the activated `L(z)`
    have hzact : W.activeLoop (i + 1) = genLoop (W.vert (i + 1)) :=
      W.activeLoop_of_two_le_wt (by omega)
    refine ⟨rotClass (W.vert (i + 1)), ?_, hLent, incident_of_mem _ rfl hz⟩
    show 2 ≤ W.mu _
    exact (Set.one_lt_ncard (W.omega_finite _)).mpr
      ⟨L, ⟨hLent, incident_of_mem _ rfl hz⟩,
        genLoop (W.vert (i + 1)), ⟨⟨i + 1, hi, hzact⟩,
          incident_of_mem _ rfl (mem_V_genLoop n _ hv)⟩,
        fun hcon => hgz hcon.symm⟩

/-- **Lemma [lem:pinned] (Pinned fresh window), display (†)**: in a fresh switch-free
window at `j ∈ A₀`, the walk is pinned to the canonical ride:
`π_{a+o} = R_{⌊o/n⌋, o mod n}` whenever `o < N−1` and `o < n(n−1)`
(`N = b − a`). -/
theorem pinned_dagger {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j) (o : ℕ)
    (ho : o + 1 < W.tauIdx (j + 1) - W.tauIdx j) (ho' : o < n * (n - 1)) :
    W.vert (W.tauIdx j + o) = ride n (W.xEntry j) (o / n) (o % n) := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hEfe : W.Efe j = genLoop (W.xEntry j) :=
    W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
  revert ho ho'
  induction o using Nat.strong_induction_on with
  | _ o IH =>
    intro ho ho'
    rcases Nat.eq_zero_or_pos o with rfl | hopos
    · -- offset 0: the entry vertex itself
      simp only [Nat.zero_div, Nat.zero_mod, Nat.add_zero]
      exact (List.rotate_zero _).symm
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    -- the pinned prefix through offset `o'`
    have hpin : ∀ m ≤ o', W.vert (W.tauIdx j + m) =
        ride n (W.xEntry j) (m / n) (m % n) := by
      intro m hm
      exact IH m (by omega) (by omega) (by omega)
    obtain ⟨h, r, hor, hrn⟩ : ∃ h r, o' = h * n + r ∧ r < n :=
      ⟨o' / n, o' % n, by rw [Nat.mul_comm]; exact (Nat.div_add_mod o' n).symm,
        Nat.mod_lt _ (by omega)⟩
    have hdiv : o' / n = h := by
      rw [hor, show h * n + r = r + h * n from by omega,
        Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hrn]
      omega
    have hmod : o' % n = r := by
      rw [hor, show h * n + r = r + h * n from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrn]
    have hhlt : h < n - 1 := by
      rw [← hdiv]
      exact Nat.div_lt_of_lt_mul (by omega)
    have hσ : W.vert (W.tauIdx j + o') = ride n (W.xEntry j) h r := by
      have h2 := hpin o' (le_refl o')
      rwa [hdiv, hmod] at h2
    rcases Nat.lt_or_ge r (n - 1) with hrmid | hrtop
    · -- mid-orbit: the rotation step
      have hdiv1 : (o' + 1) / n = h := by
        rw [show o' + 1 = (r + 1) + h * n from by omega,
          Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt (by omega)]
        omega
      have hmod1 : (o' + 1) % n = r + 1 := by
        rw [show o' + 1 = (r + 1) + h * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hdiv1, hmod1]
      show W.vert (W.tauIdx j + o' + 1) = ride n (W.xEntry j) h (r + 1)
      exact W.midorbit_next hj hfresh hor hrmid hhlt (by omega) hpin
    · -- orbit end: `r = n − 1`, the internal orbit-end alternatives
      have hreq : r = n - 1 := by omega
      have hσtop : W.vert (W.tauIdx j + o') = ride n (W.xEntry j) h (n - 1) := by
        rw [hσ, hreq]
      have hbridge : (h + 1) * n = h * n + n := by ring
      have ho1 : o' + 1 = (h + 1) * n := by omega
      have hdiv1 : (o' + 1) / n = h + 1 := by
        rw [show o' + 1 = 0 + (h + 1) * n from by omega,
          Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.zero_div]
        omega
      have hmod1 : (o' + 1) % n = 0 := by
        rw [show o' + 1 = 0 + (h + 1) * n from by omega,
          Nat.add_mul_mod_self_right]
        exact Nat.zero_mod n
      -- the whole source orbit has appeared (pinned at offsets `hn + k`)
      have horb : ∀ w, rotClass w = rotClass (W.vert (W.tauIdx j + o')) →
          ∃ s ≤ W.tauIdx j + o', W.vert s = w := by
        intro w hw
        rw [hσtop, rotClass_ride] at hw
        obtain ⟨k, hk, rfl⟩ := exists_ride_of_rotClass hn2 hx hw
        have hdivk : (h * n + k) / n = h := by
          rw [show h * n + k = k + h * n from by omega,
            Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hk]
          omega
        have hmodk : (h * n + k) % n = k := by
          rw [show h * n + k = k + h * n from by omega,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
        refine ⟨W.tauIdx j + (h * n + k), by omega, ?_⟩
        have h2 := hpin (h * n + k) (by omega)
        rwa [hdivk, hmodk] at h2
      have hd : W.defect (W.tauIdx j + o') = 0 :=
        W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
      have hσV : W.vert (W.tauIdx j + o') ∈ V n (W.Efe j) := by
        rw [hσtop, hEfe]
        exact ride_mem_V hn2 hx h (n - 1)
      obtain ⟨-, halt⟩ := orbitend_alternatives W hW j hj hfresh hsf
        (W.tauIdx j + o') (by omega) (by omega) hσV horb hd
      rcases halt with hclose | ⟨-, hdoor, -, -⟩
      · -- the closing rotation is impossible: the following edge would be a
        -- zero-defect internal edge out of the just-counted orbit
        exfalso
        have hsrc : rotClass (W.vert (W.tauIdx j + o' + 1)) =
            rotClass (W.vert (W.tauIdx j + o')) := by
          rw [hclose]
          exact (rotClass_eq_iff.mpr ⟨1, rfl⟩).symm
        have hafter := orbitend_after_close W hW j hj hfresh hsf
          (W.tauIdx j + o') (by omega) (by omega) hσV horb hd hclose
          (W.tauIdx j + o' + 1) (by omega) (by omega) (by omega) hsrc
        exact hafter
          (W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega))
      · -- the same-loop door pins the next anchor
        rw [hdiv1, hmod1]
        show W.vert (W.tauIdx j + o' + 1) = ride n (W.xEntry j) (h + 1) 0
        rw [hdoor, hσtop]
        show door (ride n (W.xEntry j) h (n - 1)) =
          (rideAnchor n (W.xEntry j) (h + 1)).rotate 0
        rw [door_ride_top, List.rotate_zero]

/-- **Lemma [lem:pinned]**, the top-offset clause: if `N − 1 ≢ 0 (mod n)` and
`N ≤ n(n−1)`, then (†) also holds for `o = N − 1`. -/
theorem pinned_top {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hmod : ¬ n ∣ (W.tauIdx (j + 1) - W.tauIdx j - 1))
    (hN : W.tauIdx (j + 1) - W.tauIdx j ≤ n * (n - 1)) :
    W.vert (W.tauIdx j + (W.tauIdx (j + 1) - W.tauIdx j - 1)) =
      ride n (W.xEntry j) ((W.tauIdx (j + 1) - W.tauIdx j - 1) / n)
        ((W.tauIdx (j + 1) - W.tauIdx j - 1) % n) := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  set N := W.tauIdx (j + 1) - W.tauIdx j with hNdef
  have hr0 : (N - 1) % n ≠ 0 := fun h => hmod (Nat.dvd_of_mod_eq_zero h)
  have hrn : (N - 1) % n < n := Nat.mod_lt _ (by omega)
  have hN2 : 2 ≤ N := by
    by_contra hlt
    push_neg at hlt
    apply hr0
    rw [show N - 1 = 0 from by omega]
    exact Nat.zero_mod n
  have hdm := Nat.div_add_mod (N - 1) n
  rw [Nat.mul_comm n ((N - 1) / n)] at hdm
  have hhlt : (N - 1) / n < n - 1 := Nat.div_lt_of_lt_mul (by omega)
  have hstep := W.midorbit_next hj hfresh
    (show N - 2 = ((N - 1) / n) * n + ((N - 1) % n - 1) from by omega)
    (show (N - 1) % n - 1 < n - 1 from by omega) hhlt
    (show W.tauIdx j + (N - 2) + 1 < W.tauIdx (j + 1) from by omega)
    (fun m hm => pinned_dagger W hW j hj hfresh hsf m (by omega) (by omega))
  rw [show (N - 1) % n - 1 + 1 = (N - 1) % n from by omega] at hstep
  rw [show W.tauIdx j + (N - 1) = W.tauIdx j + (N - 2) + 1 from by omega]
  exact hstep

/-- **Lemma [lem:pinned]**, consequence 1: if `N = n(n−1)` (full window), the window
visits exactly `V(L)`, and `π_{b−1} = R_{n−2,n−1}`. -/
theorem pinned_full {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hfull : W.FullWindow j) :
    {w | ∃ t, W.tauIdx j ≤ t ∧ t < W.tauIdx (j + 1) ∧ W.vert t = w} = V n (W.Efe j) ∧
      W.vert (W.tauIdx (j + 1) - 1) = ride n (W.xEntry j) (n - 2) (n - 1) := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hEfe : W.Efe j = genLoop (W.xEntry j) :=
    W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
  have hfull' : W.tauIdx (j + 1) - W.tauIdx j = n * (n - 1) := hfull
  have hnd1 : ¬ n ∣ (W.tauIdx (j + 1) - W.tauIdx j - 1) := by
    rw [hfull']
    intro hdvd
    have h2 : n ∣ n * (n - 1) := Dvd.intro _ rfl
    have h3 := Nat.dvd_sub h2 hdvd
    rw [show n * (n - 1) - (n * (n - 1) - 1) = 1 from by omega] at h3
    have h4 := Nat.dvd_one.mp h3
    omega
  have hpinall : ∀ o, o < n * (n - 1) → W.vert (W.tauIdx j + o) =
      ride n (W.xEntry j) (o / n) (o % n) := by
    intro o hoo
    rcases Nat.lt_or_ge (o + 1) (n * (n - 1)) with hlt | hge
    · exact pinned_dagger W hW j hj hfresh hsf o (by omega) hoo
    · have hoeq : o = W.tauIdx (j + 1) - W.tauIdx j - 1 := by omega
      rw [hoeq]
      exact pinned_top W hW j hj hfresh hsf hnd1 (by omega)
  have hcorner : W.vert (W.tauIdx (j + 1) - 1) =
      ride n (W.xEntry j) (n - 2) (n - 1) := by
    have ho := hpinall (n * (n - 1) - 1) (by omega)
    have h5 : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
    have h6 : (n - 1) * n = (n - 2) * n + n := by
      rw [show n - 1 = (n - 2) + 1 from by omega]
      ring
    have he1 : n * (n - 1) - 1 = (n - 1) + (n - 2) * n := by omega
    have hdiv : (n * (n - 1) - 1) / n = n - 2 := by
      rw [he1, Nat.add_mul_div_right _ _ (by omega : 0 < n),
        Nat.div_eq_of_lt (by omega)]
      omega
    have hmodq : (n * (n - 1) - 1) % n = n - 1 := by
      rw [he1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hdiv, hmodq] at ho
    rw [show W.tauIdx (j + 1) - 1 = W.tauIdx j + (n * (n - 1) - 1) from by omega]
    exact ho
  refine ⟨?_, hcorner⟩
  have hVcard : (V n (W.Efe j)).ncard = n * (n - 1) :=
    card_V n hn2 _ (W.isMarkedLoop_of_entered (by omega) (Efe_entered W j (by omega)))
  have hsub : {w | ∃ t, W.tauIdx j ≤ t ∧ t < W.tauIdx (j + 1) ∧ W.vert t = w} ⊆
      V n (W.Efe j) := by
    rintro w ⟨t, ht1, ht2, rfl⟩
    have hpin := hpinall (t - W.tauIdx j) (by omega)
    rw [show W.tauIdx j + (t - W.tauIdx j) = t from by omega] at hpin
    rw [hpin, hEfe]
    exact ride_mem_V hn2 hx _ _
  have himg : {w | ∃ t, W.tauIdx j ≤ t ∧ t < W.tauIdx (j + 1) ∧ W.vert t = w} =
      (fun o => ride n (W.xEntry j) (o / n) (o % n)) '' Set.Iio (n * (n - 1)) := by
    ext w
    constructor
    · rintro ⟨t, ht1, ht2, rfl⟩
      refine ⟨t - W.tauIdx j, by simp only [Set.mem_Iio]; omega, ?_⟩
      have hpin := hpinall (t - W.tauIdx j) (by omega)
      rw [show W.tauIdx j + (t - W.tauIdx j) = t from by omega] at hpin
      exact hpin.symm
    · rintro ⟨o, ho, rfl⟩
      simp only [Set.mem_Iio] at ho
      exact ⟨W.tauIdx j + o, by omega, by omega, hpinall o ho⟩
  have hinj : Set.InjOn (fun o => ride n (W.xEntry j) (o / n) (o % n))
      (Set.Iio (n * (n - 1))) := by
    intro o1 h1 o2 h2 heq
    simp only [Set.mem_Iio] at h1 h2
    have hd1 : o1 / n < n - 1 := Nat.div_lt_of_lt_mul h1
    have hd2 : o2 / n < n - 1 := Nat.div_lt_of_lt_mul h2
    obtain ⟨hh, hr⟩ := ride_word_inj hn2 hx hd1 hd2
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
    have e1 := Nat.div_add_mod o1 n
    have e2 := Nat.div_add_mod o2 n
    rw [hh, hr] at e1
    omega
  have hIio : (Set.Iio (n * (n - 1))).ncard = n * (n - 1) := by
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  have hcard : {w | ∃ t, W.tauIdx j ≤ t ∧ t < W.tauIdx (j + 1) ∧
      W.vert t = w}.ncard = n * (n - 1) := by
    rw [himg, Set.ncard_image_of_injOn hinj, hIio]
  exact Set.eq_of_subset_of_ncard_le hsub (by omega)
    ((permWords_finite n).subset (fun σ hσ => hσ.1))

/-- **Lemma [lem:pinned]**, consequence 2: if `(N−1) ≡ n−1 (mod n)` and `N ≤ (n−2)n`,
then the full rotation orbit `{R_{n−2,0},…,R_{n−2,n−1}} ⊆ V(L)` is missed by
`π_a,…,π_{b−1}`. -/
theorem pinned_missed {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hmod : (W.tauIdx (j + 1) - W.tauIdx j - 1) ≡ (n - 1) [MOD n])
    (hN : W.tauIdx (j + 1) - W.tauIdx j ≤ (n - 2) * n) :
    (∀ r < n, ride n (W.xEntry j) (n - 2) r ∈ V n (W.Efe j)) ∧
      ∀ t, W.tauIdx j ≤ t → t < W.tauIdx (j + 1) →
        ∀ r < n, W.vert t ≠ ride n (W.xEntry j) (n - 2) r := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hEfe : W.Efe j = genLoop (W.xEntry j) :=
    W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
  refine ⟨fun r _ => by rw [hEfe]; exact ride_mem_V hn2 hx _ _, ?_⟩
  intro t ht1 ht2 r hr hcon
  have hmodv : (W.tauIdx (j + 1) - W.tauIdx j - 1) % n = n - 1 := by
    have h2 : (W.tauIdx (j + 1) - W.tauIdx j - 1) % n = (n - 1) % n := hmod
    rwa [Nat.mod_eq_of_lt (by omega : n - 1 < n)] at h2
  have hdm := Nat.div_add_mod (W.tauIdx (j + 1) - W.tauIdx j - 1) n
  rw [Nat.mul_comm n ((W.tauIdx (j + 1) - W.tauIdx j - 1) / n), hmodv] at hdm
  -- `h₀ + 1 ≤ n − 2`
  have hb1 : ((W.tauIdx (j + 1) - W.tauIdx j - 1) / n + 1) * n =
      ((W.tauIdx (j + 1) - W.tauIdx j - 1) / n) * n + n := by ring
  have hh0 : (W.tauIdx (j + 1) - W.tauIdx j - 1) / n + 1 ≤ n - 2 := by
    have hmul : ((W.tauIdx (j + 1) - W.tauIdx j - 1) / n + 1) * n ≤ (n - 2) * n := by
      omega
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hNle : (n - 2) * n ≤ n * (n - 1) := by
    have h4 := Nat.mul_le_mul_right n (show n - 2 ≤ n - 1 by omega)
    rwa [Nat.mul_comm (n - 1) n] at h4
  -- every window vertex is pinned
  have hpin : W.vert t = ride n (W.xEntry j)
      ((t - W.tauIdx j) / n) ((t - W.tauIdx j) % n) := by
    rcases Nat.lt_or_ge (t - W.tauIdx j + 1) (W.tauIdx (j + 1) - W.tauIdx j)
      with hlt | hge
    · have h5 := pinned_dagger W hW j hj hfresh hsf (t - W.tauIdx j) hlt (by omega)
      rwa [show W.tauIdx j + (t - W.tauIdx j) = t from by omega] at h5
    · have hoeq : t - W.tauIdx j = W.tauIdx (j + 1) - W.tauIdx j - 1 := by omega
      have hnd1 : ¬ n ∣ (W.tauIdx (j + 1) - W.tauIdx j - 1) := by
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        rw [hc, Nat.mul_mod_right] at hmodv
        omega
      have h5 := pinned_top W hW j hj hfresh hsf hnd1 (by omega)
      rw [hoeq]
      rwa [show W.tauIdx j + (W.tauIdx (j + 1) - W.tauIdx j - 1) = t from by omega]
        at h5
  have hdivle : (t - W.tauIdx j) / n ≤ (W.tauIdx (j + 1) - W.tauIdx j - 1) / n :=
    Nat.div_le_div_right (by omega)
  rw [hpin] at hcon
  obtain ⟨heqh, -⟩ := ride_word_inj hn2 hx
    (show (t - W.tauIdx j) / n < n - 1 from by omega)
    (show n - 2 < n - 1 from by omega) (Nat.mod_lt _ (by omega)) hr hcon
  omega

/-- **Lemma [lem:nolong] (No long non-door windows)**: a fresh switch-free window at
`j ∈ A₀` whose terminal edge is not a weight-2 edge is not long: `b − a ≤ n(n−1)`. -/
theorem no_long_nondoor {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hnd : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) ≠ 2) :
    W.tauIdx (j + 1) - W.tauIdx j ≤ n * (n - 1) := by
  by_contra hlong
  push_neg at hlong
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hEfe : W.Efe j = genLoop (W.xEntry j) :=
    W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
  set N := W.tauIdx (j + 1) - W.tauIdx j with hNdef
  -- arithmetic of `T = n(n−1)`
  have h5 : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
  have h6 : (n - 1) * n = (n - 2) * n + n := by
    rw [show n - 1 = (n - 2) + 1 from by omega]
    ring
  -- the first `T` offsets are pinned
  have hpin : ∀ m ≤ n * (n - 1) - 1, W.vert (W.tauIdx j + m) =
      ride n (W.xEntry j) (m / n) (m % n) := fun m hm =>
    pinned_dagger W hW j hj hfresh hsf m (by omega) (by omega)
  -- the vertex at offset `T − 1` is the corner `R(n−2,n−1)`
  have he1 : n * (n - 1) - 1 = (n - 2) * n + (n - 1) := by omega
  have hdivT : (n * (n - 1) - 1) / n = n - 2 := by
    rw [he1]
    exact mul_add_div_eq (by omega) _ (by omega)
  have hmodT : (n * (n - 1) - 1) % n = n - 1 := by
    rw [he1]
    exact mul_add_mod_eq (by omega) _ (by omega)
  have hσtop : W.vert (W.tauIdx j + (n * (n - 1) - 1)) =
      ride n (W.xEntry j) (n - 2) (n - 1) := by
    have h7 := hpin (n * (n - 1) - 1) (le_refl _)
    rwa [hdivT, hmodT] at h7
  -- the whole last orbit has appeared
  have horb : ∀ w, rotClass w = rotClass (W.vert (W.tauIdx j + (n * (n - 1) - 1))) →
      ∃ s ≤ W.tauIdx j + (n * (n - 1) - 1), W.vert s = w := by
    intro w hw
    rw [hσtop, rotClass_ride] at hw
    obtain ⟨k, hk, rfl⟩ := exists_ride_of_rotClass hn2 hx hw
    have hd1 := mul_add_div_eq (show 0 < n from by omega) (n - 2) hk
    have hm1 := mul_add_mod_eq (show 0 < n from by omega) (n - 2) hk
    refine ⟨W.tauIdx j + ((n - 2) * n + k), by omega, ?_⟩
    have h7 := hpin ((n - 2) * n + k) (by omega)
    rwa [hd1, hm1] at h7
  have hd : W.defect (W.tauIdx j + (n * (n - 1) - 1)) = 0 :=
    W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
  have hσV : W.vert (W.tauIdx j + (n * (n - 1) - 1)) ∈ V n (W.Efe j) := by
    rw [hσtop, hEfe]
    exact ride_mem_V hn2 hx _ _
  obtain ⟨-, halt⟩ := orbitend_alternatives W hW j hj hfresh hsf
    (W.tauIdx j + (n * (n - 1) - 1)) (by omega) (by omega) hσV horb hd
  rcases halt with hclose | ⟨-, hdoor, -, hnew⟩
  · -- the closing rotation: first `N = T + 1`, then the terminal edge is stuck
    have hNT1 : N = n * (n - 1) + 1 := by
      by_contra hne
      have hsrc : rotClass (W.vert (W.tauIdx j + (n * (n - 1) - 1) + 1)) =
          rotClass (W.vert (W.tauIdx j + (n * (n - 1) - 1))) := by
        rw [hclose]
        exact (rotClass_eq_iff.mpr ⟨1, rfl⟩).symm
      have hafter := orbitend_after_close W hW j hj hfresh hsf
        (W.tauIdx j + (n * (n - 1) - 1)) (by omega) (by omega) hσV horb hd hclose
        (W.tauIdx j + (n * (n - 1) - 1) + 1) (by omega) (by omega) (by omega) hsrc
      exact hafter
        (W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega))
    -- the terminal source is the revisited anchor `R(n−2,0)`
    have hvb1 : W.vert (W.tauIdx (j + 1) - 1) = rideAnchor n (W.xEntry j) (n - 2) := by
      rw [show W.tauIdx (j + 1) - 1 = W.tauIdx j + (n * (n - 1) - 1) + 1 from by omega,
        hclose, hσtop, rho_ride_top hn2 hx]
    have hb1eq : W.tauIdx (j + 1) - 1 + 1 = W.tauIdx (j + 1) := by omega
    have hd' : W.defect (W.tauIdx (j + 1) - 1) = 0 :=
      W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
    have hFEb : W.IsFirstEntryTime (W.tauIdx (j + 1) - 1 + 1) := by
      rw [hb1eq]
      exact W.isFirstEntry_tauIdx hj1
    have hwt2 := W.two_le_wt_into_firstEntry hFEb
    rw [hb1eq] at hwt2
    have hwle := localtight_wt_le_three W hW (W.tauIdx (j + 1) - 1) (by omega) hd'
    rw [hb1eq] at hwle
    have hwt3 : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) = 3 := by
      omega
    obtain ⟨-, hc3, -⟩ := localtight_w3 W hW (W.tauIdx (j + 1) - 1) (by omega) hd'
      (by rwa [hb1eq])
    obtain ⟨hfirst, -⟩ := W.dc_eq_one_data (by omega) hc3
    -- but the anchor was already visited at offset `(n−2)n`
    have hd2 := mul_add_div_eq (show 0 < n from by omega) (n - 2) (show 0 < n from by omega)
    have hm2 := mul_add_mod_eq (show 0 < n from by omega) (n - 2) (show 0 < n from by omega)
    have hearly := hpin ((n - 2) * n + 0) (by omega)
    rw [hd2, hm2] at hearly
    refine hfirst (W.tauIdx j + ((n - 2) * n + 0)) (by omega) ?_
    rw [hearly, hvb1]
    exact List.rotate_zero _
  · -- the door returns to `x_j`, contradicting the new-target clause
    refine hnew (W.tauIdx j) (by omega) ?_
    rw [hdoor, hσtop, door_ride_top, show n - 2 + 1 = n - 1 from by omega,
      rideAnchor_wrap hn2 hx]
    rfl

/-- **Lemma [lem:orbitend] (Non-door short endings)**: a fresh switch-free *short*
window at `j ∈ A₀` with non-door terminal edge has
`(N−1) ≡ n−1 (mod n)` and `N ≤ (n−2)n`. -/
theorem nondoor_short_ending {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hshort : W.ShortWindow j)
    (hnd : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) ≠ 2) :
    (W.tauIdx (j + 1) - W.tauIdx j - 1) ≡ (n - 1) [MOD n] ∧
      W.tauIdx (j + 1) - W.tauIdx j ≤ (n - 2) * n := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hEfe : W.Efe j = genLoop (W.xEntry j) :=
    W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
  set N := W.tauIdx (j + 1) - W.tauIdx j with hNdef
  have hshort' : N < n * (n - 1) := hshort
  -- the terminal edge has weight 3 and completes its source orbit
  have hb1eq : W.tauIdx (j + 1) - 1 + 1 = W.tauIdx (j + 1) := by omega
  have hd' : W.defect (W.tauIdx (j + 1) - 1) = 0 :=
    W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
  have hFEb : W.IsFirstEntryTime (W.tauIdx (j + 1) - 1 + 1) := by
    rw [hb1eq]
    exact W.isFirstEntry_tauIdx hj1
  have hwt2 := W.two_le_wt_into_firstEntry hFEb
  rw [hb1eq] at hwt2
  have hwle := localtight_wt_le_three W hW (W.tauIdx (j + 1) - 1) (by omega) hd'
  rw [hb1eq] at hwle
  obtain ⟨-, hc3, -⟩ := localtight_w3 W hW (W.tauIdx (j + 1) - 1) (by omega) hd'
    (by rw [hb1eq]; omega)
  obtain ⟨hfirst, hothers⟩ := W.dc_eq_one_data (by omega) hc3
  -- (*) the terminal source cannot sit strictly inside a ride orbit whose top
  -- offset exceeds `N − 2`
  have hkill : ∀ h₀ r', h₀ < n - 1 → r' ≠ n - 1 → r' < n →
      W.vert (W.tauIdx (j + 1) - 1) = ride n (W.xEntry j) h₀ r' →
      N - 2 < h₀ * n + (n - 1) → False := by
    intro h₀ r' hh0 hr'ne hr'lt hvb1 harith
    have hwne : ride n (W.xEntry j) h₀ (n - 1) ≠ W.vert (W.tauIdx (j + 1) - 1) := by
      rw [hvb1]
      intro hcon
      obtain ⟨-, hre⟩ := ride_word_inj hn2 hx hh0 hh0 (by omega) hr'lt hcon
      exact hr'ne hre.symm
    have hcls : rotClass (ride n (W.xEntry j) h₀ (n - 1)) =
        rotClass (W.vert (W.tauIdx (j + 1) - 1)) := by
      rw [hvb1, rotClass_ride, rotClass_ride]
    obtain ⟨s, hs, hsv⟩ := hothers _ hcls hwne
    rcases Nat.lt_or_ge s (W.tauIdx j) with hsa | hsa
    · apply hfresh s hsa
      rw [hsv, hEfe]
      exact ride_mem_V hn2 hx _ _
    · have hslt : s - W.tauIdx j + 1 < N := by omega
      have hpins := pinned_dagger W hW j hj hfresh hsf (s - W.tauIdx j) hslt (by omega)
      rw [show W.tauIdx j + (s - W.tauIdx j) = s from by omega] at hpins
      rw [hpins] at hsv
      have hdlt : (s - W.tauIdx j) / n < n - 1 := Nat.div_lt_of_lt_mul (by omega)
      obtain ⟨hdh, hdr⟩ := ride_word_inj hn2 hx hdlt hh0
        (Nat.mod_lt _ (by omega)) (by omega) hsv
      have hda := Nat.div_add_mod (s - W.tauIdx j) n
      rw [hdh, hdr, Nat.mul_comm n h₀] at hda
      omega
  -- main congruence: `(N − 1) % n = n − 1`
  have hmodv : (N - 1) % n = n - 1 := by
    by_contra hne
    have hrn : (N - 1) % n < n := Nat.mod_lt _ (by omega)
    have hdm := Nat.div_add_mod (N - 1) n
    rw [Nat.mul_comm n ((N - 1) / n)] at hdm
    have hh0lt : (N - 1) / n < n - 1 := Nat.div_lt_of_lt_mul (by omega)
    rcases Nat.eq_zero_or_pos ((N - 1) % n) with hr0 | hrpos
    · -- `r₀ = 0`
      rcases Nat.eq_zero_or_pos (N - 1) with hN1 | hNpos
      · -- `N = 1`: the source is `x_j` itself
        have hvb1 : W.vert (W.tauIdx (j + 1) - 1) = ride n (W.xEntry j) 0 0 := by
          rw [show W.tauIdx (j + 1) - 1 = W.tauIdx j from by omega]
          exact (List.rotate_zero _).symm
        exact hkill 0 0 (by omega) (by omega) (by omega) hvb1 (by omega)
      · -- `N − 1 = h₀ n` with `h₀ ≥ 1`: analyze the previous internal edge
        have hh0pos : 1 ≤ (N - 1) / n := by
          rcases Nat.eq_zero_or_pos ((N - 1) / n) with h0 | h0
          · rw [h0, Nat.zero_mul] at hdm
            omega
          · exact h0
        have hbr2 : ((N - 1) / n - 1 + 1) * n = ((N - 1) / n - 1) * n + n := by ring
        have hbr3 : (N - 1) / n - 1 + 1 = (N - 1) / n := by omega
        have hbr4 : ((N - 1) / n - 1) * n + n = ((N - 1) / n) * n := by
          rw [← hbr2, hbr3]
        have he0 : N - 2 = ((N - 1) / n - 1) * n + (n - 1) := by omega
        have hpin2 : ∀ m ≤ N - 2, W.vert (W.tauIdx j + m) =
            ride n (W.xEntry j) (m / n) (m % n) := fun m hm =>
          pinned_dagger W hW j hj hfresh hsf m (by omega) (by omega)
        have hdive : (N - 2) / n = (N - 1) / n - 1 := by
          rw [he0]
          exact mul_add_div_eq (by omega) _ (by omega)
        have hmode : (N - 2) % n = n - 1 := by
          rw [he0]
          exact mul_add_mod_eq (by omega) _ (by omega)
        have hσprev : W.vert (W.tauIdx j + (N - 2)) =
            ride n (W.xEntry j) ((N - 1) / n - 1) (n - 1) := by
          have h7 := hpin2 (N - 2) (le_refl _)
          rwa [hdive, hmode] at h7
        have horb2 : ∀ w,
            rotClass w = rotClass (W.vert (W.tauIdx j + (N - 2))) →
            ∃ s ≤ W.tauIdx j + (N - 2), W.vert s = w := by
          intro w hw
          rw [hσprev, rotClass_ride] at hw
          obtain ⟨k, hk, rfl⟩ := exists_ride_of_rotClass hn2 hx hw
          have hd1 := mul_add_div_eq (show 0 < n from by omega) ((N - 1) / n - 1) hk
          have hm1 := mul_add_mod_eq (show 0 < n from by omega) ((N - 1) / n - 1) hk
          refine ⟨W.tauIdx j + (((N - 1) / n - 1) * n + k), by omega, ?_⟩
          have h7 := hpin2 (((N - 1) / n - 1) * n + k) (by omega)
          rwa [hd1, hm1] at h7
        have hdprev : W.defect (W.tauIdx j + (N - 2)) = 0 :=
          W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
        have hσV : W.vert (W.tauIdx j + (N - 2)) ∈ V n (W.Efe j) := by
          rw [hσprev, hEfe]
          exact ride_mem_V hn2 hx _ _
        obtain ⟨-, halt⟩ := orbitend_alternatives W hW j hj hfresh hsf
          (W.tauIdx j + (N - 2)) (by omega) (by omega) hσV horb2 hdprev
        rcases halt with hclose | ⟨-, hdoor, -, -⟩
        · -- closing rotation: the terminal source revisits `R(h₀−1, 0)`
          have hvb1 : W.vert (W.tauIdx (j + 1) - 1) =
              ride n (W.xEntry j) ((N - 1) / n - 1) 0 := by
            rw [show W.tauIdx (j + 1) - 1 = W.tauIdx j + (N - 2) + 1 from by omega,
              hclose, hσprev, rho_ride_top hn2 hx]
            exact (List.rotate_zero _).symm
          have hd2 := mul_add_div_eq (show 0 < n from by omega)
            ((N - 1) / n - 1) (show 0 < n from by omega)
          have hm2 := mul_add_mod_eq (show 0 < n from by omega)
            ((N - 1) / n - 1) (show 0 < n from by omega)
          have hearly := hpin2 (((N - 1) / n - 1) * n + 0) (by omega)
          rw [hd2, hm2] at hearly
          refine hfirst (W.tauIdx j + (((N - 1) / n - 1) * n + 0)) (by omega) ?_
          rw [hearly, hvb1]
        · -- door: the terminal source is the fresh anchor `R(h₀, 0)`
          have hvb1 : W.vert (W.tauIdx (j + 1) - 1) =
              ride n (W.xEntry j) ((N - 1) / n) 0 := by
            rw [show W.tauIdx (j + 1) - 1 = W.tauIdx j + (N - 2) + 1 from by omega,
              hdoor, hσprev, door_ride_top, hbr3]
            exact (List.rotate_zero _).symm
          exact hkill ((N - 1) / n) 0 hh0lt (by omega) (by omega) hvb1 (by omega)
    · -- `0 < r₀ ≠ n−1`: the top-offset clause pins the terminal source mid-orbit
      have hnd1 : ¬ n ∣ (N - 1) := by
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        rw [hc, Nat.mul_mod_right] at hrpos
        omega
      have htop := pinned_top W hW j hj hfresh hsf hnd1 (by omega)
      have hvb1 : W.vert (W.tauIdx (j + 1) - 1) =
          ride n (W.xEntry j) ((N - 1) / n) ((N - 1) % n) := by
        rw [show W.tauIdx (j + 1) - 1 = W.tauIdx j + (N - 1) from by omega]
        exact htop
      exact hkill ((N - 1) / n) ((N - 1) % n) hh0lt hne (by omega) hvb1 (by omega)
  -- conclusion: the congruence, and the size bound
  refine ⟨?_, ?_⟩
  · show (N - 1) % n = (n - 1) % n
    rw [hmodv, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  · have hdm2 := Nat.div_add_mod (N - 1) n
    rw [Nat.mul_comm n ((N - 1) / n), hmodv] at hdm2
    have hb2 : ((N - 1) / n + 1) * n = ((N - 1) / n) * n + n := by ring
    have hb3 : (n - 1) * n = (n - 2) * n + n := by
      rw [show n - 1 = (n - 2) + 1 from by omega]
      ring
    have hb4 : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
    have hlt : ((N - 1) / n + 1) * n < ((n - 2) + 1) * n := by
      have hb5 : ((n - 2) + 1) * n = (n - 2) * n + n := by ring
      omega
    have hle2 := lt_of_mul_lt_mul_right hlt (Nat.zero_le n)
    have hle3 := Nat.mul_le_mul_right n (show (N - 1) / n + 1 ≤ n - 2 from by omega)
    omega

/-- **Lemma [lem:cornerexit] (Full-corner exit)**: at a full fresh switch-free window
with a break and non-door terminal edge, there is a vertex
`y ∈ V(L) ∩ V(E_{j+1})` visited before time `b`. -/
theorem full_corner_exit {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hfull : W.FullWindow j)
    (hbr : W.xEntry (j + 1) ≠ Msucc n (W.xEntry j))
    (hnd : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) ≠ 2) :
    ∃ y, y ∈ V n (W.Efe j) ∧ y ∈ V n (W.Efe (j + 1)) ∧
      ∃ t < W.tauIdx (j + 1), W.vert t = y := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hEfe : W.Efe j = genLoop (W.xEntry j) :=
    W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
  obtain ⟨hvis, hcorner⟩ := pinned_full W hW j hj hfresh hsf hfull
  set z := W.vert (W.tauIdx (j + 1)) with hzdef
  have hxz : W.xEntry (j + 1) = z := rfl
  have hzperm : IsPermWord n z := W.vert_isPerm hb
  have hσperm : IsPermWord n (W.vert (W.tauIdx (j + 1) - 1)) := W.vert_isPerm (by omega)
  -- the terminal edge has weight 3
  have hb1eq : W.tauIdx (j + 1) - 1 + 1 = W.tauIdx (j + 1) := by omega
  have hd' : W.defect (W.tauIdx (j + 1) - 1) = 0 :=
    W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) (by omega)
  have hFEb : W.IsFirstEntryTime (W.tauIdx (j + 1) - 1 + 1) := by
    rw [hb1eq]
    exact W.isFirstEntry_tauIdx hj1
  have hwt2 := W.two_le_wt_into_firstEntry hFEb
  rw [hb1eq, ← hzdef] at hwt2
  have hwle := localtight_wt_le_three W hW (W.tauIdx (j + 1) - 1) (by omega) hd'
  rw [hb1eq, ← hzdef] at hwle
  have hwt3 : wt n (W.vert (W.tauIdx (j + 1) - 1)) z = 3 := by omega
  have hn3 : 3 ≤ n := le_n_of_wt_eq hσperm hwt3 (by omega)
  -- name the marker and split the corner word
  obtain ⟨A, hA⟩ : ∃ A, (W.xEntry j).getLastD 0 = A := ⟨_, rfl⟩
  have hcw : ride n (W.xEntry j) (n - 2) (n - 1) =
      (W.xEntry j).getLastD 0 ::
        ((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate (n - 2) := by
    rw [ride, rideAnchor_eq_all (by omega) hx (n - 2),
      rotate_last _ _ (by rw [List.length_rotate, erase_getLastD hx.nodup,
        List.length_dropLast, hx.length])]
  obtain ⟨β, γ, r, hur⟩ : ∃ β γ r,
      ((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate (n - 2) = β :: γ :: r := by
    have hlen : (((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate
        (n - 2)).length = n - 1 := by
      rw [List.length_rotate, erase_getLastD hx.nodup, List.length_dropLast, hx.length]
    rcases hu : ((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate (n - 2)
      with _ | ⟨β, t⟩
    · rw [hu] at hlen
      simp at hlen
      omega
    · rcases t with _ | ⟨γ, r⟩
      · rw [hu] at hlen
        simp at hlen
        omega
      · exact ⟨β, γ, r, rfl⟩
  have hσc : W.vert (W.tauIdx (j + 1) - 1) = A :: β :: γ :: r := by
    rw [hcorner, hcw, hur, hA]
  have hσcperm : IsPermWord n (A :: β :: γ :: r) := by
    rw [← hσc]
    exact hσperm
  -- distinctness of the three corner symbols
  have hσcnd := hσcperm.nodup
  have hnd1 := List.nodup_cons.mp hσcnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have hAmem := hnd1.1
  simp only [List.mem_cons, not_or] at hAmem
  obtain ⟨hAβ, hAγ, hAr⟩ := hAmem
  have hβmem := hnd2.1
  simp only [List.mem_cons, not_or] at hβmem
  obtain ⟨hβγ, hβr⟩ := hβmem
  have hγr := hnd3.1
  -- the successor value
  have hmsucc : Msucc n (W.xEntry j) = r ++ [γ, β, A] := by
    show (((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate (n - 2)).drop 2 ++
      [(((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate (n - 2)).getD 1 0,
        (((W.xEntry j).erase ((W.xEntry j).getLastD 0)).rotate (n - 2)).getD 0 0,
        (W.xEntry j).getLastD 0] = r ++ [γ, β, A]
    rw [hur, hA]
    rfl
  -- split the landing word after the overlap
  have hover := (wt_spec (u := W.vert (W.tauIdx (j + 1) - 1)) (v := z) (by omega)
    (le_of_eq hσperm.length)).2.2
  rw [hwt3] at hover
  have hzr : z = r ++ z.drop (n - 3) := by
    conv_lhs => rw [← List.take_append_drop (n - 3) z]
    congr 1
    rw [← hover, hσc]
    rfl
  obtain ⟨t1, t2, t3, hz3⟩ : ∃ t1 t2 t3, z.drop (n - 3) = [t1, t2, t3] := by
    apply List.length_eq_three.mp
    rw [List.length_drop, hzperm.length]
    omega
  rw [hz3] at hzr
  -- the tail is a permutation of the three corner symbols
  have hznd := hzperm.nodup
  rw [hzr] at hznd
  have hzndparts := List.nodup_append.mp hznd
  have hznd3 := hzndparts.2.1
  have hzσ : z ~ A :: β :: γ :: r :=
    (isPermWord_iff_perm_refList.mp hzperm).trans
      (isPermWord_iff_perm_refList.mp hσcperm).symm
  have hch : r ++ [t1, t2, t3] ~ r ++ [A, β, γ] := by
    rw [← hzr]
    exact hzσ.trans (List.perm_append_comm (l₁ := [A, β, γ]) (l₂ := r))
  have hperm3 : [t1, t2, t3] ~ [A, β, γ] := (List.perm_append_left_iff r).mp hch
  -- properness rules out the forbidden prefixes
  have hps : ProperStep n (W.vert (W.tauIdx (j + 1) - 1)) z := by
    have h7 := W.properStep (show W.tauIdx (j + 1) - 1 + 1 < W.numVerts from by omega)
    rwa [hb1eq] at h7
  have hprop := (properStep_iff_prop n (W.vert (W.tauIdx (j + 1) - 1)) z
    hσperm hzperm).mp hps
  have hne1 : t1 ≠ A := by
    intro he
    apply hprop 1 (by omega) (by rw [hwt3]; omega)
    rw [hwt3, hz3, hσc, he]
    rfl
  have hne2 : ([t1, t2] : List ℕ).toFinset ≠ ([A, β] : List ℕ).toFinset := by
    intro he
    apply hprop 2 (by omega) (by rw [hwt3]; omega)
    rw [hwt3, hz3, hσc]
    exact he
  -- membership of the tail symbols
  have ht1mem : t1 ∈ [A, β, γ] := hperm3.subset List.mem_cons_self
  have ht2mem : t2 ∈ [A, β, γ] :=
    hperm3.subset (List.mem_cons_of_mem _ List.mem_cons_self)
  have ht3mem : t3 ∈ [A, β, γ] :=
    hperm3.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht1mem ht2mem ht3mem
  have ht12 : t1 ≠ t2 := (List.nodup_cons.mp hznd3).1 ∘ (by
    intro he
    rw [he]
    exact List.mem_cons_self)
  have ht13 : t1 ≠ t3 := (List.nodup_cons.mp hznd3).1 ∘ (by
    intro he
    rw [he]
    exact List.mem_cons_of_mem _ List.mem_cons_self)
  have ht23 : t2 ≠ t3 :=
    (List.nodup_cons.mp (List.nodup_cons.mp hznd3).2).1 ∘ (by
      intro he
      rw [he]
      exact List.mem_cons_self)
  -- the three-way case analysis on the tail
  have hcase : (t1 = β ∧ t2 = γ ∧ t3 = A) ∨ (t1 = γ ∧ t2 = A ∧ t3 = β) ∨
      (t1 = γ ∧ t2 = β ∧ t3 = A) := by
    rcases ht1mem with h1 | h1 | h1
    · exact absurd h1 hne1
    · -- t1 = β
      rcases ht2mem with h2 | h2 | h2
      · exfalso
        apply hne2
        rw [h1, h2]
        ext y
        simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · exact absurd (h1.trans h2.symm) ht12
      · rcases ht3mem with h3 | h3 | h3
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact absurd (h1.trans h3.symm) ht13
        · exact absurd (h2.trans h3.symm) ht23
    · -- t1 = γ
      rcases ht2mem with h2 | h2 | h2
      · rcases ht3mem with h3 | h3 | h3
        · exact absurd (h2.trans h3.symm) ht23
        · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
        · exact absurd (h1.trans h3.symm) ht13
      · rcases ht3mem with h3 | h3 | h3
        · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
        · exact absurd (h2.trans h3.symm) ht23
        · exact absurd (h1.trans h3.symm) ht13
      · exact absurd (h1.trans h2.symm) ht12
  -- shared computation: the deleted word of the entry
  have hclassx : rotClass ((W.xEntry j).dropLast) = rotClass (β :: γ :: r) := by
    rw [← erase_getLastD hx.nodup]
    rw [← hur]
    exact (rotClass_eq_iff.mpr ⟨n - 2, rfl⟩)
  rcases hcase with ⟨he1, he2, he3⟩ | ⟨he1, he2, he3⟩ | ⟨he1, he2, he3⟩
  · -- (β, γ, A): the landing would re-generate `E_j`, impossible
    exfalso
    rw [he1, he2, he3] at hzr
    have hzform : z = (r ++ [β, γ]) ++ [A] := by
      rw [hzr]
      simp
    have hgz : genLoop z = (A, rotClass (r ++ [β, γ])) := by
      rw [hzform]
      show (((r ++ [β, γ]) ++ [A]).getLastD 0,
        rotClass ((r ++ [β, γ]) ++ [A]).dropLast) = _
      rw [List.getLastD_concat, List.dropLast_concat]
    have hrot2 : rotClass (r ++ [β, γ]) = rotClass (β :: γ :: r) := by
      refine (rotClass_eq_iff.mpr ⟨2, ?_⟩).symm
      rw [List.rotate_eq_drop_append_take (by simp only [List.length_cons]; omega)]
      rfl
    have hEfeEq : W.Efe j = W.Efe (j + 1) := by
      rw [Efe_eq_genLoop_xEntry W (j + 1) hj1, hxz, hgz, hEfe]
      show (_, rotClass ((W.xEntry j).dropLast)) = _
      rw [hA, hclassx, ← hrot2]
    exact Efe_injective W j (j + 1) (by omega) hj1 (by omega) hEfeEq
  · -- (γ, A, β): the genuine exit; take `y = r β γ A`
    rw [he1, he2, he3] at hzr
    have hyperm : IsPermWord n (r ++ [β, γ, A]) := by
      have s1 : (γ :: A :: r) ~ (A :: γ :: r) := List.Perm.swap A γ r
      have s2 : (β :: γ :: A :: r) ~ (β :: A :: γ :: r) := s1.cons β
      have s3 : (β :: A :: γ :: r) ~ (A :: β :: γ :: r) := List.Perm.swap A β (γ :: r)
      have hyp : (r ++ [β, γ, A]) ~ (A :: β :: γ :: r) :=
        (List.perm_append_comm (l₁ := r) (l₂ := [β, γ, A])).trans (s2.trans s3)
      exact isPermWord_iff_perm_refList.mpr
        (hyp.trans (isPermWord_iff_perm_refList.mp hσcperm))
    have hymemL : r ++ [β, γ, A] ∈ V n (W.Efe j) := by
      rw [hEfe]
      refine ⟨hyperm, ?_⟩
      show rotClass ((r ++ [β, γ, A]).erase ((W.xEntry j).getLastD 0)) =
        rotClass ((W.xEntry j).dropLast)
      rw [hA]
      have herase : (r ++ [β, γ, A]).erase A = r ++ [β, γ] := by
        rw [show r ++ [β, γ, A] = (r ++ [β, γ]) ++ [A] from by simp,
          List.erase_append_right _ (by
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            rintro (h | h | h)
            · exact hAr h
            · exact hAβ h
            · exact hAγ h),
          List.erase_cons_head, List.append_nil]
      rw [herase, hclassx]
      refine (rotClass_eq_iff.mpr ⟨2, ?_⟩).symm
      rw [List.rotate_eq_drop_append_take (by simp only [List.length_cons]; omega)]
      rfl
    have hzform : z = (r ++ [γ, A]) ++ [β] := by
      rw [hzr]
      simp
    have hgz : genLoop z = (β, rotClass (r ++ [γ, A])) := by
      rw [hzform]
      show (((r ++ [γ, A]) ++ [β]).getLastD 0,
        rotClass ((r ++ [γ, A]) ++ [β]).dropLast) = _
      rw [List.getLastD_concat, List.dropLast_concat]
    have hymemR : r ++ [β, γ, A] ∈ V n (W.Efe (j + 1)) := by
      rw [Efe_eq_genLoop_xEntry W (j + 1) hj1, hxz, hgz]
      refine ⟨hyperm, ?_⟩
      show rotClass ((r ++ [β, γ, A]).erase β) = rotClass (r ++ [γ, A])
      rw [List.erase_append_right _ hβr, List.erase_cons_head]
    refine ⟨r ++ [β, γ, A], hymemL, hymemR, ?_⟩
    have hy' : r ++ [β, γ, A] ∈
        {w | ∃ t, W.tauIdx j ≤ t ∧ t < W.tauIdx (j + 1) ∧ W.vert t = w} := by
      rw [hvis]
      exact hymemL
    obtain ⟨t, -, ht2, hty⟩ := hy'
    exact ⟨t, ht2, hty⟩
  · -- (γ, β, A): the landing is `M(x_j)`, excluded by the break hypothesis
    exfalso
    rw [he1, he2, he3] at hzr
    apply hbr
    rw [hxz, hzr, ← hmsucc]

/-- **Lemma [lem:fullresidual] (Full residual charge)**: under the hypotheses of
Lemma [lem:cornerexit], `𝒞(j) ≠ ∅`. -/
theorem full_residual_charge {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hfull : W.FullWindow j)
    (hbr : W.xEntry (j + 1) ≠ Msucc n (W.xEntry j))
    (hnd : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) ≠ 2) :
    (W.chargeSet j).Nonempty := by
  obtain ⟨y, hyL, hyL', t, ht, hty⟩ :=
    full_corner_exit W hW j hj hfresh hsf hfull hbr hnd
  have hj1 : j + 1 < W.numFE := hj.1.1
  have hL'ent : W.Entered (W.Efe (j + 1)) := Efe_entered W (j + 1) hj1
  have hO : Incident n (rotClass y) (W.Efe (j + 1)) :=
    (incident_iff_exists_mem n _ _).mpr ⟨y, rfl, hyL'⟩
  have hpre : W.PreEntryOwner (rotClass y) (W.Efe (j + 1)) := by
    refine ⟨⟨hL'ent, hO⟩, t, ?_, by rw [hty]⟩
    rw [W.tauLoop_Efe hj1]
    exact ht
  obtain ⟨hD, _, hFne⟩ := owner_bookkeeping W hW _ _ hpre
  exact ⟨(rotClass y, W.Efe (j + 1)), hD, hO, Or.inr rfl, fun _ => hFne⟩

/-- **Lemma [lem:missed] (Anchored missed-orbit dichotomy)**: let `L` be an entered
loop and `O ⊆ V(L)` a rotation orbit first visited at time `t`; if there is a
first-entry time `t₀ ≤ t` such that `L` was already entered before `t₀`, then either
some shared rotation orbit is owned by `L`, or some positive-defect edge lands in
`V(L)`. -/
theorem anchored_missed_orbit {n : ℕ} (W : Walk n) (hW : W.Covering)
    (L : MarkedLoop) (O : RotClass) (hOL : Incident n O L) (hL : W.Entered L)
    (t : ℕ) (ht : t < W.numVerts) (htO : rotClass (W.vert t) = O)
    (hfirst : ∀ s < t, rotClass (W.vert s) ≠ O)
    (t0 : ℕ) (ht0 : W.IsFirstEntryTime t0) (ht0t : t0 ≤ t)
    (hbef : W.EnteredBefore t0 L) :
    (∃ O', O' ∈ W.Dset ∧ L ∈ W.OmegaSet O') ∨
      ∃ i ∈ W.Pset, W.vert (i + 1) ∈ V n L := by
  obtain ⟨sb, hsb, hsbL⟩ := hbef
  have ht0pos : 0 < t0 := by omega
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push_neg at hlt
    refine hfirst 0 (by omega) ?_
    rw [eq_of_isPermWord_le_one (by omega) (W.vert_isPerm (by omega))
      (W.vert_isPerm ht)]
    exact htO
  -- if some positive-defect edge of the anchored segment lands in `V(L)`, done
  by_cases hcross : ∃ i, t0 ≤ i ∧ i < t ∧ 0 < W.defect i ∧ W.vert (i + 1) ∈ V n L
  · obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hcross
    exact Or.inr ⟨i, ⟨by omega, hi3⟩, hi4⟩
  push_neg at hcross
  -- the arrival at `O` is not a rotation, so it activates `L(π_t)`
  have ht1e : t - 1 + 1 = t := by omega
  have hwt : 2 ≤ wt n (W.vert (t - 1)) (W.vert t) := by
    by_contra hlt2
    push_neg at hlt2
    have hu := W.vert_isPerm (show t - 1 < W.numVerts from by omega)
    have hv := W.vert_isPerm ht
    have hw1 : wt n (W.vert (t - 1)) (W.vert t) = 1 := by
      have h7 := (wt_spec (u := W.vert (t - 1)) (v := W.vert t) (by omega)
        (le_of_eq hu.length)).1
      omega
    have hrho : W.vert t = rho (W.vert (t - 1)) :=
      eq_rho_of_wt_one (by omega) hu hv hw1
    refine hfirst (t - 1) (by omega) ?_
    rw [← htO, hrho]
    exact rotClass_eq_iff.mpr ⟨1, rfl⟩
  have hactt : W.activeLoop t = genLoop (W.vert t) := by
    rw [← ht1e]
    exact W.activeLoop_of_two_le_wt (by rw [ht1e]; exact hwt)
  by_cases hHt : genLoop (W.vert t) = L
  case neg =>
    -- the landing loop is a second owner of `O`
    left
    refine ⟨O, ?_, hL, hOL⟩
    show 2 ≤ W.mu O
    exact (Set.one_lt_ncard (W.omega_finite O)).mpr
      ⟨L, ⟨hL, hOL⟩, genLoop (W.vert t), ⟨⟨t, ht, hactt⟩,
        incident_of_mem _ htO (mem_V_genLoop n _ (W.vert_isPerm ht))⟩,
        fun hcon => hHt hcon.symm⟩
  case pos =>
    -- the return case: find the last anchored index before `t`
    have htnFE : ¬ W.IsFirstEntryTime t := by
      intro hFE
      exact hFE.2 sb (by omega) (by rw [hsbL, hactt, hHt])
    have ht0lt : t0 < t := by
      rcases Nat.lt_or_eq_of_le ht0t with h | h
      · exact h
      · exact absurd (h ▸ ht0) htnFE
    set S := {s | t0 ≤ s ∧ s < t ∧ (W.IsFirstEntryTime s ∨ W.vert s ∉ V n L)}
      with hSdef
    have hSne : S.Nonempty := ⟨t0, le_refl _, ht0lt, Or.inl ht0⟩
    have hSfin : S.Finite := (Set.finite_Iio t).subset (fun s hs => hs.2.1)
    have hs0mem : sSup S ∈ S := hSne.csSup_mem hSfin
    obtain ⟨hs0a, hs0b, hs0anch⟩ := hs0mem
    have hs0max : ∀ s', sSup S < s' → s' < t →
        W.vert s' ∈ V n L ∧ ¬ W.IsFirstEntryTime s' := by
      intro s' h1 h2
      by_contra hcon
      have hs'S : s' ∈ S := by
        refine ⟨by omega, h2, ?_⟩
        rcases Classical.em (W.IsFirstEntryTime s') with h | h
        · exact Or.inl h
        · rcases Classical.em (W.vert s' ∈ V n L) with h' | h'
          · exact absurd ⟨h', h⟩ hcon
          · exact Or.inr h'
      have := le_csSup hSfin.bddAbove hs'S
      omega
    have htarget : W.vert (sSup S + 1) ∈ V n L := by
      rcases Nat.lt_or_eq_of_le (show sSup S + 1 ≤ t from by omega) with h | h
      · exact (hs0max (sSup S + 1) (by omega) h).1
      · rw [h]
        exact hOL _ htO
    have hH : W.activeLoop (sSup S) ≠ L := by
      rcases hs0anch with hFE | hnV
      · intro hcon
        exact hFE.2 sb (by omega) (by rw [hsbL, hcon])
      · intro hcon
        exact hnV (by rw [← hcon]; exact vert_mem_activeLoop W _ (by omega))
    have hd0 : W.defect (sSup S) = 0 := by
      have hle : W.defect (sSup S) ≤ 0 := by
        by_contra hpos
        push_neg at hpos
        exact hcross (sSup S) hs0a (by omega) hpos htarget
      have h8 := W.defect_nonneg_of_pos (by omega)
        (show sSup S + 1 < W.numVerts from by omega)
      omega
    left
    exact anchored_boundary W hW L (sSup S) (by omega) ⟨sb, by omega, hsbL⟩
      htarget hd0 hH

/-- **Lemma [lem:shortresidual] (Short residual dispatch)**: a fresh switch-free short
window at `j ∈ A₀` with non-door terminal edge yields a charge or a crossing
positive-defect edge into `V(L)`. -/
theorem short_residual_dispatch {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) (hfresh : W.FreshWindow j) (hsf : W.SwitchFree j)
    (hshort : W.ShortWindow j)
    (hnd : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) ≠ 2) :
    (W.chargeSet j).Nonempty ∨ ∃ i ∈ W.Pset, W.vert (i + 1) ∈ V n (W.Efe j) := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hab : W.tauIdx j < W.tauIdx (j + 1) :=
    W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj1
  have hτ : W.tauIdx j < W.numVerts := by omega
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  obtain ⟨hcong, hsize⟩ := nondoor_short_ending W hW j hj hfresh hsf hshort hnd
  obtain ⟨hmemall, hmiss⟩ := pinned_missed W hW j hj hfresh hsf hcong hsize
  -- the missed rotation orbit of `V(L)`
  set O := rotClass (rideAnchor n (W.xEntry j) (n - 2)) with hOdef
  have hOL : Incident n O (W.Efe j) := by
    apply incident_of_mem (rideAnchor n (W.xEntry j) (n - 2)) rfl
    have h7 := hmemall 0 (by omega)
    rwa [show ride n (W.xEntry j) (n - 2) 0 = rideAnchor n (W.xEntry j) (n - 2)
      from List.rotate_zero _] at h7
  -- the first visit to `O` (the walk is covering)
  obtain ⟨i0, hi0, hi0w⟩ :=
    List.getElem_of_mem (hW _ (isPermWord_rideAnchor hn2 hx (n - 2)))
  have hne : {s | s < W.numVerts ∧ rotClass (W.vert s) = O}.Nonempty :=
    ⟨i0, hi0, by rw [W.vert_eq_getElem hi0, hi0w]⟩
  obtain ⟨ht1, ht2⟩ := W.sVisit_spec hne
  have htmin : ∀ s < W.sVisit O, rotClass (W.vert s) ≠ O := by
    intro s hs hcon
    have h8 := W.sVisit_le (show s < W.numVerts from by omega) hcon
    omega
  -- the first visit happens at or after `b = τ_{j+1}`
  have htb : W.tauIdx (j + 1) ≤ W.sVisit O := by
    by_contra hlt
    push_neg at hlt
    rcases Nat.lt_or_ge (W.sVisit O) (W.tauIdx j) with hlt2 | hge2
    · exact hfresh _ hlt2 (hOL _ ht2)
    · have hO2 : rotClass (W.vert (W.sVisit O)) =
          rotClass (rideAnchor n (W.xEntry j) (n - 2)) := by
        rw [← hOdef]
        exact ht2
      obtain ⟨k, hk, hkw⟩ := exists_ride_of_rotClass hn2 hx hO2
      exact hmiss (W.sVisit O) hge2 hlt k hk hkw
  -- the anchored missed-orbit dichotomy with anchor `t₀ = b`
  rcases anchored_missed_orbit W hW (W.Efe j) O hOL (Efe_entered W j (by omega))
      (W.sVisit O) ht1 ht2 htmin (W.tauIdx (j + 1)) (W.isFirstEntry_tauIdx hj1) htb
      ⟨W.tauIdx j, hab, rfl⟩ with ⟨O', hO'D, hO'Ω⟩ | hcr
  · left
    exact ⟨(O', W.Efe j), hO'D, hO'Ω.2, Or.inl rfl,
      fun hcon => absurd hcon (Efe_injective W j (j + 1) (by omega) hj1 (by omega))⟩
  · right
    exact hcr

/-- **Lemma [lem:dispatch] (Endpoint-or-cross dispatch)**: for every `j ∈ A₀`, either
`𝒞(j) ≠ ∅`, or there is an edge `i ∈ P` with `π_{i+1} ∈ V(E_j)`. -/
theorem endpoint_or_cross {n : ℕ} (W : Walk n) (hW : W.Covering) (j : ℕ)
    (hj : j ∈ W.A0Set) :
    (W.chargeSet j).Nonempty ∨ ∃ i ∈ W.Pset, W.vert (i + 1) ∈ V n (W.Efe j) := by
  by_cases hw : wt n (W.vert (W.tauIdx (j + 1) - 1)) (W.vert (W.tauIdx (j + 1))) = 2
  · exact Or.inl (immediate_charge W hW j hj (Or.inl hw))
  by_cases hfresh : W.FreshWindow j
  case neg => exact Or.inl (immediate_charge W hW j hj (Or.inr (Or.inl hfresh)))
  by_cases hsf : W.SwitchFree j
  case neg =>
    exact Or.inl (immediate_charge W hW j hj (Or.inr (Or.inr (not_forall_not.mp hsf))))
  have hnl := no_long_nondoor W hW j hj hfresh hsf hw
  rcases Nat.lt_or_ge (W.tauIdx (j + 1) - W.tauIdx j) (n * (n - 1)) with hshort | hge
  · exact short_residual_dispatch W hW j hj hfresh hsf hshort hw
  · have hfull : W.FullWindow j := le_antisymm hnl hge
    exact Or.inl (full_residual_charge W hW j hj hfresh hsf hfull hj.1.2 hw)

/-- **Lemma [lem:uncharged] (Uncharged breaks), display (8)**: `|B| ≤ n|P|`. -/
theorem uncharged_le {n : ℕ} (W : Walk n) (hW : W.Covering) :
    W.Bset.ncard ≤ n * W.Pset.ncard := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- over the empty alphabet only one loop is ever active, so there are no breaks
    have hBempty : W.Bset = ∅ := by
      ext j
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hj
      have hbr : W.IsBreak j := hj.1.1
      have hall : ∀ s, s < W.numVerts → W.activeLoop s = W.activeLoop 0 := by
        intro s
        induction s with
        | zero => intro _; rfl
        | succ s ih =>
          intro hs
          show (if 2 ≤ wt 0 (W.vert s) (W.vert (s + 1)) then genLoop (W.vert (s + 1))
            else W.activeLoop s) = _
          rw [wt_eq_zero_of_n_zero, if_neg (by omega)]
          exact ih (by omega)
      have hFE : ∀ t, W.IsFirstEntryTime t → t = 0 := by
        intro t htFE
        by_contra ht0
        exact htFE.2 0 (by omega) (hall t htFE.1).symm
      have hone : W.numFE ≤ 1 := by
        have hsub : setOf W.IsFirstEntryTime ⊆ {0} := fun t ht => hFE t ht
        calc W.numFE ≤ ({0} : Set ℕ).ncard :=
              Set.ncard_le_ncard hsub (Set.finite_singleton 0)
          _ = 1 := Set.ncard_singleton 0
      have := hbr.1
      omega
    rw [hBempty]
    simp
  · -- dispatch each uncharged break to a crossing edge, and count markers
    have hchoice : ∀ j ∈ W.Bset, ∃ i, i ∈ W.Pset ∧ W.vert (i + 1) ∈ V n (W.Efe j) := by
      intro j hj
      have hjA0 : j ∈ W.A0Set := hj.1
      have hnc : ¬ W.Charged j := fun hc => hj.2 ⟨hjA0, hc⟩
      rcases endpoint_or_cross W hW j hjA0 with hch | hcr
      · exact absurd hch hnc
      · obtain ⟨i, hi, hmem⟩ := hcr
        exact ⟨i, hi, hmem⟩
    set iOf : ℕ → ℕ :=
      fun j => sInf {i | i ∈ W.Pset ∧ W.vert (i + 1) ∈ V n (W.Efe j)} with hiOf
    have hiOfspec : ∀ j ∈ W.Bset,
        iOf j ∈ W.Pset ∧ W.vert (iOf j + 1) ∈ V n (W.Efe j) := by
      intro j hj
      obtain ⟨i, hi⟩ := hchoice j hj
      exact Nat.sInf_mem
        (⟨i, hi⟩ : {i | i ∈ W.Pset ∧ W.vert (i + 1) ∈ V n (W.Efe j)}.Nonempty)
    have hPfin : W.Pset.Finite := (Set.finite_Iio W.numVerts).subset (fun i hi => by
      have := hi.1
      simp only [Set.mem_Iio]
      omega)
    have hBfin : W.Bset.Finite := W.breakSet_finite.subset (fun j hj => hj.1.1)
    have hmaps : ∀ j ∈ hBfin.toFinset, iOf j ∈ hPfin.toFinset := by
      intro j hj
      exact hPfin.mem_toFinset.mpr (hiOfspec j (hBfin.mem_toFinset.mp hj)).1
    have hcount := Finset.card_eq_sum_card_fiberwise (f := iOf) (s := hBfin.toFinset)
      (t := hPfin.toFinset) hmaps
    have hfib : ∀ i ∈ hPfin.toFinset,
        (hBfin.toFinset.filter (fun j => iOf j = i)).card ≤ n := by
      intro i _
      have hmapsE : ∀ j ∈ hBfin.toFinset.filter (fun j => iOf j = i),
          (W.Efe j).1 ∈ Finset.Icc 1 n := by
        intro j hj
        rw [Finset.mem_filter] at hj
        have hjB := hBfin.mem_toFinset.mp hj.1
        have hjFE : j < W.numFE := by
          have := hjB.1.1.1
          omega
        exact (W.isMarkedLoop_of_entered hn (Efe_entered W j hjFE)).1
      have hinjE : Set.InjOn (fun j => (W.Efe j).1)
          ↑(hBfin.toFinset.filter (fun j => iOf j = i)) := by
        intro j hj j' hj' heq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj hj'
        have hjB := hBfin.mem_toFinset.mp hj.1
        have hj'B := hBfin.mem_toFinset.mp hj'.1
        have hjFE : j < W.numFE := by
          have := hjB.1.1.1
          omega
        have hj'FE : j' < W.numFE := by
          have := hj'B.1.1.1
          omega
        have heq' : (W.Efe j).1 = (W.Efe j').1 := heq
        have hV := (hiOfspec j hjB).2
        have hV' := (hiOfspec j' hj'B).2
        rw [hj.2] at hV
        rw [hj'.2] at hV'
        have hloopeq : W.Efe j = W.Efe j' := by
          refine Prod.ext heq' ?_
          rw [← hV.2, ← hV'.2, heq']
        by_contra hne
        exact Efe_injective W j j' hjFE hj'FE hne hloopeq
      have hle := Finset.card_le_card_of_injOn (f := fun j => (W.Efe j).1)
        hmapsE hinjE
      rw [Nat.card_Icc] at hle
      omega
    have hfinal : hBfin.toFinset.card ≤ hPfin.toFinset.card * n := by
      rw [hcount]
      calc ∑ i ∈ hPfin.toFinset, (hBfin.toFinset.filter (fun j => iOf j = i)).card
          ≤ ∑ _i ∈ hPfin.toFinset, n := Finset.sum_le_sum hfib
        _ = hPfin.toFinset.card * n := by rw [Finset.sum_const, smul_eq_mul]
    rw [Set.ncard_eq_toFinset_card _ hBfin, Set.ncard_eq_toFinset_card _ hPfin,
      Nat.mul_comm]
    exact hfinal

/-- **Lemma [lem:slot] (Slot fibers)**, part 1: every incident slot receives at most
two charges. -/
theorem slot_fiber_le_two {n : ℕ} (W : Walk n) (hW : W.Covering)
    (s : RotClass × MarkedLoop) (hs : W.IncidentSlot s) :
    (W.Gfiber s).ncard ≤ 2 := by
  classical
  have hfin := W.gfiber_finite s
  have hsplit : W.Gfiber s ⊆
      {j ∈ W.Gfiber s | W.LeftCharge j} ∪ {j ∈ W.Gfiber s | W.RightCharge j} := by
    intro j hj
    rcases (W.charge_mem hj.1.2).2.2.1 with h | h
    · exact Or.inl ⟨hj, h⟩
    · exact Or.inr ⟨hj, h⟩
  have hL1 : {j ∈ W.Gfiber s | W.LeftCharge j}.ncard ≤ 1 := by
    rw [Set.ncard_le_one (hfin.subset (Set.sep_subset _ _))]
    rintro a ⟨⟨haG, has⟩, haL⟩ b ⟨⟨hbG, hbs⟩, hbL⟩
    by_contra hne
    have h1 : W.Efe a = W.Efe b := by
      rw [← haL, ← hbL, has, hbs]
    exact Efe_injective W a b (by have := haG.1.1.1; omega)
      (by have := hbG.1.1.1; omega) hne h1
  have hR1 : {j ∈ W.Gfiber s | W.RightCharge j}.ncard ≤ 1 := by
    rw [Set.ncard_le_one (hfin.subset (Set.sep_subset _ _))]
    rintro a ⟨⟨haG, has⟩, haR⟩ b ⟨⟨hbG, hbs⟩, hbR⟩
    by_contra hne
    have h1 : W.Efe (a + 1) = W.Efe (b + 1) := by
      rw [← haR, ← hbR, has, hbs]
    have := Efe_injective W (a + 1) (b + 1) haG.1.1.1 hbG.1.1.1 (by omega) h1
    exact this
  calc (W.Gfiber s).ncard
      ≤ ({j ∈ W.Gfiber s | W.LeftCharge j} ∪
          {j ∈ W.Gfiber s | W.RightCharge j}).ncard :=
        Set.ncard_le_ncard hsplit
          ((hfin.subset (Set.sep_subset _ _)).union (hfin.subset (Set.sep_subset _ _)))
    _ ≤ {j ∈ W.Gfiber s | W.LeftCharge j}.ncard +
          {j ∈ W.Gfiber s | W.RightCharge j}.ncard := Set.ncard_union_le _ _
    _ ≤ 2 := by omega

/-- **Lemma [lem:slot]**, part 2: an initial slot (`L = F(O)`) receives at most one
charge. -/
theorem slot_fiber_initial {n : ℕ} (W : Walk n) (hW : W.Covering)
    (s : RotClass × MarkedLoop) (hs : W.IncidentSlot s)
    (hinit : s.2 = W.Fowner s.1) :
    (W.Gfiber s).ncard ≤ 1 := by
  classical
  have hfin := W.gfiber_finite s
  have hleft : ∀ a ∈ W.Gfiber s, W.LeftCharge a := by
    rintro a ⟨haG, has⟩
    rcases (W.charge_mem haG.2).2.2.1 with h | h
    · exact h
    · exfalso
      exact (W.charge_mem haG.2).2.2.2 h (by rw [has]; exact hinit)
  rw [Set.ncard_le_one hfin]
  intro a ha b hb
  by_contra hne
  have h1 : W.Efe a = W.Efe b := by
    rw [← hleft a ha, ← hleft b hb, ha.2, hb.2]
  exact Efe_injective W a b (by have := ha.1.1.1.1; omega)
    (by have := hb.1.1.1.1; omega) hne h1

/-- **Lemma [lem:slot]**, part 3: a slot receiving two charges receives one left and
one right charge. -/
theorem slot_fiber_two_leftright {n : ℕ} (W : Walk n) (hW : W.Covering)
    (s : RotClass × MarkedLoop) (hs : W.IncidentSlot s)
    (h2 : (W.Gfiber s).ncard = 2) :
    ∃ j k, j ≠ k ∧ W.Gfiber s = {j, k} ∧ W.LeftCharge j ∧ W.RightCharge k := by
  obtain ⟨j, k, hjk, hset⟩ := Set.ncard_eq_two.mp h2
  have hjmem : j ∈ W.Gfiber s := by rw [hset]; exact Set.mem_insert _ _
  have hkmem : k ∈ W.Gfiber s := by
    rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hjbound := W.gfiber_lt_numFE hjmem
  have hkbound := W.gfiber_lt_numFE hkmem
  rcases (W.charge_mem hjmem.1.2).2.2.1 with hjL | hjR <;>
    rcases (W.charge_mem hkmem.1.2).2.2.1 with hkL | hkR
  · exfalso
    have h1 : W.Efe j = W.Efe k := by
      rw [← hjL, ← hkL, hjmem.2, hkmem.2]
    exact Efe_injective W j k (by omega) (by omega) hjk h1
  · exact ⟨j, k, hjk, hset, hjL, hkR⟩
  · exact ⟨k, j, hjk.symm, by rw [hset, Set.pair_comm], hkL, hjR⟩
  · exfalso
    have h1 : W.Efe (j + 1) = W.Efe (k + 1) := by
      rw [← hjR, ← hkR, hjmem.2, hkmem.2]
    have := Efe_injective W (j + 1) (k + 1) hjbound hkbound (by omega) h1
    exact this

/-- **Display (9)** (§5): since there are `μ(O) − 1` noninitial slots over `O`,
`C ≤ Σ_{O∈D} (μ(O)−1) = q`. -/
theorem Cstat_le_q {n : ℕ} (W : Walk n) (hW : W.Covering) :
    W.Cstat ≤ W.qStat := by
  classical
  set DF := W.dset_finite.toFinset with hDF
  set f : RotClass → Set (RotClass × MarkedLoop) :=
    fun O => (fun L => (O, L)) '' (W.OmegaSet O \ {W.Fowner O}) with hf
  have hfin : ∀ O ∈ DF, (f O).Finite :=
    fun O _ => (((W.omega_finite O).diff)).image _
  have hcov : {s | W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2} ⊆
      ⋃ O ∈ DF, f O := by
    rintro ⟨O, L⟩ ⟨⟨hD, hent, hinc⟩, hne, -⟩
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨O, W.dset_finite.mem_toFinset.mpr hD,
      ⟨L, ⟨⟨hent, hinc⟩, fun h => hne h⟩, rfl⟩⟩
  have hbound := ncard_le_sum_of_cover DF f hcov hfin
  have hterm : ∀ O ∈ DF, (f O).ncard = W.mu O - 1 := by
    intro O hO
    have hD : O ∈ W.Dset := W.dset_finite.mem_toFinset.mp hO
    have hOperm := W.dset_subset_permClasses hD
    have hF : W.Fowner O ∈ W.OmegaSet O := fowner_mem_Omega W hW O hOperm
    rw [hf]
    rw [Set.ncard_image_of_injOn (fun L _ L' _ h => congrArg Prod.snd h),
      Set.ncard_sdiff_singleton_of_mem hF]
    rfl
  calc W.Cstat ≤ ∑ O ∈ DF, (f O).ncard := hbound
    _ = ∑ O ∈ DF, (W.mu O - 1) := Finset.sum_congr rfl hterm
    _ = W.qStat := W.qStat_eq_sum.symm

/-- **Lemma [lem:fiber] (Refined break count), display (10)**:
`|A₀| ≤ q + |D| + C + n|P|`. -/
theorem refined_break_count {n : ℕ} (W : Walk n) (hW : W.Covering) :
    W.A0Set.ncard ≤ W.qStat + W.Dset.ncard + W.Cstat + n * W.Pset.ncard := by
  classical
  have hGsub : W.Gset ⊆ W.A0Set := fun j hj => hj.1
  have hA0fin : W.A0Set.Finite := W.breakSet_finite.subset (fun j hj => hj.1)
  have hGfin : W.Gset.Finite := hA0fin.subset hGsub
  have hsplit : W.A0Set.ncard ≤ W.Gset.ncard + W.Bset.ncard := by
    have hunion : W.A0Set = W.Gset ∪ W.Bset := by
      rw [Walk.Bset, Set.union_diff_cancel hGsub]
    rw [hunion]
    exact Set.ncard_union_le _ _
  have hB := uncharged_le W hW
  suffices hG : W.Gset.ncard ≤ W.qStat + W.Dset.ncard + W.Cstat by omega
  -- count the charged breaks through the (injective-per-slot-fiber) charge map
  have husedfin : (W.charge '' W.Gset).Finite := hGfin.image _
  have hchspec : ∀ j ∈ W.Gset, W.charge j ∈ W.chargeSet j := fun j hj => W.charge_mem hj.2
  have hIncSlot : ∀ j ∈ W.Gset, W.IncidentSlot (W.charge j) := by
    intro j hj
    obtain ⟨hD, hinc, hor, -⟩ := hchspec j hj
    have hjb : j + 1 < W.numFE := hj.1.1.1
    refine ⟨hD, ?_, hinc⟩
    rcases hor with h | h
    · rw [h]
      exact Efe_entered W j (by omega)
    · rw [h]
      exact Efe_entered W (j + 1) hjb
  have hmaps : ∀ j ∈ hGfin.toFinset, W.charge j ∈ husedfin.toFinset := by
    intro j hj
    exact husedfin.mem_toFinset.mpr ⟨j, hGfin.mem_toFinset.mp hj, rfl⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (f := W.charge)
    (s := hGfin.toFinset) (t := husedfin.toFinset) hmaps
  have hfibeq : ∀ s, (hGfin.toFinset.filter (fun j => W.charge j = s)).card =
      (W.Gfiber s).ncard := by
    intro s
    have hseteq : (↑(hGfin.toFinset.filter (fun j => W.charge j = s)) : Set ℕ) =
        W.Gfiber s := by
      ext j
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hGfin.mem_toFinset]
      exact Iff.rfl
    rw [← hseteq, Set.ncard_coe_finset]
  -- the per-slot bound: 1 in general (+1 for the double noninitial slots)
  have hperslot : ∀ s ∈ husedfin.toFinset, (W.Gfiber s).ncard ≤
      1 + (if s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2 then 1 else 0) := by
    intro s hs
    obtain ⟨j, hjG, rfl⟩ := husedfin.mem_toFinset.mp hs
    have hslot := hIncSlot j hjG
    by_cases hinit : (W.charge j).2 = W.Fowner (W.charge j).1
    · have h1 := slot_fiber_initial W hW _ hslot hinit
      have : ¬ ((W.charge j).2 ≠ W.Fowner (W.charge j).1 ∧
          (W.Gfiber (W.charge j)).ncard = 2) := fun h => h.1 hinit
      rw [if_neg this]
      omega
    · have h2 := slot_fiber_le_two W hW _ hslot
      by_cases h2eq : (W.Gfiber (W.charge j)).ncard = 2
      · rw [if_pos ⟨hinit, h2eq⟩]
        omega
      · rw [if_neg (fun h => h2eq h.2)]
        omega
  -- `Σ (1 + ite) = |used| + #(double noninitial used slots)`, and the latter is `≤ C`
  have hsum1 : ∑ s ∈ husedfin.toFinset,
      (1 + (if s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2 then 1 else 0)) =
      husedfin.toFinset.card +
        (husedfin.toFinset.filter
          (fun s => s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2)).card := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.card_eq_sum_ones]
    · rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  -- the double noninitial used slots are counted by `C`
  have hU2C : (husedfin.toFinset.filter
      (fun s => s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2)).card ≤ W.Cstat := by
    have hsub : (↑(husedfin.toFinset.filter
        (fun s => s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2)) :
          Set (RotClass × MarkedLoop)) ⊆
        {s | W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2} := by
      intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq, husedfin.mem_toFinset] at hs
      obtain ⟨⟨j, hjG, rfl⟩, hrest⟩ := hs
      exact ⟨hIncSlot j hjG, hrest⟩
    have hCfin : {s | W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧
        (W.Gfiber s).ncard = 2}.Finite := by
      refine husedfin.subset ?_
      rintro s ⟨-, -, h2⟩
      have hne : (W.Gfiber s).Nonempty :=
        (Set.ncard_pos (W.gfiber_finite s)).mp (by omega)
      obtain ⟨j, hjfib⟩ := hne
      exact ⟨j, hjfib.1, hjfib.2⟩
    calc (husedfin.toFinset.filter
        (fun s => s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2)).card
        = (↑(husedfin.toFinset.filter
            (fun s => s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2)) :
              Set (RotClass × MarkedLoop)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ W.Cstat := Set.ncard_le_ncard hsub hCfin
  -- the used slots are at most `Σ_{O ∈ D} μ(O) = q + |D|`
  have hused_le : husedfin.toFinset.card ≤ W.qStat + W.Dset.ncard := by
    have hmaps2 : ∀ s ∈ husedfin.toFinset, Prod.fst s ∈ W.dset_finite.toFinset := by
      intro s hs
      obtain ⟨j, hjG, rfl⟩ := husedfin.mem_toFinset.mp hs
      exact W.dset_finite.mem_toFinset.mpr (hchspec j hjG).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps2]
    have hfibO : ∀ O ∈ W.dset_finite.toFinset,
        (husedfin.toFinset.filter (fun s => s.1 = O)).card ≤ W.mu O := by
      intro O hO
      have hmapsE : ∀ s ∈ husedfin.toFinset.filter (fun s => s.1 = O),
          Prod.snd s ∈ (W.omega_finite O).toFinset := by
        intro s hs
        rw [Finset.mem_filter] at hs
        obtain ⟨j, hjG, hcj⟩ := husedfin.mem_toFinset.mp hs.1
        have hslot := hIncSlot j hjG
        rw [hcj] at hslot
        refine (W.omega_finite O).mem_toFinset.mpr ?_
        rw [← hs.2]
        exact ⟨hslot.2.1, hslot.2.2⟩
      have hinjE : Set.InjOn (Prod.snd : RotClass × MarkedLoop → MarkedLoop)
          ↑(husedfin.toFinset.filter (fun s => s.1 = O)) := by
        intro s hs s' hs' heq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs hs'
        exact Prod.ext (hs.2.trans hs'.2.symm) heq
      have hle := Finset.card_le_card_of_injOn
        (f := (Prod.snd : RotClass × MarkedLoop → MarkedLoop)) hmapsE hinjE
      rwa [← Set.ncard_eq_toFinset_card _ (W.omega_finite O)] at hle
    calc ∑ O ∈ W.dset_finite.toFinset,
          (husedfin.toFinset.filter (fun s => s.1 = O)).card
        ≤ ∑ O ∈ W.dset_finite.toFinset, W.mu O := Finset.sum_le_sum hfibO
      _ = ∑ O ∈ W.dset_finite.toFinset, ((W.mu O - 1) + 1) := by
          refine Finset.sum_congr rfl (fun O hO => ?_)
          have h2 : 2 ≤ W.mu O := W.dset_finite.mem_toFinset.mp hO
          omega
      _ = W.qStat + W.Dset.ncard := by
          rw [Finset.sum_add_distrib, ← W.qStat_eq_sum, Finset.sum_const, smul_eq_mul,
            Nat.mul_one, Set.ncard_eq_toFinset_card _ W.dset_finite]
  -- assemble the G-count
  calc W.Gset.ncard = hGfin.toFinset.card := Set.ncard_eq_toFinset_card _ hGfin
    _ = ∑ s ∈ husedfin.toFinset,
        (hGfin.toFinset.filter (fun j => W.charge j = s)).card := hcount
    _ = ∑ s ∈ husedfin.toFinset, (W.Gfiber s).ncard :=
        Finset.sum_congr rfl (fun s _ => hfibeq s)
    _ ≤ ∑ s ∈ husedfin.toFinset,
        (1 + (if s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2 then 1 else 0)) :=
        Finset.sum_le_sum hperslot
    _ ≤ W.qStat + W.Dset.ncard + W.Cstat := by
        rw [hsum1]
        omega

/-- **Lemma [lem:short] (Short-block credit), display (11)**:
`v(W) + C(n−3) ≤ (|A|+1)(n−2)`.  (Stated for `n ≥ 3`, as for display (3).) -/
theorem short_block_credit {n : ℕ} (W : Walk n) (hW : W.Covering) (hn : 3 ≤ n) :
    W.vStat + W.Cstat * (n - 3) ≤ (W.breakSet.ncard + 1) * (n - 2) := by
  classical
  -- each double-charged noninitial slot docks at a break following a break
  have hslotdata : ∀ s : RotClass × MarkedLoop, ∃ j,
      (W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2) →
        j ∈ W.Gfiber s ∧ W.IsBreak j ∧ W.IsBreak (j - 1) ∧ 1 ≤ j := by
    intro s
    by_cases hs : W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2
    · obtain ⟨hslot, hnoninit, h2⟩ := hs
      obtain ⟨j, k, hjk, hset, hL, hR⟩ := slot_fiber_two_leftright W hW s hslot h2
      have hjmem : j ∈ W.Gfiber s := by
        rw [hset]
        exact Set.mem_insert _ _
      have hkmem : k ∈ W.Gfiber s := by
        rw [hset]
        exact Set.mem_insert_iff.mpr (Or.inr rfl)
      have hjb : j + 1 < W.numFE := W.gfiber_lt_numFE hjmem
      have hkb : k + 1 < W.numFE := W.gfiber_lt_numFE hkmem
      have hEfe : W.Efe j = W.Efe (k + 1) := by
        have h1 : s.2 = W.Efe j := by
          rw [← hjmem.2]
          exact hL
        have h2' : s.2 = W.Efe (k + 1) := by
          rw [← hkmem.2]
          exact hR
        rw [← h1, h2']
      have hjk1 : j = k + 1 := by
        by_contra hne
        exact Efe_injective W j (k + 1) (by omega) hkb hne hEfe
      refine ⟨j, fun _ => ⟨hjmem, hjmem.1.1.1, ?_, by omega⟩⟩
      have hkbr : W.IsBreak k := hkmem.1.1.1
      rw [hjk1]
      exact hkbr
    · exact ⟨0, fun h => absurd h hs⟩
  choose φ hφ using hslotdata
  -- the C-counted slots form a finite set
  set CS : Set (RotClass × MarkedLoop) :=
    {s | W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2} with hCS
  have hA0fin : W.A0Set.Finite := W.breakSet_finite.subset (fun j hj => hj.1)
  have hGfin : W.Gset.Finite := hA0fin.subset (fun j hj => hj.1)
  have hCSfin : CS.Finite := by
    refine (hGfin.image W.charge).subset ?_
    rintro s ⟨-, -, h2⟩
    have hne : (W.Gfiber s).Nonempty :=
      (Set.ncard_pos (W.gfiber_finite s)).mp (by omega)
    obtain ⟨j, hjfib⟩ := hne
    exact ⟨j, hjfib.1, hjfib.2⟩
  set SBF : Finset ℕ := hCSfin.toFinset.image φ with hSBF
  -- the docked breaks are breaks following breaks
  have hSBbr : ∀ b ∈ SBF, W.IsBreak b ∧ (b = 0 ∨ W.IsBreak (b - 1)) := by
    intro b hb
    rw [hSBF, Finset.mem_image] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    have hsCS := hCSfin.mem_toFinset.mp hs
    obtain ⟨-, hbr, hbr', -⟩ := hφ s hsCS
    exact ⟨hbr, Or.inr hbr'⟩
  -- `C ≤ |SBF|` by injectivity of the docking
  have hCle : W.Cstat ≤ SBF.card := by
    have hinj : Set.InjOn φ ↑hCSfin.toFinset := by
      intro s hs s' hs' heq
      have hsCS := hCSfin.mem_toFinset.mp (Finset.mem_coe.mp hs)
      have hs'CS := hCSfin.mem_toFinset.mp (Finset.mem_coe.mp hs')
      have h1 := (hφ s hsCS).1
      have h2 := (hφ s' hs'CS).1
      rw [heq] at h1
      exact h1.2.symm.trans h2.2
    have h1 : W.Cstat = hCSfin.toFinset.card := by
      show CS.ncard = _
      exact Set.ncard_eq_toFinset_card _ hCSfin
    rw [h1, hSBF, Finset.card_image_of_injOn hinj]
  -- the run bound, as in `block_bound`
  have hrun : ∀ i, i < W.numFE → i - W.blockStart i ≤ n - 3 := by
    intro i hi
    have hb := (W.blockStart_spec i).1
    have hcanon := canonical_run_le W hW hn (W.blockStart i) i hb hi ?_
    · omega
    · intro j hj1 hj2
      have hnb := W.blockStart_no_break hj1 hj2
      by_contra hne
      exact hnb ⟨by omega, hne⟩
  have h := W.numFE_add_le (n - 3) hrun SBF hSBbr
  have he : n - 3 + 1 = n - 2 := by omega
  rw [he] at h
  have hmul : W.Cstat * (n - 3) ≤ SBF.card * (n - 3) :=
    Nat.mul_le_mul_right _ hCle
  rw [← numFE_eq_vStat]
  omega

/-- **Proposition [prop:interface] (Sharpness of the accounting interface)**, first
half: the displayed assignment satisfies all seven constraints (4), (5), (6a), (6b),
(9), (10), (11), each with equality. -/
theorem interface_sharp (n : ℕ) (hn : 5 ≤ n) (e ℓ : ℕ) :
    ∃ P A A0 q D C v : ℕ,
      P = e ∧ q = ℓ * (n - 1) ∧ D = ℓ * (n - 1) ∧ C = ℓ * (n - 1) ∧
      A0 = 3 * ℓ * (n - 1) + n * e ∧ A = 3 * ℓ * (n - 1) + (n + 1) * e ∧
      v = (2 * ℓ * (n - 1) + (n + 1) * e + 1) * (n - 2) + ℓ * (n - 1) ∧
      P = e ∧ A = A0 + P ∧ q = ℓ * (n - 1) ∧ D = ℓ * (n - 1) ∧ C = q ∧
      A0 = q + D + C + n * P ∧ v + C * (n - 3) = (A + 1) * (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
  have e1 : 5 + m - 1 = m + 4 := by omega
  have e2 : 5 + m - 2 = m + 3 := by omega
  have e3 : 5 + m - 3 = m + 2 := by omega
  rw [e1, e2, e3]
  refine ⟨e, 3 * ℓ * (m + 4) + (5 + m + 1) * e, 3 * ℓ * (m + 4) + (5 + m) * e,
    ℓ * (m + 4), ℓ * (m + 4), ℓ * (m + 4),
    (2 * ℓ * (m + 4) + (5 + m + 1) * e + 1) * (m + 3) + ℓ * (m + 4),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ring, rfl, rfl, rfl, by ring, by ring⟩

/-- **Proposition [prop:interface]**, "consequently": the system (4)–(11) does not
imply, for any `e, ℓ`, any upper bound on `v` smaller than
`(2ℓ(n−1) + (n+1)e + 1)(n−2) + ℓ(n−1)`. -/
theorem interface_no_better (n : ℕ) (hn : 5 ≤ n) (bnd : ℕ → ℕ → ℕ)
    (h : ∀ e ℓ P A A0 q D C v : ℕ,
      SystemFacts n e ℓ P A A0 q D C v → v ≤ bnd e ℓ) :
    ∀ e ℓ : ℕ,
      (2 * ℓ * (n - 1) + (n + 1) * e + 1) * (n - 2) + ℓ * (n - 1) ≤ bnd e ℓ := by
  intro e ℓ
  obtain ⟨P, A, A0, q, D, C, v, h1, h2, h3, h4, h5, h6, h7,
    _, h9, h10, h11, h12, h13, h14⟩ := interface_sharp n hn e ℓ
  have hsys : SystemFacts n e ℓ P A A0 q D C v :=
    ⟨h1.le, h9.le, h10, h11.le, h12.le, h13.le, h14.le⟩
  have hb := h e ℓ P A A0 q D C v hsys
  rw [← h7]
  exact hb

/-! ## §6 The coefficient-two estimate -/

/-- **Proposition [prop:twoparam], display (12)**: for `n ≥ 5` there is no covering
walk `W` with `e(W) = e` and `v(W) = (n−2)! + ℓ` if
`(2ℓ(n−1) + (n+1)e + 1)(n−2) + ℓ(n−1) < (n−2)! + ℓ`. -/
theorem twoparam (n : ℕ) (hn : 5 ≤ n) (e ℓ : ℕ)
    (h12 : (2 * ℓ * (n - 1) + (n + 1) * e + 1) * (n - 2) + ℓ * (n - 1) <
      (n - 2).factorial + ℓ) :
    ¬ ∃ W : Walk n, W.Covering ∧ W.eStat = e ∧
      W.vStat = (n - 2).factorial + ℓ := by
  rintro ⟨W, hcov, he, hv⟩
  have h6a := incidence_count_6a W hcov (by omega) ℓ hv
  have h6b := incidence_count_6b W hcov (by omega) ℓ hv
  have h4 : W.Pset.ncard ≤ e := by
    -- display (4) in unbundled form (`Walk.pset_ncard_le_eStat`)
    have h := W.pset_ncard_le_eStat (by omega)
    rw [he] at h
    exact_mod_cast h
  have h5 := break_card_le W hcov
  have h9 := Cstat_le_q W hcov
  have h10 := refined_break_count W hcov
  have h11 := short_block_credit W hcov (by omega)
  -- Step 1: |A| ≤ 2ℓ(n−1) + C + (n+1)e, via (5), (10), (6a), (6b), (4).
  have hnp : n * W.Pset.ncard ≤ n * e := Nat.mul_le_mul_left n h4
  have ha : W.breakSet.ncard ≤ 2 * (ℓ * (n - 1)) + W.Cstat + (n * e + e) := by
    have hq : W.qStat = ℓ * (n - 1) := h6a
    generalize hNP : n * W.Pset.ncard = NP at h10 hnp
    generalize hNE : n * e = NE at hnp ⊢
    generalize hL1 : ℓ * (n - 1) = L1 at h6b hq ⊢
    omega
  -- Step 2: multiply by (n−2) and use (11).
  have ha1 : (W.breakSet.ncard + 1) * (n - 2) ≤
      (2 * (ℓ * (n - 1)) + W.Cstat + (n * e + e) + 1) * (n - 2) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right ha 1)
  have hexp : (2 * (ℓ * (n - 1)) + W.Cstat + (n * e + e) + 1) * (n - 2)
      = (2 * ℓ * (n - 1) + (n + 1) * e + 1) * (n - 2) + W.Cstat * (n - 2) := by ring
  have hsplit : W.Cstat * (n - 2) = W.Cstat * (n - 3) + W.Cstat := by
    have h2 : n - 2 = (n - 3) + 1 := by omega
    rw [h2]; ring
  -- Step 3: assemble and contradict (12).
  have hCq : W.Cstat ≤ ℓ * (n - 1) := h9.trans (le_of_eq h6a)
  rw [hv] at h11
  rw [hexp, hsplit] at ha1
  generalize hY : (2 * ℓ * (n - 1) + (n + 1) * e + 1) * (n - 2) = Y at ha1 h12
  generalize hL1 : ℓ * (n - 1) = L1 at hCq h12
  generalize hCn : W.Cstat * (n - 3) = Cn at h11 ha1
  generalize hAn : (W.breakSet.ncard + 1) * (n - 2) = An at h11 ha1
  omega

/-- **Lemma [lem:corner], display (13)**: if `n ≥ 5` and
`(2k(n−1)+1)(n−2) + k(n−1) < (n−2)! + k`, then for all `e, ℓ ≥ 0` with `e + ℓ ≤ k`
the two-parameter inequality (12) holds. -/
theorem corner_reduction (n : ℕ) (hn : 5 ≤ n) (k e ℓ : ℕ)
    (h13 : (2 * k * (n - 1) + 1) * (n - 2) + k * (n - 1) < (n - 2).factorial + k)
    (hel : e + ℓ ≤ k) :
    (2 * ℓ * (n - 1) + (n + 1) * e + 1) * (n - 2) + ℓ * (n - 1) <
      (n - 2).factorial + ℓ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = e + ℓ + d := ⟨k - (e + ℓ), by omega⟩
  have e1 : 5 + m - 1 = m + 4 := by omega
  have e2 : 5 + m - 2 = m + 3 := by omega
  rw [e1, e2] at h13 ⊢
  have e3 : 5 + m + 1 = m + 6 := by omega
  rw [e3]
  have key : (2 * ℓ * (m + 4) + (m + 6) * e + 1) * (m + 3) + ℓ * (m + 4) + (e + ℓ + d)
      + (m + 3) * (e * (m + 3) + d * (2 * (m + 3) + 3))
      = ((2 * (e + ℓ + d) * (m + 4) + 1) * (m + 3) + (e + ℓ + d) * (m + 4)) + ℓ := by
    ring
  generalize hQ : (2 * ℓ * (m + 4) + (m + 6) * e + 1) * (m + 3) + ℓ * (m + 4) = Q
    at key ⊢
  generalize hP : (2 * (e + ℓ + d) * (m + 4) + 1) * (m + 3) + (e + ℓ + d) * (m + 4) = P
    at key h13
  generalize hZ : (m + 3) * (e * (m + 3) + d * (2 * (m + 3) + 3)) = Z at key
  generalize hF : (m + 3).factorial = F at h13 ⊢
  omega

/-- **Theorem [thm:criterion] (Coefficient-two criterion)**: for `n ≥ 5`, if `k ≥ 0`
satisfies `(2k(n−1)+1)(n−2) + k(n−1) < (n−2)! + k`, then `Λ(n) ≥ HPV(n) + k + 1`. -/
theorem criterion (n : ℕ) (hn : 5 ≤ n) (k : ℕ)
    (hk : (2 * k * (n - 1) + 1) * (n - 2) + k * (n - 1) < (n - 2).factorial + k) :
    HPV n + k + 1 ≤ Lam n := by
  by_contra hcon
  push_neg at hcon
  have hne : {m | ∃ W : Walk n, W.Covering ∧ W.len = m}.Nonempty := by
    obtain ⟨W, hW⟩ := covering_walk_exists n
    exact ⟨W.len, W, hW, rfl⟩
  obtain ⟨W, hWcov, hWlen⟩ := Nat.sInf_mem hne
  have hlen : W.len ≤ HPV n + k := by
    change W.len = Lam n at hWlen
    omega
  have hid := excess_identity W hWcov
  have hre := eStat_nonneg (by omega) W hWcov
  have hrr := rStat_nonneg W hWcov
  have hrl := ellStat_nonneg W hWcov
  have he0 : W.eStat = (W.eStat.toNat : ℤ) := (Int.toNat_of_nonneg hre).symm
  have hl0 : W.ellStat = (W.ellStat.toNat : ℤ) := (Int.toNat_of_nonneg hrl).symm
  have hsum : W.eStat.toNat + W.ellStat.toNat ≤ k := by
    have hcast : (W.len : ℤ) ≤ (HPV n : ℤ) + (k : ℤ) := by exact_mod_cast hlen
    rw [hid] at hcast
    omega
  have hv : W.vStat = (n - 2).factorial + W.ellStat.toNat := by
    have hdef : W.ellStat = (W.vStat : ℤ) - ((n - 2).factorial : ℤ) := rfl
    have hvge := covering_loops_lower W hWcov
    omega
  have h12 := corner_reduction n hn k W.eStat.toNat W.ellStat.toNat hk hsum
  exact twoparam n hn W.eStat.toNat W.ellStat.toNat h12 ⟨W, hWcov, he0, hv⟩

/-- **Lemma [lem:solve] (Solving the criterion)**: for `n ≥ 5` and `k ≥ 0`, the
criterion holds iff `k(2n−1) < (n−3)! − 1`, iff `k < ⌈((n−3)!−1)/(2n−1)⌉`. -/
theorem solve_criterion (n : ℕ) (hn : 5 ≤ n) (k : ℕ) :
    ((2 * k * (n - 1) + 1) * (n - 2) + k * (n - 1) < (n - 2).factorial + k ↔
      k * (2 * n - 1) < (n - 3).factorial - 1) ∧
    (k * (2 * n - 1) < (n - 3).factorial - 1 ↔
      k < ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
  have e1 : 5 + m - 1 = m + 4 := by omega
  have e2 : 5 + m - 2 = m + 3 := by omega
  have e3 : 5 + m - 3 = m + 2 := by omega
  have e4 : 2 * (5 + m) - 1 = 2 * m + 9 := by omega
  rw [e1, e2, e3, e4]
  have hfac : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
  have hF : 1 ≤ (m + 2).factorial := (m + 2).factorial_pos
  constructor
  · -- (i): the criterion ⟺ k(2n−1) < (n−3)! − 1
    rw [hfac]
    have key : (2 * k * (m + 4) + 1) * (m + 3) + k * (m + 4)
        = (m + 3) * (k * (2 * m + 9) + 1) + k := by ring
    rw [key]
    generalize (m + 2).factorial = F at hF
    generalize k * (2 * m + 9) = K
    constructor
    · intro h
      have h1 : (m + 3) * (K + 1) < (m + 3) * F := Nat.lt_of_add_lt_add_right h
      have h2 : K + 1 < F := lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
      omega
    · intro h
      have h2 : K + 1 < F := by omega
      have h1 : (m + 3) * (K + 1) < (m + 3) * F :=
        mul_lt_mul_of_pos_left h2 (by omega)
      exact Nat.add_lt_add_right h1 k
  · -- (ii): k(2n−1) < (n−3)! − 1 ⟺ k < the ceiling
    exact (lt_ceilDiv_iff (by omega)).symm

/-- **Theorem [thm:solved] (The criterion, solved)**: for all `n ≥ 5`,
`Λ(n) ≥ HPV(n) + ⌈((n−3)!−1)/(2n−1)⌉`, hence the same for `S(n)`. -/
theorem solved (n : ℕ) (hn : 5 ≤ n) :
    HPV n + ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) ≤ Lam n ∧
    HPV n + ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) ≤ S n := by
  have hκ : 1 ≤ ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) := by
    have h2 : 2 ≤ (n - 3).factorial := by
      calc 2 = Nat.factorial 2 := rfl
        _ ≤ (n - 3).factorial := Nat.factorial_le (by omega)
    have := (lt_ceilDiv_iff (a := (n - 3).factorial - 1) (b := 2 * n - 1) (k := 0)
      (by omega)).mpr (by omega)
    omega
  have hcrit : (2 * (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) - 1) * (n - 1) + 1) * (n - 2)
      + (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) - 1) * (n - 1) <
      (n - 2).factorial + (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) - 1) := by
    have hs := solve_criterion n hn (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) - 1)
    exact hs.1.mpr (hs.2.mpr (by omega))
  have hcr := criterion n hn _ hcrit
  have hlam : HPV n + ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) ≤ Lam n := by
    have : HPV n + (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) - 1) + 1
        = HPV n + ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) := by omega
    omega
  exact ⟨hlam, hlam.trans (lam_le_S n)⟩

/-- **Theorem [thm:solved]**, "moreover the ceiling is exact": the criterion fails at
`k = ⌈((n−3)!−1)/(2n−1)⌉`, so no larger bound is an instance of
Theorem [thm:criterion]. -/
theorem solved_exact (n : ℕ) (hn : 5 ≤ n) :
    ¬ ((2 * (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1)) * (n - 1) + 1) * (n - 2) +
        (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1)) * (n - 1) <
      (n - 2).factorial + ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1)) := by
  intro hcrit
  have h1 := (solve_criterion n hn (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1))).1.mp hcrit
  have h2 := (solve_criterion n hn (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1))).2.mp h1
  exact lt_irrefl _ h2

/-- **Corollary [cor:pointvalues] (Point values)**: the walk-model point values
`Λ(5) ≥ HPV(5)+1`, …, `Λ(11) ≥ HPV(11)+1920`. -/
theorem pointvalues :
    HPV 5 + 1 ≤ Lam 5 ∧ HPV 6 + 1 ≤ Lam 6 ∧ HPV 7 + 2 ≤ Lam 7 ∧
    HPV 8 + 8 ≤ Lam 8 ∧ HPV 9 + 43 ≤ Lam 9 ∧ HPV 10 + 266 ≤ Lam 10 ∧
    HPV 11 + 1920 ≤ Lam 11 :=
  ⟨criterion 5 (by norm_num) 0 (by decide), criterion 6 (by norm_num) 0 (by decide),
    criterion 7 (by norm_num) 1 (by decide), criterion 8 (by norm_num) 7 (by decide),
    criterion 9 (by norm_num) 42 (by decide), criterion 10 (by norm_num) 265 (by decide),
    criterion 11 (by norm_num) 1919 (by decide)⟩

/-! ## §7 The closed form -/

/-- **Lemma [lem:third] (display (14))**: the uniform certificate
`⌈(n−4)!/3⌉ ≤ ⌈((n−3)!−1)/(2n−1)⌉` for all `n ≥ 5`.  Equality holds at `n = 5, 6, 7, 8`
(both sides `1, 1, 2, 8`), exercised in the proof's base cases. -/
theorem uniform_certificate (n : ℕ) (hn : 5 ≤ n) :
    (n - 4).factorial ⌈/⌉ 3 ≤ ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) := by
  rcases Nat.lt_or_ge n 9 with h9 | h9
  · -- base cases `n = 5, 6, 7, 8`: both sides evaluate to `1, 1, 2, 8`
    have hc : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> decide
  · -- `n ≥ 9`: ceiling monotonicity reduces to `(2n−1)·(n−4)! ≤ 3·((n−3)!−1)`,
    -- i.e. `(n−4)!·(n−8) ≥ 3`, from `(n−4)! ≥ 120` and `n − 8 ≥ 1`
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have e3 : m + 9 - 3 = m + 6 := by omega
    have e4 : m + 9 - 4 = m + 5 := by omega
    have eb : 2 * (m + 9) - 1 = 2 * m + 17 := by omega
    rw [e3, e4, eb]
    have h120 : 120 ≤ (m + 5).factorial :=
      calc (120 : ℕ) = Nat.factorial 5 := rfl
        _ ≤ (m + 5).factorial := Nat.factorial_le (by omega)
    have h6 : (m + 6).factorial = (m + 6) * (m + 5).factorial := Nat.factorial_succ (m + 5)
    -- the right ceiling is large: `(m+6)! − 1 ≤ ⌈((m+6)!−1)/(2m+17)⌉·(2m+17)`
    have hlow : (m + 6).factorial - 1 ≤
        (((m + 6).factorial - 1) ⌈/⌉ (2 * m + 17)) * (2 * m + 17) :=
      Nat.not_lt.mp fun hcon => lt_irrefl _ ((lt_ceilDiv_iff (by omega)).mpr hcon)
    have hmain : (m + 5).factorial * (2 * m + 17) ≤ 3 * ((m + 6).factorial - 1) := by
      have hB : 3 ≤ (m + 1) * (m + 5).factorial :=
        le_trans (by omega) (Nat.le_mul_of_pos_left _ (show 0 < m + 1 by omega))
      have key : (m + 5).factorial * (2 * m + 17) + (m + 1) * (m + 5).factorial
          = 3 * ((m + 6) * (m + 5).factorial) := by ring
      rw [h6]
      generalize hA : (m + 5).factorial * (2 * m + 17) = A at key ⊢
      generalize hBv : (m + 1) * (m + 5).factorial = B at key hB
      generalize hC : (m + 6) * (m + 5).factorial = C at key ⊢
      omega
    rw [ceilDiv_le_iff_le_mul (show (0 : ℕ) < 3 by norm_num)]
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 2 * m + 17 by omega)
    calc (m + 5).factorial * (2 * m + 17)
        ≤ 3 * ((m + 6).factorial - 1) := hmain
      _ ≤ 3 * ((((m + 6).factorial - 1) ⌈/⌉ (2 * m + 17)) * (2 * m + 17)) :=
          Nat.mul_le_mul le_rfl hlow
      _ = 3 * (((m + 6).factorial - 1) ⌈/⌉ (2 * m + 17)) * (2 * m + 17) := by ring

/-- **Corollary [cor:third] (Uniform factorial form)** — also the uniform clause of
Theorem [thm:intromain]: `Λ(n) ≥ HPV(n) + ⌈(n−4)!/3⌉` and `S(n) ≥ HPV(n) + ⌈(n−4)!/3⌉`
for all `n ≥ 5`. -/
theorem uniform_form (n : ℕ) (hn : 5 ≤ n) :
    HPV n + (n - 4).factorial ⌈/⌉ 3 ≤ Lam n ∧
    HPV n + (n - 4).factorial ⌈/⌉ 3 ≤ S n :=
  ⟨(Nat.add_le_add_left (uniform_certificate n hn) (HPV n)).trans (solved n hn).1,
    (Nat.add_le_add_left (uniform_certificate n hn) (HPV n)).trans (solved n hn).2⟩

/-- **Corollary [cor:words]**, criterion transfer: the reduction `S(n) ≥ Λ(n)`
transfers Theorem [thm:criterion] verbatim to `S(n)`. -/
theorem words_criterion (n : ℕ) (hn : 5 ≤ n) (k : ℕ)
    (hk : (2 * k * (n - 1) + 1) * (n - 2) + k * (n - 1) < (n - 2).factorial + k) :
    HPV n + k + 1 ≤ S n :=
  (criterion n hn k hk).trans (lam_le_S n)

/-- **Corollary [cor:words]**, the numeric point values: `S(5) ≥ 153`, `S(6) ≥ 868`,
`S(7) ≥ 5886`, `S(8) ≥ 46093`, `S(9) ≥ 408289`, `S(10) ≥ 4032273`,
`S(11) ≥ 43910408`. -/
theorem words_pointvalues :
    153 ≤ S 5 ∧ 868 ≤ S 6 ∧ 5886 ≤ S 7 ∧ 46093 ≤ S 8 ∧
    408289 ≤ S 9 ∧ 4032273 ≤ S 10 ∧ 43910408 ≤ S 11 := by
  obtain ⟨h5, h6, h7, h8, h9, h10, h11⟩ := pointvalues
  have l5 := lam_le_S 5
  have l6 := lam_le_S 6
  have l7 := lam_le_S 7
  have l8 := lam_le_S 8
  have l9 := lam_le_S 9
  have l10 := lam_le_S 10
  have l11 := lam_le_S 11
  have e5 : HPV 5 + 1 = 153 := by simp [HPV, Nat.factorial]
  have e6 : HPV 6 + 1 = 868 := by simp [HPV, Nat.factorial]
  have e7 : HPV 7 + 2 = 5886 := by simp [HPV, Nat.factorial]
  have e8 : HPV 8 + 8 = 46093 := by simp [HPV, Nat.factorial]
  have e9 : HPV 9 + 43 = 408289 := by simp [HPV, Nat.factorial]
  have e10 : HPV 10 + 266 = 4032273 := by simp [HPV, Nat.factorial]
  have e11 : HPV 11 + 1920 = 43910408 := by simp [HPV, Nat.factorial]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **Remark [rem:half] (display (15))**: the coefficient cannot reach one half —
`2·⌈((n−3)!−1)/(2n−1)⌉ < (n−4)!` for every `n ≥ 7`. -/
theorem half_wall (n : ℕ) (hn : 7 ≤ n) :
    2 * (((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1)) < (n - 4).factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have e3 : m + 7 - 3 = m + 4 := by omega
  have e4 : m + 7 - 4 = m + 3 := by omega
  have eb : 2 * (m + 7) - 1 = 2 * m + 13 := by omega
  rw [e3, e4, eb]
  have hpos : 1 ≤ (m + 4).factorial := (m + 4).factorial_pos
  -- ceiling upper bound: `⌈((m+4)!−1)/(2m+13)⌉·(2m+13) ≤ (m+4)! + 2m + 11`
  have hup : (((m + 4).factorial - 1) ⌈/⌉ (2 * m + 13)) * (2 * m + 13)
      ≤ (m + 4).factorial + 2 * m + 11 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    calc ((m + 4).factorial - 1 + (2 * m + 13) - 1) / (2 * m + 13) * (2 * m + 13)
        ≤ (m + 4).factorial - 1 + (2 * m + 13) - 1 := Nat.div_mul_le_self _ _
      _ = (m + 4).factorial + 2 * m + 11 := by omega
  -- factorial growth: `6(m+1) ≤ (m+3)!`
  have h3 : (m + 3).factorial = (m + 3) * ((m + 2) * ((m + 1) * m.factorial)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  have h6m : 6 * (m + 1) ≤ (m + 3).factorial := by
    rw [h3]
    calc 6 * (m + 1) = 3 * 2 * (m + 1) := by ring
      _ ≤ (m + 3) * (m + 2) * (m + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) le_rfl
      _ = (m + 3) * ((m + 2) * ((m + 1) * 1)) := by ring
      _ ≤ (m + 3) * ((m + 2) * ((m + 1) * m.factorial)) :=
          Nat.mul_le_mul le_rfl
            (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl m.factorial_pos))
  have h4 : (m + 4).factorial = (m + 4) * (m + 3).factorial := Nat.factorial_succ (m + 3)
  -- multiply the target by `2m+13` and compare: `2(m+4)! + 4m + 22 < (2m+13)(m+3)!`,
  -- i.e. `5(m+3)! > 4m + 22`
  have hmul : 2 * (((m + 4).factorial - 1) ⌈/⌉ (2 * m + 13)) * (2 * m + 13)
      < (m + 3).factorial * (2 * m + 13) := by
    have key : (m + 3).factorial * (2 * m + 13)
        = 2 * ((m + 4) * (m + 3).factorial) + 5 * (m + 3).factorial := by ring
    calc 2 * (((m + 4).factorial - 1) ⌈/⌉ (2 * m + 13)) * (2 * m + 13)
        = 2 * ((((m + 4).factorial - 1) ⌈/⌉ (2 * m + 13)) * (2 * m + 13)) := by ring
      _ ≤ 2 * ((m + 4).factorial + 2 * m + 11) := Nat.mul_le_mul le_rfl hup
      _ < (m + 3).factorial * (2 * m + 13) := by
          rw [h4, key]
          generalize hA : (m + 4) * (m + 3).factorial = A
          generalize hG : (m + 3).factorial = G at h6m ⊢
          omega
  exact lt_of_mul_lt_mul_right hmul (Nat.zero_le _)

/-! ## §4/§5 ride facts (prose, used by Lemma [lem:cornerexit])

The paper's §4 computation of the canonical ride: the `h`-th orbit of the ride is
anchored at `u^{(h)}α`, the `n−1` orbits are pairwise distinct, the last vertex of the
last orbit is the corner `αβγr`, and the canonical cross-loop exit from the corner is a
proper weight-3 edge landing at `M(x)`. -/

/-- Prose fact (§4): the ride anchors are `R_{h,0} = u^{(h)}α`.  (Stated for `n ≥ 2`, sharper
than the paper's standing `n ≥ 4`.) -/
theorem rideAnchor_eq (n : ℕ) (hn : 2 ≤ n) (x : List ℕ) (hx : IsPermWord n x)
    (h : ℕ) (hh : h ≤ n - 2) :
    rideAnchor n x h = ((x.erase (x.getLastD 0)).rotate h) ++ [x.getLastD 0] :=
  rideAnchor_eq_all hn hx h

/-- Prose fact (§4): the `n−1` ride orbits are pairwise distinct (each contains
exactly one `α`-last vertex, its anchor). -/
theorem ride_orbits_distinct (n : ℕ) (hn : 2 ≤ n) (x : List ℕ) (hx : IsPermWord n x)
    (h h' : ℕ) (hh : h < n - 1) (hh' : h' < n - 1) (hne : h ≠ h') :
    rotClass (rideAnchor n x h) ≠ rotClass (rideAnchor n x h') := by
  intro hcon
  obtain ⟨l, a, rfl⟩ : ∃ l a, x = l ++ [a] := by
    rcases List.eq_nil_or_concat x with h0 | ⟨l, a, h0⟩
    · exact absurd h0 (hx.ne_nil (by omega))
    · exact ⟨l, a, by rw [h0, List.concat_eq_append]⟩
  have herase : (l ++ [a]).erase ((l ++ [a]).getLastD 0) = l := by
    rw [erase_getLastD hx.nodup, List.dropLast_concat]
  rw [rideAnchor_eq_all hn hx h, rideAnchor_eq_all hn hx h', herase,
    List.getLastD_concat] at hcon
  have hllen : l.length = n - 1 := by
    have := hx.length
    simp at this
    omega
  have hnd := hx.nodup
  rw [List.nodup_append] at hnd
  have hal : a ∉ l := fun ha => hnd.2.2 a ha a (List.mem_singleton_self a) rfl
  have hndrot : (l.rotate h ++ [a]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.rotate_perm l h).nodup_iff.mpr hnd.1, List.nodup_singleton a, ?_⟩
    intro y hy z hz
    rw [List.mem_singleton] at hz
    subst hz
    intro hya
    exact hal ((List.rotate_perm l h).mem_iff.mp (hya ▸ hy))
  have heq : l.rotate h = l.rotate h' :=
    isRotated_concat_inj hndrot (rotClass_eq_iff.mp hcon)
  exact hne (rotate_injOn_lt hnd.1 (by omega) (by omega) heq)

/-- Prose fact (§4): the last vertex of the last orbit of the ride is the corner
`ρ^{n−1}(u^{(n−2)}α) = α β γ r`. -/
theorem ride_corner (n : ℕ) (hn : 3 ≤ n) (x : List ℕ) (hx : IsPermWord n x) :
    ride n x (n - 2) (n - 1) =
      x.getLastD 0 :: (x.erase (x.getLastD 0)).rotate (n - 2) := by
  rw [ride, rideAnchor_eq_all (by omega) hx (n - 2),
    rotate_last _ _ (by rw [List.length_rotate, erase_getLastD hx.nodup,
      List.length_dropLast, hx.length])]

/-- Prose fact (§4): the canonical cross-loop exit from the corner is the proper edge
of weight 3 landing at `M(x) = rγβα`. -/
theorem msucc_edge (n : ℕ) (hn : 4 ≤ n) (x : List ℕ) (hx : IsPermWord n x) :
    wt n (ride n x (n - 2) (n - 1)) (Msucc n x) = 3 ∧
      ProperStep n (ride n x (n - 2) (n - 1)) (Msucc n x) := by
  -- the corner in word form: `A β γ r` with `A` the marker
  have hcw : ride n x (n - 2) (n - 1) =
      x.getLastD 0 :: (x.erase (x.getLastD 0)).rotate (n - 2) :=
    ride_corner n (by omega) x hx
  obtain ⟨A, hA⟩ : ∃ A, x.getLastD 0 = A := ⟨_, rfl⟩
  obtain ⟨β, γ, r, hur⟩ : ∃ β γ r,
      (x.erase (x.getLastD 0)).rotate (n - 2) = β :: γ :: r := by
    have hlen : ((x.erase (x.getLastD 0)).rotate (n - 2)).length = n - 1 := by
      rw [List.length_rotate, erase_getLastD hx.nodup, List.length_dropLast, hx.length]
    rcases hu : (x.erase (x.getLastD 0)).rotate (n - 2) with _ | ⟨β, t⟩
    · rw [hu] at hlen
      simp at hlen
      omega
    · rcases t with _ | ⟨γ, r⟩
      · rw [hu] at hlen
        simp at hlen
        omega
      · exact ⟨β, γ, r, rfl⟩
  have hrlen : r.length = n - 3 := by
    have h := congrArg List.length hur
    rw [List.length_rotate, erase_getLastD hx.nodup, List.length_dropLast,
      hx.length] at h
    simp only [List.length_cons] at h
    omega
  -- the corner and the successor in split form
  have hcornerEq : ride n x (n - 2) (n - 1) = A :: β :: γ :: r := by
    rw [hcw, hur, hA]
  have hmsucc : Msucc n x = r ++ [γ, β, A] := by
    show ((x.erase (x.getLastD 0)).rotate (n - 2)).drop 2 ++
      [((x.erase (x.getLastD 0)).rotate (n - 2)).getD 1 0,
        ((x.erase (x.getLastD 0)).rotate (n - 2)).getD 0 0, x.getLastD 0] =
      r ++ [γ, β, A]
    rw [hur, hA]
    rfl
  -- both endpoints are permutation words
  have hridePerm : IsPermWord n (ride n x (n - 2) (n - 1)) :=
    isPermWord_ride (by omega) hx (n - 2) (n - 1)
  have hcornerPerm : IsPermWord n (A :: β :: γ :: r) := by
    rw [← hcornerEq]
    exact hridePerm
  have hmsuccPerm : IsPermWord n (r ++ [γ, β, A]) := by
    have s1 : (β :: A :: r) ~ (A :: β :: r) := List.Perm.swap A β r
    have s2 : (γ :: β :: A :: r) ~ (γ :: A :: β :: r) := s1.cons γ
    have s3 : (γ :: A :: β :: r) ~ (A :: γ :: β :: r) := List.Perm.swap A γ (β :: r)
    have s4 : (A :: γ :: β :: r) ~ (A :: β :: γ :: r) := (List.Perm.swap β γ r).cons A
    have hp : (r ++ [γ, β, A]) ~ (A :: β :: γ :: r) :=
      (List.perm_append_comm (l₁ := r) (l₂ := [γ, β, A])).trans
        (s2.trans (s3.trans s4))
    exact isPermWord_iff_perm_refList.mpr
      (hp.trans (isPermWord_iff_perm_refList.mp hcornerPerm))
  -- distinctness of the corner symbols
  have hnd := hcornerPerm.nodup
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have hAmem := hnd1.1
  simp only [List.mem_cons, not_or] at hAmem
  obtain ⟨hAβ, hAγ, hAr⟩ := hAmem
  have hβmem := hnd2.1
  simp only [List.mem_cons, not_or] at hβmem
  obtain ⟨hβγ, hβr⟩ := hβmem
  have hγr := hnd3.1
  -- `r` is nonempty: this is exactly where `n ≥ 4` is needed
  obtain ⟨c, r', rfl⟩ : ∃ c r', r = c :: r' :=
    List.exists_cons_of_ne_nil (by
      intro h0
      rw [h0] at hrlen
      simp at hrlen
      omega)
  -- weight at most 3: the `d = 3` overlap witness (the shared block is `r`)
  have hwtle : wt n (ride n x (n - 2) (n - 1)) (Msucc n x) ≤ 3 := by
    refine wt_le (by omega) (by omega) ?_
    rw [hcornerEq, hmsucc, List.take_left' hrlen]
    rfl
  have hspec := wt_spec (u := ride n x (n - 2) (n - 1)) (v := Msucc n x)
    (show (1 : ℕ) ≤ n by omega) (by rw [hcornerEq]; exact le_of_eq hcornerPerm.length)
  -- weight ≠ 1: `d = 1` would force `β γ r = r γ β`, so `β = r₁`, against distinctness
  have hne1 : wt n (ride n x (n - 2) (n - 1)) (Msucc n x) ≠ 1 := by
    intro hw1
    have hover := hspec.2.2
    rw [hw1, hcornerEq, hmsucc] at hover
    have htake : ((c :: r') ++ [γ, β, A]).take (n - 1) = c :: (r' ++ [γ, β]) := by
      rw [List.take_append, List.take_of_length_le (by rw [hrlen]; omega), hrlen,
        show n - 1 - (n - 3) = 2 by omega]
      rfl
    rw [htake] at hover
    have hover' : β :: γ :: c :: r' = c :: (r' ++ [γ, β]) := hover
    injection hover' with hbc _htail
    exact hβr (by rw [hbc]; exact List.mem_cons_self)
  -- weight ≠ 2: `d = 2` would force `γ r = r γ`, so `γ = r₁` (this fails at `n = 3`)
  have hne2 : wt n (ride n x (n - 2) (n - 1)) (Msucc n x) ≠ 2 := by
    intro hw2
    have hover := hspec.2.2
    rw [hw2, hcornerEq, hmsucc] at hover
    have htake : ((c :: r') ++ [γ, β, A]).take (n - 2) = c :: (r' ++ [γ]) := by
      rw [List.take_append, List.take_of_length_le (by rw [hrlen]; omega), hrlen,
        show n - 2 - (n - 3) = 1 by omega]
      rfl
    rw [htake] at hover
    have hover' : γ :: c :: r' = c :: (r' ++ [γ]) := hover
    injection hover' with hgc _htail
    exact hγr (by rw [hgc]; exact List.mem_cons_self)
  have hwt3 : wt n (ride n x (n - 2) (n - 1)) (Msucc n x) = 3 := by
    have h1 := hspec.1
    omega
  -- properness via the (prop) criterion: the tails `{γ} , {γ,β}` avoid `{A} , {A,β}`
  refine ⟨hwt3, ?_⟩
  have hmsuccPerm' : IsPermWord n (Msucc n x) := by
    rw [hmsucc]
    exact hmsuccPerm
  rw [properStep_iff_prop n _ _ hridePerm hmsuccPerm']
  intro h hh1 hh2
  rw [hwt3] at hh2
  rw [hwt3, hmsucc, hcornerEq]
  have hdropm : (((c :: r') ++ [γ, β, A])).drop (n - 3) = [γ, β, A] := by
    rw [List.drop_append_of_le_length (le_of_eq hrlen.symm),
      List.drop_eq_nil_of_le (le_of_eq hrlen), List.nil_append]
  rw [hdropm]
  rcases (show h = 1 ∨ h = 2 by omega) with rfl | rfl
  · -- offset 1: `{γ} ≠ {A}` since `γ ≠ A`
    show (([γ] : List ℕ)).toFinset ≠ (([A] : List ℕ)).toFinset
    intro he
    have hmem : γ ∈ (([A] : List ℕ)).toFinset := by
      rw [← he]
      simp
    simp at hmem
    exact hAγ hmem.symm
  · -- offset 2: `{γ, β} ≠ {A, β}` since `γ ∉ {A, β}`
    show (([γ, β] : List ℕ)).toFinset ≠ (([A, β] : List ℕ)).toFinset
    intro he
    have hmem : γ ∈ (([A, β] : List ℕ)).toFinset := by
      rw [← he]
      simp
    simp at hmem
    rcases hmem with h | h
    · exact hAγ h.symm
    · exact hβγ h.symm

/-! ## §1 Introduction — Theorem [thm:intromain]

Stated here (after §6–§7) because the proofs consume the later results; in the paper
this is Theorem 1. -/

/-- **Theorem [thm:intromain] (main theorem)**, first three clauses: the solved ceiling
bound for `S(n)`; the criterion instance (for every `k ≥ 0` satisfying the criterion,
`S(n) ≥ HPV(n) + k + 1`); and the exact solution of the criterion
(`criterion ⟺ k(2n−1) < (n−3)!−1 ⟺ k < ⌈((n−3)!−1)/(2n−1)⌉`). -/
theorem intromain (n : ℕ) (hn : 5 ≤ n) :
    HPV n + ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1) ≤ S n ∧
    (∀ k : ℕ, (2 * k * (n - 1) + 1) * (n - 2) + k * (n - 1) < (n - 2).factorial + k →
      HPV n + k + 1 ≤ S n) ∧
    (∀ k : ℕ,
      ((2 * k * (n - 1) + 1) * (n - 2) + k * (n - 1) < (n - 2).factorial + k ↔
        k * (2 * n - 1) < (n - 3).factorial - 1) ∧
      (k * (2 * n - 1) < (n - 3).factorial - 1 ↔
        k < ((n - 3).factorial - 1) ⌈/⌉ (2 * n - 1))) :=
  ⟨(solved n hn).2, fun k hk => words_criterion n hn k hk,
    fun k => solve_criterion n hn k⟩

/-- **Theorem [thm:intromain]**, the displayed point values
`S(5) ≥ HPV(5)+1 = 153`, …, `S(11) ≥ HPV(11)+1920`. -/
theorem intromain_points :
    HPV 5 + 1 ≤ S 5 ∧ HPV 6 + 1 ≤ S 6 ∧ HPV 7 + 2 ≤ S 7 ∧ HPV 8 + 8 ≤ S 8 ∧
    HPV 9 + 43 ≤ S 9 ∧ HPV 10 + 266 ≤ S 10 ∧ HPV 11 + 1920 ≤ S 11 := by
  obtain ⟨h5, h6, h7, h8, h9, h10, h11⟩ := pointvalues
  exact ⟨h5.trans (lam_le_S 5), h6.trans (lam_le_S 6), h7.trans (lam_le_S 7),
    h8.trans (lam_le_S 8), h9.trans (lam_le_S 9), h10.trans (lam_le_S 10),
    h11.trans (lam_le_S 11)⟩

end Coeff2
