/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Helpers

/-!
# Port-campaign helpers (not statements of the paper)

Additional infrastructure for the proofs in `Coeff2/Statements.lean`.  Contents:

* walk-chain extraction (`Walk.properStep`);
* the per-edge increment lemmas for `p` and `v` (the `c` case is
  `increment_of_c` in `Coeff2/Statements.lean`);
* the weight-2 word dichotomy (`wt_two_cases`) and the improperness of the
  double rotation;
* the per-edge defect bound `defect_nonneg_of_pos` — the induction step of the
  HPV monovariant, proved for `1 ≤ n` (at `n = 0` the degenerate two-vertex walk over the
  empty alphabet has a negative defect, so the hypothesis is necessary).
-/

namespace Coeff2

open List

variable {n : ℕ}

/-! ## Walk-chain extraction -/

/-- Consecutive vertices of a walk are joined by proper edges. -/
theorem Walk.properStep {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    ProperStep n (W.vert i) (W.vert (i + 1)) := by
  have h := W.chain.getElem i hi
  rwa [W.vert_eq_getElem (by omega), W.vert_eq_getElem hi]

/-! ## Membership in prefix walks -/

theorem Walk.mem_pre_verts {W : Walk n} {w : List ℕ} {t : ℕ} :
    w ∈ (W.pre t).verts ↔ ∃ s ≤ t, s < W.numVerts ∧ W.vert s = w := by
  show w ∈ W.verts.take (t + 1) ↔ _
  rw [W.mem_take_vert]
  constructor
  · rintro ⟨s, hs1, hs2, hs3⟩; exact ⟨s, by omega, hs2, hs3⟩
  · rintro ⟨s, hs1, hs2, hs3⟩; exact ⟨s, by omega, hs2, hs3⟩

theorem Walk.pStat_set_pre {W : Walk n} (t : ℕ) :
    {w | w ∈ (W.pre t).verts} = {w | ∃ s ≤ t, s < W.numVerts ∧ W.vert s = w} := by
  ext w; exact W.mem_pre_verts

/-- The visited-vertex set of the one-longer prefix: insert the new vertex. -/
theorem Walk.pre_succ_vertSet {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    {w | w ∈ (W.pre (i + 1)).verts} = insert (W.vert (i + 1)) {w | w ∈ (W.pre i).verts} := by
  rw [W.pStat_set_pre, W.pStat_set_pre]
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨s, hs1, hs2, rfl⟩
    rcases Nat.lt_or_eq_of_le hs1 with h | h
    · exact Or.inr ⟨s, by omega, hs2, rfl⟩
    · subst h; exact Or.inl rfl
  · rintro (rfl | ⟨s, hs1, hs2, rfl⟩)
    · exact ⟨i + 1, le_refl _, hi, rfl⟩
    · exact ⟨s, by omega, hs2, rfl⟩

theorem Walk.pre_vertSet_finite (W : Walk n) (t : ℕ) :
    {w | w ∈ (W.pre t).verts}.Finite := (W.pre t).verts.finite_toSet

/-! ## The `p` increment -/

/-- `Δp ∈ {0,1}`, and `Δp = 0` exactly when the target was already visited. -/
theorem Walk.dp_cases {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    (W.dp i = 0 ∧ ∃ s ≤ i, W.vert s = W.vert (i + 1)) ∨
      (W.dp i = 1 ∧ ∀ s ≤ i, W.vert s ≠ W.vert (i + 1)) := by
  have hfin := W.pre_vertSet_finite i
  have hins := W.pre_succ_vertSet hi
  have hp1 : (W.pre (i + 1)).pStat = {w | w ∈ (W.pre (i + 1)).verts}.ncard := rfl
  have hp0 : (W.pre i).pStat = {w | w ∈ (W.pre i).verts}.ncard := rfl
  by_cases hmem : W.vert (i + 1) ∈ {w | w ∈ (W.pre i).verts}
  · left
    have hcard : (W.pre (i + 1)).pStat = (W.pre i).pStat := by
      rw [hp1, hp0, hins, Set.ncard_insert_of_mem hmem]
    obtain ⟨s, hs1, _, hs3⟩ := W.mem_pre_verts.mp hmem
    refine ⟨by unfold Walk.dp; omega, s, hs1, hs3⟩
  · right
    have hcard : (W.pre (i + 1)).pStat = (W.pre i).pStat + 1 := by
      rw [hp1, hp0, hins, Set.ncard_insert_of_notMem hmem hfin]
    refine ⟨by unfold Walk.dp; omega, fun s hs hcon => hmem ?_⟩
    exact W.mem_pre_verts.mpr ⟨s, hs, by omega, hcon⟩

theorem Walk.dp_nonneg {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) : 0 ≤ W.dp i := by
  rcases W.dp_cases hi with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem Walk.dp_le_one {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) : W.dp i ≤ 1 := by
  rcases W.dp_cases hi with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- `Δp = 0` given an earlier occurrence of the target. -/
theorem Walk.dp_eq_zero {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts)
    {s : ℕ} (hs : s ≤ i) (hv : W.vert s = W.vert (i + 1)) : W.dp i = 0 := by
  rcases W.dp_cases hi with ⟨h, -⟩ | ⟨-, hnone⟩
  · exact h
  · exact absurd hv (hnone s hs)

/-! ## The `v` increment -/

/-- The entered-loop set of a prefix walk. -/
theorem Walk.entered_pre {W : Walk n} {t : ℕ} (ht : t < W.numVerts) (L : MarkedLoop) :
    (W.pre t).Entered L ↔ ∃ s ≤ t, W.activeLoop s = L := by
  unfold Walk.Entered
  rw [W.pre_numVerts]
  constructor
  · rintro ⟨s, hs1, hs2⟩
    have hst : s ≤ t := by omega
    exact ⟨s, hst, by rw [← W.activeLoop_pre t s hst]; exact hs2⟩
  · rintro ⟨s, hs1, hs2⟩
    exact ⟨s, by omega, by rw [W.activeLoop_pre t s hs1]; exact hs2⟩

/-- The entered-loop set of the one-longer prefix: insert the new active loop. -/
theorem Walk.pre_succ_enteredSet {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    {L | (W.pre (i + 1)).Entered L} =
      insert (W.activeLoop (i + 1)) {L | (W.pre i).Entered L} := by
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
    W.entered_pre hi, W.entered_pre (by omega : i < W.numVerts)]
  constructor
  · rintro ⟨s, hs1, rfl⟩
    rcases Nat.lt_or_eq_of_le hs1 with h | h
    · exact Or.inr ⟨s, by omega, rfl⟩
    · subst h; exact Or.inl rfl
  · rintro (rfl | ⟨s, hs1, rfl⟩)
    · exact ⟨i + 1, le_refl _, rfl⟩
    · exact ⟨s, by omega, rfl⟩

theorem Walk.entered_pre_finite (W : Walk n) (t : ℕ) :
    {L | (W.pre t).Entered L}.Finite := (W.pre t).entered_finite

/-- `Δv ∈ {0,1}`; `Δv = 0` exactly when the loop active after the edge was already
active at some time `≤ i`. -/
theorem Walk.dv_cases {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    (W.dv i = 0 ∧ ∃ s ≤ i, W.activeLoop s = W.activeLoop (i + 1)) ∨
      (W.dv i = 1 ∧ ∀ s ≤ i, W.activeLoop s ≠ W.activeLoop (i + 1)) := by
  have hfin := W.entered_pre_finite i
  have hins := W.pre_succ_enteredSet hi
  have hv1 : (W.pre (i + 1)).vStat = {L | (W.pre (i + 1)).Entered L}.ncard := rfl
  have hv0 : (W.pre i).vStat = {L | (W.pre i).Entered L}.ncard := rfl
  by_cases hmem : W.activeLoop (i + 1) ∈ {L | (W.pre i).Entered L}
  · left
    have hcard : (W.pre (i + 1)).vStat = (W.pre i).vStat := by
      rw [hv1, hv0, hins, Set.ncard_insert_of_mem hmem]
    obtain ⟨s, hs1, hs2⟩ := (W.entered_pre (by omega : i < W.numVerts) _).mp hmem
    refine ⟨by unfold Walk.dv; omega, s, hs1, hs2⟩
  · right
    have hcard : (W.pre (i + 1)).vStat = (W.pre i).vStat + 1 := by
      rw [hv1, hv0, hins, Set.ncard_insert_of_notMem hmem hfin]
    refine ⟨by unfold Walk.dv; omega, fun s hs hcon => hmem ?_⟩
    exact (W.entered_pre (by omega : i < W.numVerts) _).mpr ⟨s, hs, hcon⟩

theorem Walk.dv_nonneg {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) : 0 ≤ W.dv i := by
  rcases W.dv_cases hi with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem Walk.dv_le_one {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) : W.dv i ≤ 1 := by
  rcases W.dv_cases hi with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- Across a weight-1 (rotation) edge, the active loop does not change, so `Δv = 0`. -/
theorem Walk.dv_eq_zero_of_wt_one {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts)
    (hw : wt n (W.vert i) (W.vert (i + 1)) < 2) : W.dv i = 0 := by
  have hact : W.activeLoop (i + 1) = W.activeLoop i := by
    show (if 2 ≤ wt n (W.vert i) (W.vert (i + 1)) then genLoop (W.vert (i + 1))
      else W.activeLoop i) = W.activeLoop i
    rw [if_neg (by omega)]
  rcases W.dv_cases hi with ⟨h, -⟩ | ⟨-, hnone⟩
  · exact h
  · exact absurd hact.symm (hnone i (le_refl i))

/-- Across a nonrotation edge (weight `≥ 2`), the activated loop is the loop of the
landing vertex. -/
theorem Walk.activeLoop_of_two_le_wt {W : Walk n} {i : ℕ}
    (hw : 2 ≤ wt n (W.vert i) (W.vert (i + 1))) :
    W.activeLoop (i + 1) = genLoop (W.vert (i + 1)) := by
  show (if 2 ≤ wt n (W.vert i) (W.vert (i + 1)) then genLoop (W.vert (i + 1))
    else W.activeLoop i) = _
  rw [if_pos hw]

/-! ## The `c` increment: convenience corollaries of `increment_of_c`
(stated there; the bounds are re-derived here from the prefix sets directly, so that
this file does not depend on `Coeff2/Statements.lean`). -/

theorem Walk.completed_pre_mono {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    {O | (W.pre i).Completed O} ⊆ {O | (W.pre (i + 1)).Completed O} := by
  intro O hO
  rw [Set.mem_setOf_eq, W.completed_pre_iff hi]
  rw [Set.mem_setOf_eq, W.completed_pre_iff (by omega : i < W.numVerts)] at hO
  intro w hw
  have := hO w hw
  rw [W.take_succ_vert (by omega : i < W.numVerts), List.mem_append]
  exact Or.inl this

theorem Walk.completed_pre_succ_subset {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) :
    {O | (W.pre (i + 1)).Completed O} ⊆
      insert (rotClass (W.vert i)) {O | (W.pre i).Completed O} := by
  intro O hO
  rw [Set.mem_insert_iff]
  by_cases hO' : O = rotClass (W.vert i)
  · exact Or.inl hO'
  · right
    rw [Set.mem_setOf_eq, W.completed_pre_iff hi] at hO
    rw [Set.mem_setOf_eq, W.completed_pre_iff (by omega : i < W.numVerts)]
    intro w hw
    have h2 := hO w hw
    rw [W.take_succ_vert (by omega : i < W.numVerts), List.mem_append] at h2
    rcases h2 with h2 | h2
    · exact h2
    · rw [List.mem_singleton] at h2
      subst h2
      exact absurd hw.symm hO'

theorem Walk.dc_nonneg {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) : 0 ≤ W.dc i := by
  have hmono := W.completed_pre_mono hi
  have hle : (W.pre i).cStat ≤ (W.pre (i + 1)).cStat :=
    Set.ncard_le_ncard hmono (W.pre (i + 1)).completed_finite
  unfold Walk.dc
  omega

theorem Walk.dc_le_one {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts) : W.dc i ≤ 1 := by
  have hsub := W.completed_pre_succ_subset hi
  have hle : (W.pre (i + 1)).cStat ≤ (W.pre i).cStat + 1 := by
    calc (W.pre (i + 1)).cStat
        ≤ (insert (rotClass (W.vert i)) {O | (W.pre i).Completed O}).ncard :=
          Set.ncard_le_ncard hsub (((W.pre i).completed_finite).insert _)
      _ ≤ (W.pre i).cStat + 1 := Set.ncard_insert_le _ _
  unfold Walk.dc
  omega

/-- If `Δc = 1`, position `i` is the first occurrence of `π_i` and every other member of
its cyclic class occurs strictly before `i` (the content of Lemma [lem:deltac], derived
here directly from the prefix sets). -/
theorem Walk.dc_eq_one_data {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts)
    (hdc : W.dc i = 1) :
    (∀ s < i, W.vert s ≠ W.vert i) ∧
      ∀ w, rotClass w = rotClass (W.vert i) → w ≠ W.vert i → ∃ s < i, W.vert s = w := by
  have hi0 : i < W.numVerts := by omega
  -- the class of the source is newly completed
  have hnew : (W.pre (i + 1)).Completed (rotClass (W.vert i)) ∧
      ¬ (W.pre i).Completed (rotClass (W.vert i)) := by
    by_contra hcon
    -- otherwise the completed sets coincide, contradicting `Δc = 1`
    have heq : {O | (W.pre (i + 1)).Completed O} = {O | (W.pre i).Completed O} := by
      apply Set.Subset.antisymm _ (W.completed_pre_mono hi)
      intro O hO
      by_cases hO' : O = rotClass (W.vert i)
      · subst hO'
        by_cases h0 : (W.pre i).Completed (rotClass (W.vert i))
        · exact h0
        · exact absurd ⟨hO, h0⟩ hcon
      · rcases W.completed_pre_succ_subset hi hO with h | h
        · exact absurd h hO'
        · exact h
    have : (W.pre (i + 1)).cStat = (W.pre i).cStat := by
      show {O | (W.pre (i + 1)).Completed O}.ncard = {O | (W.pre i).Completed O}.ncard
      rw [heq]
    unfold Walk.dc at hdc
    omega
  obtain ⟨h1, h0⟩ := hnew
  rw [W.completed_pre_iff hi] at h1
  rw [W.completed_pre_iff hi0] at h0
  constructor
  · intro s hs hcon
    apply h0
    intro w hw
    have h2 := h1 w hw
    rw [W.take_succ_vert hi0, List.mem_append] at h2
    rcases h2 with h2 | h2
    · exact h2
    · rw [List.mem_singleton] at h2
      subst h2
      exact W.mem_take_vert.mpr ⟨s, hs, by omega, hcon⟩
  · intro w hw hne
    have h2 := h1 w hw
    rw [W.take_succ_vert hi0, List.mem_append] at h2
    rcases h2 with h2 | h2
    · obtain ⟨s, hs1, _, hs3⟩ := W.mem_take_vert.mp h2
      exact ⟨s, hs1, hs3⟩
    · rw [List.mem_singleton] at h2
      exact absurd h2 hne

/-! ## Word facts: the rotation and the door -/

/-- For `n ≥ 2`, the rotation of a permutation word differs from the word (the head
moves). -/
theorem rho_ne_self {w : List ℕ} (hn : 2 ≤ n) (hw : IsPermWord n w) : rho w ≠ w := by
  intro hcon
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hw.ne_nil (by omega))
  have ht : t ≠ [] := by
    intro h0
    have := hw.length
    rw [h0] at this
    simp at this
    omega
  obtain ⟨b, t', rfl⟩ := List.exists_cons_of_ne_nil ht
  have h1 : rho (a :: b :: t') = b :: t' ++ [a] := by
    show (a :: b :: t').rotate 1 = _
    simp
  rw [h1] at hcon
  have hab : b = a := by
    have := congrArg (fun l => l.getD 0 0) hcon
    simpa using this
  have hnd := hw.nodup
  rw [hab] at hnd
  simp at hnd

/-- The weight-2 word dichotomy: if `u.drop 2 = v.take (n−2)` for permutation words,
then `v` is the double rotation or the door of `u`.  (Needs `2 ≤ n`.) -/
theorem wt_two_word_cases {u v : List ℕ} (hn : 2 ≤ n) (hu : IsPermWord n u)
    (hv : IsPermWord n v) (hover : u.drop 2 = v.take (n - 2)) :
    v = u.rotate 2 ∨ v = door u := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hu.ne_nil (by omega))
  obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
    rcases t with _ | ⟨b, s⟩
    · have := hu.length; simp at this; omega
    · exact ⟨b, s, rfl⟩
  have hulen : (a :: b :: s).length = n := hu.length
  have hslen : s.length = n - 2 := by simp at hulen; omega
  have hdrop : (a :: b :: s).drop 2 = s := rfl
  -- v = s ++ r with r of length 2
  set r := v.drop (n - 2) with hr
  have hvsplit : v = s ++ r := by
    conv_lhs => rw [← List.take_append_drop (n - 2) v]
    rw [← hover, hdrop]
  have hrlen : r.length = 2 := by
    rw [hr, List.length_drop, hv.length]
    omega
  have hnd : (a :: b :: s).Nodup := hu.nodup
  have has : a ∉ s := by
    have := (List.nodup_cons.mp hnd).1
    simp at this
    exact this.2
  have hbs : b ∉ s := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hab : a ≠ b := by
    have := (List.nodup_cons.mp hnd).1
    simp at this
    exact this.1
  -- a and b lie in r
  have hsymbols : v.toFinset = (a :: b :: s).toFinset := by
    rw [hv.toFinset_eq, hu.toFinset_eq]
  have hav : a ∈ v := by
    rw [← List.mem_toFinset, hsymbols]
    simp
  have hbv : b ∈ v := by
    rw [← List.mem_toFinset, hsymbols]
    simp
  have har : a ∈ r := by
    rw [hvsplit, List.mem_append] at hav
    rcases hav with h | h
    · exact absurd h has
    · exact h
  have hbr : b ∈ r := by
    rw [hvsplit, List.mem_append] at hbv
    rcases hbv with h | h
    · exact absurd h hbs
    · exact h
  obtain ⟨x, y, hxy⟩ : ∃ x y, r = [x, y] := by
    rcases r with _ | ⟨x, r'⟩
    · simp at hrlen
    · rcases r' with _ | ⟨y, r''⟩
      · simp at hrlen
      · rcases r'' with _ | _
        · exact ⟨x, y, rfl⟩
        · simp at hrlen
  rw [hxy] at har hbr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at har hbr
  have hrot : (a :: b :: s).rotate 2 = s ++ [a, b] := by
    rw [List.rotate_eq_drop_append_take
      (by simp only [List.length_cons]; omega : 2 ≤ (a :: b :: s).length)]
    rfl
  have hdoor : door (a :: b :: s) = s ++ [b, a] := by
    show (a :: b :: s).drop 2 ++ [(a :: b :: s).getD 1 0, (a :: b :: s).getD 0 0] = _
    rfl
  rcases har with rfl | rfl
  · rcases hbr with rfl | rfl
    · exact absurd rfl hab
    · left
      rw [hvsplit, hxy, hrot]
  · rcases hbr with rfl | rfl
    · right
      rw [hvsplit, hxy, hdoor]
    · exact absurd rfl hab.symm

/-- The double rotation at weight 2 is improper: the intermediate window at offset 1 is
the single rotation. -/
theorem improper_rotate_two {u : List ℕ} (hn : 2 ≤ n) (hu : IsPermWord n u)
    (hw : wt n u (u.rotate 2) = 2) : Improper n u (u.rotate 2) := by
  refine ⟨1, le_refl 1, by omega, ?_⟩
  have hulen : u.length = n := hu.length
  -- the overlap word is `u ++ u.take 2`
  have hover : overlapWord n u (u.rotate 2) = u ++ u.take 2 := by
    unfold overlapWord
    rw [hw]
    congr 1
    rw [List.rotate_eq_drop_append_take (by omega : 2 ≤ u.length),
      List.drop_append_of_le_length (by rw [List.length_drop]; omega),
      List.drop_eq_nil_of_le (by rw [List.length_drop]; omega),
      List.nil_append]
  rw [hover]
  -- the window at offset 1 is `ρ(u)`
  have hwin : ((u ++ u.take 2).drop 1).take n = u.rotate 1 := by
    rw [List.drop_append_of_le_length (by omega),
      List.rotate_eq_drop_append_take (by omega : 1 ≤ u.length)]
    rw [List.take_append]
    congr 1
    · rw [List.take_of_length_le (by rw [List.length_drop]; omega)]
    · rw [List.length_drop, hulen]
      have h2 : n - (n - 1) = 1 := by omega
      rw [h2, List.take_take]
      norm_num
  rw [hwin]
  exact isPermWord_rotate hu 1

/-- Deleting the marker from the rotation and from the door lands in the same marked
loop: `L(ρσ) = L(door σ)` (`n ≥ 2`). -/
theorem genLoop_door_eq_genLoop_rho {σ : List ℕ} (hn : 2 ≤ n) (hσ : IsPermWord n σ) :
    genLoop (door σ) = genLoop (rho σ) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hσ.ne_nil (by omega))
  obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
    rcases t with _ | ⟨b, s⟩
    · have := hσ.length; simp at this; omega
    · exact ⟨b, s, rfl⟩
  have hrho : rho (a :: b :: s) = b :: s ++ [a] := by
    show (a :: b :: s).rotate 1 = _
    simp
  have hdoor : door (a :: b :: s) = s ++ [b, a] := rfl
  rw [hrho, hdoor]
  unfold genLoop
  have h1 : (s ++ [b, a]).getLastD 0 = a := by
    have : s ++ [b, a] = (s ++ [b]) ++ [a] := by simp
    rw [this, List.getLastD_concat]
  have h2 : (b :: s ++ [a]).getLastD 0 = a := by
    have : b :: s ++ [a] = (b :: s) ++ [a] := by simp
    rw [this, List.getLastD_concat]
  have h3 : (s ++ [b, a]).dropLast = s ++ [b] := by
    have : s ++ [b, a] = (s ++ [b]) ++ [a] := by simp
    rw [this, List.dropLast_concat]
  have h4 : (b :: s ++ [a]).dropLast = b :: s := by
    have : b :: s ++ [a] = (b :: s) ++ [a] := by simp
    rw [this, List.dropLast_concat]
  rw [h1, h2, h3, h4]
  refine Prod.ext rfl ?_
  show rotClass (s ++ [b]) = rotClass (b :: s)
  apply Quotient.sound
  exact List.IsRotated.symm ⟨1, by simp⟩

/-! ## Weight bounds from junk-safety -/

/-- Over the empty alphabet every weight is the junk value `0`. -/
theorem wt_eq_zero_of_n_zero (u v : List ℕ) : wt 0 u v = 0 := by
  have hempty : {d | 1 ≤ d ∧ d ≤ 0 ∧ u.drop d = v.take (0 - d)} = ∅ := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    omega
  rw [wt, hempty, Nat.sInf_empty]

/-- A positive weight value is bounded by `n` (on a permutation-word source). -/
theorem le_n_of_wt_eq {u v : List ℕ} {w : ℕ} (hu : IsPermWord n u)
    (hw : wt n u v = w) (hwpos : 1 ≤ w) : w ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [wt_eq_zero_of_n_zero] at hw
    omega
  · have := (wt_spec (u := u) (v := v) hn (le_of_eq hu.length)).2.1
    omega

/-! ## Rotation classes: the unique word with a given last symbol -/

/-- Two rotated words with the same final symbol are equal, when the words are
duplicate-free: a rotation class contains at most one word ending in a given symbol. -/
theorem isRotated_concat_inj {u u' : List ℕ} {α : ℕ} (hnd : (u ++ [α]).Nodup)
    (hr : (u ++ [α]) ~r (u' ++ [α])) : u = u' := by
  obtain ⟨k, hk⟩ := hr
  have hlen : u'.length = u.length := by
    have h := congrArg List.length hk
    simp at h
    omega
  have hm : (u ++ [α]).length = u.length + 1 := by simp
  have hmpos : 0 < (u ++ [α]).length := by simp
  have hk' : (u ++ [α]).rotate (k % (u.length + 1)) = u' ++ [α] := by
    rw [← hm, List.rotate_mod]
    exact hk
  have hKlt : k % (u.length + 1) < u.length + 1 := Nat.mod_lt _ (by omega)
  have hα : α ∉ u := by
    rw [List.nodup_append] at hnd
    intro hmem
    exact hnd.2.2 α hmem α (List.mem_singleton_self α) rfl
  -- evaluate the rotation at the final index
  have e1 := congrArg (fun l => l[u.length]?) hk'
  rw [List.getElem?_rotate (by simp : u.length < (u ++ [α]).length), hm] at e1
  have hr1 : (u' ++ [α])[u.length]? = some α := by
    rw [← hlen, List.getElem?_append_right (le_refl _)]
    simp
  rw [hr1] at e1
  -- the hit index must be the final one
  set j := (u.length + k % (u.length + 1)) % (u.length + 1) with hj
  have hjlt : j < u.length + 1 := Nat.mod_lt _ (by omega)
  have hju : j = u.length := by
    by_contra hne
    have hjlt' : j < u.length := by omega
    rw [List.getElem?_append_left hjlt', List.getElem?_eq_getElem hjlt'] at e1
    have : u[j]'hjlt' = α := Option.some_inj.mp e1
    exact hα (this ▸ List.getElem_mem hjlt')
  -- whence the rotation amount is zero
  have hK0 : k % (u.length + 1) = 0 := by
    rw [hj] at hju
    rcases Nat.lt_or_ge (u.length + k % (u.length + 1)) (u.length + 1) with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at hju
      omega
    · rw [Nat.mod_eq_sub_mod hc,
        Nat.mod_eq_of_lt (by omega : u.length + k % (u.length + 1) - (u.length + 1)
          < u.length + 1)] at hju
      omega
  rw [hK0, List.rotate_zero] at hk'
  exact List.append_cancel_right hk'

/-! ## Door helpers -/

/-- At `n = 2` the door degenerates to the rotation. -/
theorem door_eq_rho_of_two {u : List ℕ} (hu : IsPermWord 2 u) : door u = rho u := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hu.ne_nil (by omega))
  obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
    rcases t with _ | ⟨b, s⟩
    · have := hu.length; simp at this
    · exact ⟨b, s, rfl⟩
  have hs : s = [] := by
    have := hu.length
    simp at this
    exact this
  subst hs
  show [b, a] = [a, b].rotate 1
  rfl

/-- Properness forces the weight-2 edge of a walk to be the door (the double rotation
is improper). -/
theorem Walk.door_of_wt_two {W : Walk n} {i : ℕ} (hi : i + 1 < W.numVerts)
    (hw : wt n (W.vert i) (W.vert (i + 1)) = 2) : W.vert (i + 1) = door (W.vert i) := by
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm (by omega)
  have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi
  have hn2 : 2 ≤ n := le_n_of_wt_eq hu hw (by omega)
  have hover : (W.vert i).drop 2 = (W.vert (i + 1)).take (n - 2) := by
    have := (wt_spec (u := W.vert i) (v := W.vert (i + 1)) (by omega)
      (le_of_eq hu.length)).2.2
    rwa [hw] at this
  rcases wt_two_word_cases hn2 hu hv hover with hrot | hdoor
  · exfalso
    apply W.properStep hi
    rw [hrot] at hw ⊢
    exact improper_rotate_two hn2 hu hw
  · exact hdoor

/-- A permutation word lies in the marked loop generated by its rotation
(`σ ∈ V(L(ρσ))`, `n ≥ 2`). -/
theorem mem_V_genLoop_rho {σ : List ℕ} (hn : 2 ≤ n) (hσ : IsPermWord n σ) :
    σ ∈ V n (genLoop (rho σ)) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hσ.ne_nil (by omega))
  obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
    rcases t with _ | ⟨b, s⟩
    · have := hσ.length; simp at this; omega
    · exact ⟨b, s, rfl⟩
  have hrho : rho (a :: b :: s) = (b :: s) ++ [a] := by
    show (a :: b :: s).rotate 1 = _
    simp
  refine ⟨hσ, ?_⟩
  rw [hrho]
  show rotClass ((a :: b :: s).erase (((b :: s) ++ [a]).getLastD 0)) =
    rotClass (((b :: s) ++ [a]).dropLast)
  rw [List.getLastD_concat, List.dropLast_concat, List.erase_cons_head]

/-! ## Counting words and rotation classes over a fixed symbol set

The paper's §3 counts ("`(n−1)!` cyclic classes, each of size `n`; `n(n−2)!` marked
2-loops; each loop has `n(n−1)` vertices") all reduce to counting duplicate-free words
with a prescribed symbol set `S` and their rotation classes.  We develop this once,
parametrized by `S : Finset ℕ`. -/

/-- The duplicate-free words with symbol set exactly `S`, as a `Finset`: the
permutations of the sorted listing of `S`. -/
noncomputable def permsOf (S : Finset ℕ) : Finset (List ℕ) :=
  (S.sort (· ≤ ·)).permutations.toFinset

theorem mem_permsOf {S : Finset ℕ} {w : List ℕ} :
    w ∈ permsOf S ↔ w.Nodup ∧ w.toFinset = S := by
  rw [permsOf, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr (S.sort_nodup _),
      by rw [List.toFinset_eq_of_perm _ _ h, S.sort_toFinset]⟩
  · rintro ⟨hnd, hS⟩
    exact List.perm_of_nodup_nodup_toFinset_eq hnd (S.sort_nodup _)
      (by rw [hS, S.sort_toFinset])

theorem length_of_mem_permsOf {S : Finset ℕ} {w : List ℕ} (h : w ∈ permsOf S) :
    w.length = S.card := by
  obtain ⟨hnd, hS⟩ := mem_permsOf.mp h
  rw [← List.toFinset_card_of_nodup hnd, hS]

theorem card_permsOf (S : Finset ℕ) : (permsOf S).card = S.card.factorial := by
  rw [permsOf,
    List.toFinset_card_of_nodup (List.nodup_permutations _ (S.sort_nodup _)),
    List.length_permutations, Finset.length_sort]

/-- Rotation-invariance of the `permsOf` condition. -/
theorem mem_permsOf_of_isRotated {S : Finset ℕ} {w w' : List ℕ} (h : w ∈ permsOf S)
    (hr : w ~r w') : w' ∈ permsOf S := by
  obtain ⟨k, rfl⟩ := hr
  obtain ⟨hnd, hS⟩ := mem_permsOf.mp h
  exact mem_permsOf.mpr ⟨(List.rotate_perm w k).nodup_iff.mpr hnd,
    by rw [List.toFinset_eq_of_perm _ _ (List.rotate_perm w k), hS]⟩

/-- The rotation classes of the duplicate-free words with symbol set `S`. -/
noncomputable def classesOf (S : Finset ℕ) : Finset RotClass :=
  (permsOf S).image rotClass

theorem mem_classesOf {S : Finset ℕ} {O : RotClass} :
    O ∈ classesOf S ↔ ∃ w, (w.Nodup ∧ w.toFinset = S) ∧ rotClass w = O := by
  rw [classesOf, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, mem_permsOf.mp hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, mem_permsOf.mpr hw, rfl⟩

/-- The `∀`-form of class membership used by `IsMarkedLoop`. -/
theorem mem_classesOf_iff_forall {S : Finset ℕ} {O : RotClass} :
    O ∈ classesOf S ↔ ∀ w, rotClass w = O → w.Nodup ∧ w.toFinset = S := by
  rw [mem_classesOf]
  constructor
  · rintro ⟨w, hw, rfl⟩ w' hw'
    exact mem_permsOf.mp
      (mem_permsOf_of_isRotated (mem_permsOf.mpr hw) (rotClass_eq_iff.mp hw'.symm))
  · intro h
    obtain ⟨w, hw⟩ := Quotient.exists_rep O
    exact ⟨w, h w hw, hw⟩

/-- Left-rotations of a duplicate-free word by distinct amounts `< length` differ. -/
theorem rotate_injOn_lt {w : List ℕ} (hnd : w.Nodup) {k k' : ℕ} (hk : k < w.length)
    (hk' : k' < w.length) (heq : w.rotate k = w.rotate k') : k = k' := by
  have h0 : 0 < w.length := by omega
  have e := congrArg (fun l => l[0]?) heq
  simp only [List.getElem?_rotate h0, Nat.zero_add, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt hk'] at e
  rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk'] at e
  exact (hnd.getElem_inj_iff).mp (Option.some_inj.mp e)

/-- The member set of the rotation class of a duplicate-free word `w` is the set of its
`length w` distinct rotations. -/
theorem classMembers_eq {w : List ℕ} :
    {w' | rotClass w' = rotClass w} = ↑((Finset.range w.length).image (w.rotate ·)) ∪
      (if w = [] then {[]} else ∅) := by
  rcases eq_or_ne w [] with rfl | hne
  · ext w'
    simp only [Set.mem_setOf_eq, if_pos rfl]
    constructor
    · intro h
      have hr := rotClass_eq_iff.mp h
      obtain ⟨k, hk⟩ := hr.symm
      simp at hk
      simp [hk]
    · intro h
      simp only [Set.union_def, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range,
        Set.mem_union, Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff] at h
      rcases h with ⟨k, -, rfl⟩ | rfl
      · simp
      · rfl
  · have hpos : 0 < w.length := List.length_pos_of_ne_nil hne
    ext w'
    simp only [Set.mem_setOf_eq, if_neg hne, Set.union_empty, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := (rotClass_eq_iff.mp h).symm
      exact ⟨k % w.length, Nat.mod_lt _ hpos, by rw [List.rotate_mod]; exact hk⟩
    · rintro ⟨k, -, rfl⟩
      exact (rotClass_eq_iff.mpr ⟨k, rfl⟩).symm

/-- Each rotation class of a nonempty duplicate-free word has exactly `length w`
members. -/
theorem ncard_classMembers {w : List ℕ} (hnd : w.Nodup) (hne : w ≠ []) :
    {w' | rotClass w' = rotClass w}.ncard = w.length := by
  rw [classMembers_eq, if_neg hne, Set.union_empty, Set.ncard_coe_finset,
    Finset.card_image_of_injOn, Finset.card_range]
  intro k hk k' hk' h
  exact rotate_injOn_lt hnd (Finset.mem_range.mp (Finset.mem_coe.mp hk))
    (Finset.mem_range.mp (Finset.mem_coe.mp hk')) h

/-- The classes of `S`-words number `(|S| − 1)!` (with the ℕ-convention `0 − 1 = 0`
giving the correct value `1` for `S = ∅`). -/
theorem card_classesOf (S : Finset ℕ) : (classesOf S).card = (S.card - 1).factorial := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · -- `S = ∅`: the only word is `[]`, the only class is `rotClass []`
    have hS : S = ∅ := Finset.card_eq_zero.mp h0
    subst hS
    have hperm : permsOf ∅ = {[]} := by
      ext w
      rw [mem_permsOf]
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨-, hw⟩
        rcases w with _ | ⟨a, t⟩
        · rfl
        · exfalso
          have : a ∈ (a :: t).toFinset := by simp
          rw [hw] at this
          simp at this
      · rintro rfl
        simp
    rw [classesOf, hperm]
    simp
  · -- `|S| ≥ 1`: fiberwise count, each class having `|S|` members
    have hfiber : ∀ O ∈ classesOf S,
        ((permsOf S).filter (fun w => rotClass w = O)).card = S.card := by
      intro O hO
      obtain ⟨w₀, hw₀mem, hw₀O⟩ := Finset.mem_image.mp hO
      have hw₀ := mem_permsOf.mp hw₀mem
      have hlen := length_of_mem_permsOf hw₀mem
      have hne : w₀ ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
        omega
      have hset : (((permsOf S).filter (fun w => rotClass w = O)) : Set (List ℕ)) =
          {w' | rotClass w' = rotClass w₀} := by
        ext w'
        simp only [Finset.coe_filter, Set.mem_setOf_eq, ← hw₀O]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · intro h
          refine ⟨mem_permsOf_of_isRotated hw₀mem ?_, h⟩
          exact (rotClass_eq_iff.mp h).symm
      have := ncard_classMembers hw₀.1 hne
      rw [← hset, Set.ncard_coe_finset] at this
      rw [this, hlen]
    have hcount := Finset.card_eq_sum_card_fiberwise
      (f := rotClass) (s := permsOf S) (t := classesOf S)
      (fun w hw => Finset.mem_image_of_mem _ hw)
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, card_permsOf] at hcount
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    rw [hm] at hcount ⊢
    rw [Nat.factorial_succ] at hcount
    simp only [Nat.add_sub_cancel]
    have h2 : (classesOf S).card * (m + 1) = m.factorial * (m + 1) := by
      rw [← hcount]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2

/-- The set of rotation classes of permutations of `[n]`, as a coerced `Finset`. -/
theorem permClasses_eq_coe (n : ℕ) :
    {O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O} =
      ↑(classesOf (Finset.Icc 1 n)) := by
  ext O
  simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_classesOf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, ⟨hw.nodup, hw.toFinset_eq⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, ⟨hw.1, hw.2⟩, rfl⟩

theorem permClasses_finite (n : ℕ) :
    {O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O}.Finite := by
  rw [permClasses_eq_coe]
  exact (classesOf (Finset.Icc 1 n)).finite_toSet

/-- The permutation words of `[n]` form a finite set. -/
theorem permWords_finite (n : ℕ) : {w | IsPermWord n w}.Finite := by
  have hset : {w | IsPermWord n w} = ↑(permsOf (Finset.Icc 1 n)) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_permsOf]
    exact ⟨fun h => ⟨h.nodup, h.toFinset_eq⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [hset]
  exact (permsOf _).finite_toSet

/-! ## Marked-loop validity of generated loops, and the active loop -/

/-- The loop generated by a permutation word is a valid marked 2-loop (`n ≥ 1`). -/
theorem isMarkedLoop_genLoop {σ : List ℕ} (hn : 1 ≤ n) (hσ : IsPermWord n σ) :
    IsMarkedLoop n (genLoop σ) := by
  have hne := hσ.ne_nil hn
  obtain ⟨l, a, rfl⟩ : ∃ l a, σ = l ++ [a] := by
    rcases List.eq_nil_or_concat σ with rfl | ⟨l, a, h⟩
    · exact absurd rfl hne
    · exact ⟨l, a, by rw [h, List.concat_eq_append]⟩
  have hgl : (l ++ [a]).getLastD 0 = a := List.getLastD_concat
  have hdl : (l ++ [a]).dropLast = l := List.dropLast_concat
  have hnd := hσ.nodup
  rw [List.nodup_append] at hnd
  have hal : a ∉ l := by
    intro ha
    exact hnd.2.2 a ha a (List.mem_singleton_self a) rfl
  have hbase : l.Nodup ∧ l.toFinset = Finset.Icc 1 n \ {a} := by
    refine ⟨hnd.1, ?_⟩
    have hσfin := hσ.toFinset_eq
    rw [List.toFinset_append] at hσfin
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton, ← hσfin,
      Finset.mem_union, List.mem_toFinset, List.toFinset_cons,
      List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.notMem_empty, or_false]
    constructor
    · intro hx
      refine ⟨Or.inl hx, ?_⟩
      intro hxa
      rw [hxa] at hx
      exact hal hx
    · rintro ⟨hx | hx, hxa⟩
      · exact hx
      · exact absurd hx hxa
  constructor
  · show (l ++ [a]).getLastD 0 ∈ Finset.Icc 1 n
    rw [hgl, ← hσ.toFinset_eq, List.mem_toFinset]
    simp
  · intro w hw
    have hw' : rotClass w = rotClass l := by
      rw [hw]
      show (genLoop (l ++ [a])).2 = _
      unfold genLoop
      rw [hdl]
    have hr : l ~r w := rotClass_eq_iff.mp hw'.symm
    obtain ⟨k, rfl⟩ := hr
    have hfst : (genLoop (l ++ [a])).1 = a := by
      show (l ++ [a]).getLastD 0 = a
      exact hgl
    rw [hfst]
    exact ⟨(List.rotate_perm _ k).nodup_iff.mpr hbase.1,
      by rw [List.toFinset_eq_of_perm _ _ (List.rotate_perm _ k), hbase.2]⟩

/-- Every active loop of a walk is generated by some earlier vertex. -/
theorem Walk.activeLoop_eq_genLoop {W : Walk n} :
    ∀ t, t < W.numVerts → ∃ s, s ≤ t ∧ s < W.numVerts ∧
      W.activeLoop t = genLoop (W.vert s) := by
  intro t
  induction t with
  | zero => intro ht; exact ⟨0, le_refl 0, ht, rfl⟩
  | succ t ih =>
    intro ht
    by_cases hw : 2 ≤ wt n (W.vert t) (W.vert (t + 1))
    · exact ⟨t + 1, le_refl _, ht, W.activeLoop_of_two_le_wt hw⟩
    · obtain ⟨s, hs1, hs2, hs3⟩ := ih (by omega)
      refine ⟨s, by omega, hs2, ?_⟩
      show (if 2 ≤ wt n (W.vert t) (W.vert (t + 1)) then genLoop (W.vert (t + 1))
        else W.activeLoop t) = _
      rw [if_neg hw]
      exact hs3

/-- Entered loops of a walk are valid marked 2-loops (`n ≥ 1`). -/
theorem Walk.isMarkedLoop_of_entered {W : Walk n} (hn : 1 ≤ n) {L : MarkedLoop}
    (hL : W.Entered L) : IsMarkedLoop n L := by
  obtain ⟨t, ht, rfl⟩ := hL
  obtain ⟨s, -, hs2, hs3⟩ := W.activeLoop_eq_genLoop t ht
  rw [hs3]
  exact isMarkedLoop_genLoop hn (W.vert_isPerm hs2)

/-- Inserting a fresh symbol at distinct positions yields distinct words. -/
theorem insert_pos_inj {w : List ℕ} {α : ℕ} (hα : α ∉ w) {j j' : ℕ}
    (hj : j ≤ w.length) (hj' : j' ≤ w.length)
    (heq : w.take j ++ α :: w.drop j = w.take j' ++ α :: w.drop j') : j = j' := by
  have key : ∀ {a b : ℕ}, a < b → b ≤ w.length →
      w.take a ++ α :: w.drop a = w.take b ++ α :: w.drop b → False := by
    intro a b hab hb heq'
    have hlta : (w.take a).length = a := by rw [List.length_take]; omega
    have hltb : (w.take b).length = b := by rw [List.length_take]; omega
    have e := congrArg (fun l => l[a]?) heq'
    rw [List.getElem?_append_right (by omega : (w.take a).length ≤ a), hlta,
      Nat.sub_self, List.getElem?_append_left (by omega : a < (w.take b).length),
      List.getElem?_take_of_lt hab, List.getElem?_eq_getElem (by omega : a < w.length)]
      at e
    have hαa : α = w[a]'(by omega) := by
      have e0 : (α :: w.drop a)[0]? = some α := rfl
      rw [e0] at e
      exact Option.some_inj.mp e
    apply hα
    rw [hαa]
    exact List.getElem_mem (by omega)
  rcases Nat.lt_trichotomy j j' with h | h | h
  · exact absurd heq (fun he => key h hj' he)
  · exact h
  · exact absurd heq.symm (fun he => key h hj he)

/-- The marked loop `(α, [del_α σ])` obtained from a permutation word by deleting any
symbol `α ∈ [n]` is valid. -/
theorem isMarkedLoop_marker_erase {σ : List ℕ} (hσ : IsPermWord n σ) {α : ℕ}
    (hα : α ∈ Finset.Icc 1 n) : IsMarkedLoop n (α, rotClass (σ.erase α)) := by
  refine ⟨hα, ?_⟩
  have hbase : (σ.erase α).Nodup ∧ (σ.erase α).toFinset = Finset.Icc 1 n \ {α} := by
    refine ⟨hσ.nodup.erase _, ?_⟩
    ext x
    rw [List.mem_toFinset, hσ.nodup.mem_erase_iff, Finset.mem_sdiff,
      Finset.mem_singleton, ← hσ.toFinset_eq, List.mem_toFinset]
    tauto
  intro w hw
  have hw' : rotClass w = rotClass (σ.erase α) := hw
  have hr : (σ.erase α) ~r w := rotClass_eq_iff.mp hw'.symm
  obtain ⟨k, rfl⟩ := hr
  exact ⟨(List.rotate_perm _ k).nodup_iff.mpr hbase.1,
    by rw [List.toFinset_eq_of_perm _ _ (List.rotate_perm _ k), hbase.2]⟩

/-! ## A union bound for `Set.ncard` -/

/-- The cardinality of a finite union is at most the sum of the cardinalities. -/
theorem ncard_biUnion_le {α β : Type*} (t : Finset β) (f : β → Set α) :
    (⋃ b ∈ t, f b).ncard ≤ ∑ b ∈ t, (f b).ncard := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    calc (f a ∪ ⋃ b ∈ s, f b).ncard
        ≤ (f a).ncard + (⋃ b ∈ s, f b).ncard := Set.ncard_union_le _ _
      _ ≤ (f a).ncard + ∑ b ∈ s, (f b).ncard := by omega

/-- Covering a set by finitely many finite sets bounds its cardinality by the sum. -/
theorem ncard_le_sum_of_cover {α β : Type*} {T : Set α} (t : Finset β) (f : β → Set α)
    (hcov : T ⊆ ⋃ b ∈ t, f b) (hfin : ∀ b ∈ t, (f b).Finite) :
    T.ncard ≤ ∑ b ∈ t, (f b).ncard :=
  le_trans (Set.ncard_le_ncard hcov (Set.Finite.biUnion t.finite_toSet hfin))
    (ncard_biUnion_le t f)

/-! ## Incidence: the `n − 1` orbits of a marked 2-loop -/

/-- Incidence from a single member (`V(L)` is closed under rotation). -/
theorem incident_of_mem {O : RotClass} {L : MarkedLoop} (w : List ℕ)
    (hw : rotClass w = O) (hmem : w ∈ V n L) : Incident n O L := by
  intro w' hw'
  obtain ⟨k, rfl⟩ := rotClass_eq_iff.mp (hw.trans hw'.symm)
  exact V_closed_rotate L hmem k

/-- A valid marked 2-loop is incident with exactly `n − 1` rotation orbits (each orbit
contains a unique marker-last vertex, whose marker-free part runs over the `n − 1`
rotations of the class). -/
theorem card_incident_orbits (hn : 2 ≤ n) {L : MarkedLoop} (hL : IsMarkedLoop n L) :
    {O | Incident n O L}.ncard = n - 1 := by
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
  set g : ℕ → RotClass := fun k => rotClass (u₀.rotate k ++ [L.1]) with hg
  have hα_k : ∀ k : ℕ, L.1 ∉ u₀.rotate k :=
    fun k h => hαu₀ ((List.rotate_perm u₀ k).mem_iff.mp h)
  have hndk : ∀ k : ℕ, (u₀.rotate k ++ [L.1]).Nodup := by
    intro k
    rw [List.nodup_append]
    refine ⟨(List.rotate_perm u₀ k).nodup_iff.mpr hu₀.1, List.nodup_singleton _, ?_⟩
    intro y hy z hz
    rw [List.mem_singleton] at hz
    subst hz
    intro hyz
    exact hα_k k (hyz ▸ hy)
  have hmemV : ∀ k : ℕ, u₀.rotate k ++ [L.1] ∈ V n L := by
    intro k
    have hfin : (u₀.rotate k ++ [L.1]).toFinset = Finset.Icc 1 n := by
      rw [List.toFinset_append, List.toFinset_eq_of_perm _ _ (List.rotate_perm u₀ k),
        hu₀.2]
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      rw [Finset.sdiff_singleton_eq_erase]
      ext x
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro (⟨-, hx⟩ | rfl)
        · exact hx
        · exact hαIcc
      · intro hx
        by_cases hxα : x = L.1
        · exact Or.inr hxα
        · exact Or.inl ⟨hxα, hx⟩
    refine ⟨⟨hndk k, hfin⟩, ?_⟩
    rw [List.erase_append_right _ (hα_k k), List.erase_cons_head, List.append_nil]
    rw [← hu₀K']
    exact (rotClass_eq_iff.mpr ⟨k, rfl⟩).symm
  have hset : {O | Incident n O L} = ↑((Finset.range (n - 1)).image g) := by
    ext O
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · intro hO
      obtain ⟨w₀, hw₀⟩ := Quotient.exists_rep O
      have hw₀' : rotClass w₀ = O := hw₀
      have hw₀V : w₀ ∈ V n L := hO w₀ hw₀'
      have hw₀perm := hw₀V.1
      have hαw : L.1 ∈ w₀ := by
        rw [← List.mem_toFinset, hw₀perm.toFinset_eq]
        exact hαIcc
      obtain ⟨t, r, rfl⟩ := List.append_of_mem hαw
      have hsplit : t ++ L.1 :: r = (t ++ [L.1]) ++ r := by simp
      have htlen : (t ++ [L.1]).length = t.length + 1 := by simp
      have hrot : (t ++ L.1 :: r).rotate (t.length + 1) = (r ++ t) ++ [L.1] := by
        rw [hsplit, List.rotate_eq_drop_append_take (by
          rw [List.length_append, htlen]; omega),
          List.drop_left' htlen, List.take_left' htlen, List.append_assoc]
      have hVrot : (r ++ t) ++ [L.1] ∈ V n L := by
        have := V_closed_rotate L hw₀V (t.length + 1)
        rwa [hrot] at this
      have hαrt : L.1 ∉ r ++ t := by
        have hnd := hVrot.1.nodup
        rw [List.nodup_append] at hnd
        intro h
        exact hnd.2.2 L.1 h L.1 (List.mem_singleton_self _) rfl
      have hclass : rotClass (r ++ t) = rotClass u₀ := by
        have h2 := hVrot.2
        rw [List.erase_append_right _ hαrt, List.erase_cons_head, List.append_nil] at h2
        rw [h2, hu₀K']
      obtain ⟨m, hm⟩ := rotClass_eq_iff.mp hclass.symm
      have hpos : 0 < u₀.length := by omega
      refine ⟨m % u₀.length, by rw [← hlen]; exact Nat.mod_lt _ hpos, ?_⟩
      show rotClass (u₀.rotate (m % u₀.length) ++ [L.1]) = O
      rw [List.rotate_mod, hm, ← hrot, ← hw₀']
      exact (rotClass_eq_iff.mpr ⟨t.length + 1, rfl⟩).symm
    · rintro ⟨k, hk, rfl⟩
      exact incident_of_mem _ rfl (hmemV k)
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro k hk k' hk' heq
  rw [Finset.mem_coe, Finset.mem_range] at hk hk'
  have heq' : u₀.rotate k = u₀.rotate k' :=
    isRotated_concat_inj (hndk k) (rotClass_eq_iff.mp heq)
  exact rotate_injOn_lt hu₀.1 (by omega) (by omega) heq'

/-! ## Shared orbits: finiteness and the `q`-sum -/

/-- A shared orbit (indeed any orbit with an entered owner) is an orbit of
permutations. -/
theorem Walk.dset_subset_permClasses {W : Walk n} :
    W.Dset ⊆ {O : RotClass | ∃ w, IsPermWord n w ∧ rotClass w = O} := by
  intro O hO
  have h2 : 2 ≤ W.mu O := hO
  have hne : (W.OmegaSet O).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [Walk.mu, h, Set.ncard_empty] at h2
    omega
  obtain ⟨L, -, hinc⟩ := hne
  obtain ⟨w, hw⟩ := Quotient.exists_rep O
  have hw' : rotClass w = O := hw
  exact ⟨w, (hinc w hw').1, hw'⟩

theorem Walk.dset_finite (W : Walk n) : W.Dset.Finite :=
  (permClasses_finite n).subset W.dset_subset_permClasses

/-- The excess incidence count as a `Finset` sum. -/
theorem Walk.qStat_eq_sum (W : Walk n) :
    W.qStat = ∑ O ∈ W.dset_finite.toFinset, (W.mu O - 1) := by
  rw [Walk.qStat, finsum_mem_eq_finite_toFinset_sum _ W.dset_finite]

/-- `μ(O) ≥ 1` follows from any member of `Ω(O)`. -/
theorem Walk.one_le_mu_of_mem {W : Walk n} {O : RotClass} {L : MarkedLoop}
    (hL : L ∈ W.OmegaSet O) : 1 ≤ W.mu O := by
  rw [Walk.mu, Nat.one_le_iff_ne_zero]
  intro h0
  rw [Set.ncard_eq_zero (W.omega_finite O)] at h0
  rw [h0] at hL
  exact hL

/-! ## The block decomposition of the first-entry sequence (§4) -/

/-- The start of the canonical block containing first-entry index `i`: the largest
index `≤ i` that is `0` or follows a break. -/
noncomputable def Walk.blockStart (W : Walk n) (i : ℕ) : ℕ :=
  sSup {s | s ≤ i ∧ (s = 0 ∨ W.IsBreak (s - 1))}

theorem Walk.blockStart_spec (W : Walk n) (i : ℕ) :
    W.blockStart i ≤ i ∧ (W.blockStart i = 0 ∨ W.IsBreak (W.blockStart i - 1)) := by
  have hne : {s | s ≤ i ∧ (s = 0 ∨ W.IsBreak (s - 1))}.Nonempty :=
    ⟨0, Nat.zero_le i, Or.inl rfl⟩
  have hfin : {s | s ≤ i ∧ (s = 0 ∨ W.IsBreak (s - 1))}.Finite :=
    (Set.finite_Iic i).subset (fun s hs => hs.1)
  exact hne.csSup_mem hfin

theorem Walk.le_blockStart (W : Walk n) {i s : ℕ} (hs : s ≤ i)
    (hbr : s = 0 ∨ W.IsBreak (s - 1)) : s ≤ W.blockStart i := by
  have hfin : {s | s ≤ i ∧ (s = 0 ∨ W.IsBreak (s - 1))}.Finite :=
    (Set.finite_Iic i).subset (fun s hs => hs.1)
  exact le_csSup hfin.bddAbove ⟨hs, hbr⟩

/-- No break occurs strictly inside a block. -/
theorem Walk.blockStart_no_break (W : Walk n) {i j : ℕ}
    (hj1 : W.blockStart i ≤ j) (hj2 : j < i) : ¬ W.IsBreak j := by
  intro hbr
  have h := W.le_blockStart (i := i) (s := j + 1) (by omega)
    (Or.inr (by simpa using hbr))
  omega

theorem Walk.breakSet_finite (W : Walk n) : W.breakSet.Finite :=
  (Set.finite_Iio W.numFE).subset (fun j hj => by
    have := hj.1
    simp only [Set.mem_Iio]
    omega)

/-- **The abstract block count**: if every block has at most `m + 1` members
(`i − blockStart i ≤ m`), and `SB` is a set of break block-starts (each giving a block
of size 1), then `numFE + |SB|·m ≤ (|A| + 1)(m + 1)`. -/
theorem Walk.numFE_add_le (W : Walk n) (m : ℕ)
    (hrun : ∀ i, i < W.numFE → i - W.blockStart i ≤ m)
    (SB : Finset ℕ) (hSBbr : ∀ b ∈ SB, W.IsBreak b ∧ (b = 0 ∨ W.IsBreak (b - 1))) :
    W.numFE + SB.card * m ≤ (W.breakSet.ncard + 1) * (m + 1) := by
  classical
  set A1 : Finset ℕ := insert 0 ((W.breakSet_finite.toFinset).image (· + 1)) with hA1
  have hmaps : ∀ i ∈ Finset.range W.numFE, W.blockStart i ∈ A1 := by
    intro i _
    obtain ⟨-, h0 | hbr⟩ := W.blockStart_spec i
    · rw [h0]
      exact Finset.mem_insert_self _ _
    · rcases Nat.eq_zero_or_pos (W.blockStart i) with h0 | hpos
      · rw [h0]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨W.blockStart i - 1, W.breakSet_finite.mem_toFinset.mpr hbr, by omega⟩)
  have hcount := Finset.card_eq_sum_card_fiberwise (f := W.blockStart)
    (s := Finset.range W.numFE) (t := A1) hmaps
  rw [Finset.card_range] at hcount
  have hfib : ∀ b ∈ A1,
      ((Finset.range W.numFE).filter (fun i => W.blockStart i = b)).card ≤ m + 1 := by
    intro b _
    have hsub : (Finset.range W.numFE).filter (fun i => W.blockStart i = b) ⊆
        Finset.Icc b (b + m) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_Icc]
      have h1 := (W.blockStart_spec i).1
      have h2 := hrun i hi.1
      have h3 := hi.2
      omega
    calc ((Finset.range W.numFE).filter (fun i => W.blockStart i = b)).card
        ≤ (Finset.Icc b (b + m)).card := Finset.card_le_card hsub
      _ = m + 1 := by rw [Nat.card_Icc]; omega
  have hfibSB : ∀ b ∈ SB,
      ((Finset.range W.numFE).filter (fun i => W.blockStart i = b)).card ≤ 1 := by
    intro b hb
    rw [Finset.card_le_one]
    have hkey : ∀ x ∈ (Finset.range W.numFE).filter (fun i => W.blockStart i = b),
        x = b := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      by_contra hxb
      have hlt : b < x := by
        have := (W.blockStart_spec x).1
        omega
      exact W.blockStart_no_break (le_of_eq hx.2) hlt (hSBbr b hb).1
    intro i hi j hj
    rw [hkey i hi, hkey j hj]
  have hSBsub : SB ⊆ A1 := by
    intro b hb
    rcases Nat.eq_zero_or_pos b with h0 | hpos
    · rw [h0]
      exact Finset.mem_insert_self _ _
    · rcases (hSBbr b hb).2 with h0 | hbr
      · omega
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨b - 1, W.breakSet_finite.mem_toFinset.mpr hbr, by omega⟩)
  have hA1card : A1.card ≤ W.breakSet.ncard + 1 := by
    calc A1.card ≤ ((W.breakSet_finite.toFinset).image (· + 1)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ W.breakSet_finite.toFinset.card + 1 := by
          have := Finset.card_image_le (f := (· + 1)) (s := W.breakSet_finite.toFinset)
          omega
      _ = W.breakSet.ncard + 1 := by
          rw [Set.ncard_eq_toFinset_card _ W.breakSet_finite]
  have hsdcard : (A1 \ SB).card = A1.card - SB.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSBsub]
  have hSBle : SB.card ≤ A1.card := Finset.card_le_card hSBsub
  calc W.numFE + SB.card * m
      = (∑ b ∈ A1 \ SB, ((Finset.range W.numFE).filter
            (fun i => W.blockStart i = b)).card +
         ∑ b ∈ SB, ((Finset.range W.numFE).filter
            (fun i => W.blockStart i = b)).card) + SB.card * m := by
        rw [Finset.sum_sdiff hSBsub, ← hcount]
    _ ≤ ((A1 \ SB).card * (m + 1) + SB.card * 1) + SB.card * m := by
        have h1 := Finset.sum_le_card_nsmul (A1 \ SB)
          (fun b => ((Finset.range W.numFE).filter (fun i => W.blockStart i = b)).card)
          (m + 1) (fun b hb => hfib b (Finset.mem_sdiff.mp hb).1)
        have h2 := Finset.sum_le_card_nsmul SB
          (fun b => ((Finset.range W.numFE).filter (fun i => W.blockStart i = b)).card)
          1 (fun b hb => hfibSB b hb)
        simp only [smul_eq_mul] at h1 h2
        omega
    _ = A1.card * (m + 1) := by
        rw [hsdcard, Nat.mul_one]
        have : (A1.card - SB.card) * (m + 1) + SB.card * (m + 1) = A1.card * (m + 1) := by
          rw [← Nat.add_mul]
          congr 1
          omega
        rw [← this]
        ring
    _ ≤ (W.breakSet.ncard + 1) * (m + 1) := Nat.mul_le_mul_right _ hA1card

/-! ## Gluing walks, and refining improper edges into proper paths (§2) -/

theorem Walk.vert_mem {W : Walk n} {t : ℕ} (ht : t < W.numVerts) :
    W.vert t ∈ W.verts := by
  rw [W.vert_eq_getElem ht]
  exact List.getElem_mem _

/-- Glue two walks whose endpoint and startpoint agree: drop the duplicated seam
vertex. -/
def Walk.glue (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0) : Walk n where
  verts := W₁.verts.dropLast ++ W₂.verts
  ne := by
    intro h0
    exact W₂.ne (List.append_eq_nil_iff.mp h0).2
  isPerm := by
    intro w hw
    rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact W₁.isPerm w (List.dropLast_sublist _ |>.subset hw)
    · exact W₂.isPerm w hw
  chain := by
    rw [List.isChain_append]
    refine ⟨W₁.chain.prefix (List.dropLast_prefix _), W₂.chain, ?_⟩
    intro x hx y hy
    -- the seam edge is the final edge of `W₁`
    have hW₁ : W₁.verts = W₁.verts.dropLast ++ [W₁.verts.getLastD []] := by
      obtain ⟨l, a, hla⟩ : ∃ l a, W₁.verts = l ++ [a] := by
        rcases List.eq_nil_or_concat W₁.verts with h0 | ⟨l, a, h0⟩
        · exact absurd h0 W₁.ne
        · exact ⟨l, a, by rw [h0, List.concat_eq_append]⟩
      rw [hla, List.dropLast_concat, List.getLastD_concat]
    have hchain := W₁.chain
    rw [hW₁, List.isChain_append] at hchain
    have hseam := hchain.2.2 x hx (W₁.verts.getLastD []) rfl
    have hy' : y = W₂.vert 0 := by
      obtain ⟨b, l₂, hb⟩ := List.exists_cons_of_ne_nil W₂.ne
      rw [hb, List.head?_cons, Option.mem_some_iff] at hy
      rw [← hy]
      show b = (W₂.verts).getD 0 []
      rw [hb]
      rfl
    rw [hy', ← h]
    exact hseam

theorem Walk.glue_verts (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0) :
    (W₁.glue W₂ h).verts = W₁.verts.dropLast ++ W₂.verts := rfl

theorem Walk.glue_vert_zero (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0) :
    (W₁.glue W₂ h).vert 0 = W₁.vert 0 := by
  show (W₁.verts.dropLast ++ W₂.verts).getD 0 [] = W₁.verts.getD 0 []
  rcases hd : W₁.verts.dropLast with _ | ⟨x, l⟩
  · -- `W₁` is a single vertex, equal to the start of `W₂`
    obtain ⟨a, l₁, ha⟩ := List.exists_cons_of_ne_nil W₁.ne
    have hl₁ : l₁ = [] := by
      rw [ha] at hd
      rcases l₁ with _ | ⟨b, l₂⟩
      · rfl
      · simp at hd
    rw [ha, hl₁] at h ⊢
    simp only [List.nil_append]
    show W₂.vert 0 = [a].getD 0 []
    rw [← h]
    rfl
  · -- `W₁` has at least two vertices
    have hhead : W₁.verts.getD 0 [] = x := by
      obtain ⟨a, l₁, ha⟩ := List.exists_cons_of_ne_nil W₁.ne
      rw [ha] at hd ⊢
      rcases l₁ with _ | ⟨b, l₂⟩
      · simp at hd
      · simp only [List.dropLast_cons_cons] at hd
        rw [List.cons.injEq] at hd
        rw [hd.1]
        rfl
    rw [hhead]
    rfl

theorem Walk.glue_getLastD (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0) :
    (W₁.glue W₂ h).verts.getLastD [] = W₂.verts.getLastD [] := by
  show (W₁.verts.dropLast ++ W₂.verts).getLastD [] = _
  obtain ⟨l, a, hla⟩ : ∃ l a, W₂.verts = l ++ [a] := by
    rcases List.eq_nil_or_concat W₂.verts with h0 | ⟨l, a, h0⟩
    · exact absurd h0 W₂.ne
    · exact ⟨l, a, by rw [h0, List.concat_eq_append]⟩
  rw [hla, ← List.append_assoc, List.getLastD_concat, List.getLastD_concat]

theorem Walk.glue_mem_left (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0)
    {x : List ℕ} (hx : x ∈ W₁.verts) : x ∈ (W₁.glue W₂ h).verts := by
  show x ∈ W₁.verts.dropLast ++ W₂.verts
  obtain ⟨l, a, hla⟩ : ∃ l a, W₁.verts = l ++ [a] := by
    rcases List.eq_nil_or_concat W₁.verts with h0 | ⟨l, a, h0⟩
    · exact absurd h0 W₁.ne
    · exact ⟨l, a, by rw [h0, List.concat_eq_append]⟩
  rw [hla, List.dropLast_concat]
  rw [hla, List.mem_append, List.mem_singleton] at hx
  rw [List.mem_append]
  rcases hx with hx | hx
  · exact Or.inl hx
  · right
    subst hx
    have : W₂.vert 0 ∈ W₂.verts := W₂.vert_mem W₂.numVerts_pos
    rw [← h] at this
    rw [hla, List.getLastD_concat] at this
    exact this

theorem Walk.glue_mem_right (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0)
    {x : List ℕ} (hx : x ∈ W₂.verts) : x ∈ (W₁.glue W₂ h).verts := by
  show x ∈ W₁.verts.dropLast ++ W₂.verts
  rw [List.mem_append]
  exact Or.inr hx

/-- The weight-sum of a glued walk adds. -/
theorem wtsum_glue (l₁ : List (List ℕ)) (a : List ℕ) (l₂ : List (List ℕ)) :
    (List.zipWith (wt n) (l₁ ++ a :: l₂) (l₁ ++ a :: l₂).tail).sum
      = (List.zipWith (wt n) (l₁ ++ [a]) (l₁ ++ [a]).tail).sum
        + (List.zipWith (wt n) (a :: l₂) (a :: l₂).tail).sum := by
  induction l₁ with
  | nil => simp
  | cons x l₁ ih =>
    rcases l₁ with _ | ⟨y, l₁'⟩
    · simp only [List.nil_append, List.cons_append, List.tail_cons,
        List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      omega
    · simp only [List.cons_append, List.tail_cons, List.zipWith_cons_cons,
        List.sum_cons] at ih ⊢
      omega

theorem Walk.glue_wtW (W₁ W₂ : Walk n) (h : W₁.verts.getLastD [] = W₂.vert 0) :
    (W₁.glue W₂ h).wtW = W₁.wtW + W₂.wtW := by
  show (List.zipWith (wt n) (W₁.verts.dropLast ++ W₂.verts)
      (W₁.verts.dropLast ++ W₂.verts).tail).sum = _
  obtain ⟨b, l₂, hb⟩ := List.exists_cons_of_ne_nil W₂.ne
  have hbv : b = W₂.vert 0 := by
    show b = W₂.verts.getD 0 []
    rw [hb]
    rfl
  obtain ⟨l, a, hla⟩ : ∃ l a, W₁.verts = l ++ [a] := by
    rcases List.eq_nil_or_concat W₁.verts with h0 | ⟨l, a, h0⟩
    · exact absurd h0 W₁.ne
    · exact ⟨l, a, by rw [h0, List.concat_eq_append]⟩
  have hab : a = b := by
    rw [hla, List.getLastD_concat] at h
    rw [h, hbv]
  subst hab
  rw [hb, hla, List.dropLast_concat, wtsum_glue]
  congr 1
  · show _ = (List.zipWith (wt n) W₁.verts W₁.verts.tail).sum
    rw [hla]
  · show _ = (List.zipWith (wt n) W₂.verts W₂.verts.tail).sum
    rw [hb]

/-- The two weight bounds of the improper-edge split: inserting the intermediate
permutation window at offset `h` cuts the edge into pieces of weight `≤ h` and
`≤ wt − h`. -/
theorem improper_split {u v : List ℕ} (hn : 1 ≤ n) (hu : IsPermWord n u)
    (hv : IsPermWord n v) {h : ℕ} (hh1 : 1 ≤ h) (hh2 : h < wt n u v) :
    wt n u (((overlapWord n u v).drop h).take n) ≤ h ∧
      wt n (((overlapWord n u v).drop h).take n) v ≤ wt n u v - h := by
  obtain ⟨hd1, hdn, hover⟩ := wt_spec (u := u) (v := v) hn (le_of_eq hu.length)
  have hulen := hu.length
  have hvlen := hv.length
  have hwin : ((overlapWord n u v).drop h).take n =
      u.drop h ++ (v.drop (n - wt n u v)).take h := by
    show ((u ++ v.drop (n - wt n u v)).drop h).take n = _
    rw [List.drop_append_of_le_length (by omega : h ≤ u.length), List.take_append]
    congr 1
    · exact List.take_of_length_le (by rw [List.length_drop]; omega)
    · congr 1
      rw [List.length_drop, hulen]
      omega
  constructor
  · -- `wt(u, m) ≤ h`: the length-(n−h) suffix of `u` is the prefix of `m`
    refine wt_le hh1 (by omega) ?_
    rw [hwin, List.take_left' (by rw [List.length_drop]; omega)]
  · -- `wt(m, v) ≤ wt − h`: dropping `wt − h` from `m` leaves a prefix of `v`
    refine wt_le (by omega) (by omega) ?_
    show (((overlapWord n u v).drop h).take n).drop (wt n u v - h) = _
    rw [List.drop_take, List.drop_drop]
    have hd : h + (wt n u v - h) = wt n u v := by omega
    rw [hd]
    have hover2 : (overlapWord n u v).drop (wt n u v) = v := by
      show (u ++ v.drop (n - wt n u v)).drop (wt n u v) = v
      rw [List.drop_append_of_le_length (by omega : wt n u v ≤ u.length), hover,
        List.take_append_drop]
    rw [hover2]

/-- **Refinement of an edge into a proper path**: between any two permutation words
there is a walk (a chain of proper edges) of total weight at most `wt(u,v)`. -/
theorem exists_proper_path (hn : 1 ≤ n) :
    ∀ (d : ℕ) (u v : List ℕ), IsPermWord n u → IsPermWord n v → wt n u v ≤ d →
      ∃ W : Walk n, W.vert 0 = u ∧ W.verts.getLastD [] = v ∧ W.wtW ≤ wt n u v := by
  intro d
  induction d with
  | zero =>
    intro u v hu hv hwt
    have := (wt_spec (u := u) (v := v) hn (le_of_eq hu.length)).1
    omega
  | succ d ih =>
    intro u v hu hv hwt
    by_cases hp : ProperStep n u v
    · -- a single proper edge
      refine ⟨⟨[u, v], by simp, ?_, ?_⟩, rfl, rfl, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hu
        · rw [List.mem_singleton] at hw
          subst hw
          exact hv
      · exact List.isChain_pair.mpr hp
      · show (List.zipWith (wt n) [u, v] [v]).sum ≤ wt n u v
        simp
    · -- split at the first intermediate permutation window and recurse
      have himp : Improper n u v := not_not.mp hp
      obtain ⟨h, hh1, hh2, hm⟩ := himp
      obtain ⟨h1, h2⟩ := improper_split hn hu hv hh1 hh2
      obtain ⟨W₁, hW₁0, hW₁l, hW₁w⟩ := ih u _ hu hm (by omega)
      obtain ⟨W₂, hW₂0, hW₂l, hW₂w⟩ := ih _ v hm hv (by omega)
      refine ⟨W₁.glue W₂ (by rw [hW₁l, hW₂0]), ?_, ?_, ?_⟩
      · rw [Walk.glue_vert_zero]
        exact hW₁0
      · rw [Walk.glue_getLastD]
        exact hW₂l
      · rw [Walk.glue_wtW]
        omega

/-- The overlap-position bound: consecutive permutation windows of a word at positions
`p < q` overlap in all but `q − p` symbols. -/
theorem wt_le_pos_gap {w : List ℕ} {p q : ℕ} (hn : 1 ≤ n) (hpq : p < q)
    (hq : q + n ≤ w.length) (hup : IsPermWord n ((w.drop p).take n)) :
    wt n ((w.drop p).take n) ((w.drop q).take n) ≤ q - p := by
  rcases Nat.lt_or_ge (q - p) n with hlt | hge
  · refine wt_le (by omega) (by omega) ?_
    rw [List.drop_take, List.drop_drop]
    have h1 : p + (q - p) = q := by omega
    rw [h1, List.take_take]
    congr 1
    omega
  · have := (wt_spec (u := (w.drop p).take n) (v := (w.drop q).take n) hn
      (le_of_eq hup.length)).2.1
    omega

/-- Helper: covering walks exist — glue proper paths through the list of all
permutation words.  Needed so that `Λ(n)` is the minimum of a nonempty set.
(Declared in `Coeff2/Helpers.lean`; proved here, where the refinement
machinery lives.) -/
theorem covering_walk_exists (n : ℕ) : ∃ W : Walk n, W.Covering := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨[[]], by simp, ?_, List.isChain_singleton _⟩, ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨List.nodup_nil, by simp⟩
    · intro x hx
      rw [List.length_eq_zero_iff.mp hx.length]
      exact List.mem_singleton_self _
  · have hthrough : ∀ (l : List (List ℕ)) (u : List ℕ), IsPermWord n u →
        (∀ x ∈ l, IsPermWord n x) →
        ∃ W : Walk n, W.vert 0 = u ∧ u ∈ W.verts ∧ ∀ x ∈ l, x ∈ W.verts := by
      intro l
      induction l with
      | nil =>
        intro u hu _
        refine ⟨⟨[u], by simp, ?_, List.isChain_singleton _⟩, rfl,
          List.mem_singleton_self _, by simp⟩
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact hu
      | cons x l' ih =>
        intro u hu hl
        obtain ⟨W₂, hW₂0, hW₂u, hW₂mem⟩ := ih x (hl x List.mem_cons_self)
          (fun y hy => hl y (List.mem_cons_of_mem x hy))
        obtain ⟨W₁, hW₁0, hW₁l, -⟩ := exists_proper_path hn (wt n u x) u x hu
          (hl x List.mem_cons_self) (le_refl _)
        have hseam : W₁.verts.getLastD [] = W₂.vert 0 := by rw [hW₁l, hW₂0]
        refine ⟨W₁.glue W₂ hseam, ?_, ?_, ?_⟩
        · rw [Walk.glue_vert_zero]
          exact hW₁0
        · refine Walk.glue_mem_left _ _ _ ?_
          rw [← hW₁0]
          exact W₁.vert_mem W₁.numVerts_pos
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact Walk.glue_mem_right _ _ _ hW₂u
          · exact Walk.glue_mem_right _ _ _ (hW₂mem y hy)
    obtain ⟨W, -, -, hmem⟩ := hthrough (refList n).permutations (refList n)
      ⟨refList_nodup n, refList_toFinset n⟩
      (fun x hx => isPermWord_iff_perm_refList.mpr (List.mem_permutations.mp hx))
    exact ⟨W, fun v hv => hmem v
      (List.mem_permutations.mpr (isPermWord_iff_perm_refList.mp hv))⟩

/-! ## The word of a walk (§2, Proposition exactmodel) -/

/-- The word of a walk: each vertex contributes the first `wt` symbols of its word,
the final vertex its whole word. -/
noncomputable def wordOf (n : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | [σ] => σ
  | σ :: τ :: rest => σ.take (wt n σ τ) ++ wordOf n (τ :: rest)

theorem wordOf_length (hn : 1 ≤ n) :
    ∀ (l : List (List ℕ)), l ≠ [] → (∀ x ∈ l, IsPermWord n x) →
      (wordOf n l).length = n + (List.zipWith (wt n) l l.tail).sum
  | [], h, _ => absurd rfl h
  | [σ], _, hp => by
    show σ.length = n + (List.zipWith (wt n) [σ] []).sum
    rw [(hp σ (List.mem_singleton_self σ)).length]
    simp
  | σ :: τ :: rest, _, hp => by
    have ih := wordOf_length hn (τ :: rest) (by simp)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have hσ := hp σ List.mem_cons_self
    have hwt : wt n σ τ ≤ n :=
      (wt_spec (u := σ) (v := τ) hn (le_of_eq hσ.length)).2.1
    show (σ.take (wt n σ τ) ++ wordOf n (τ :: rest)).length = _
    rw [List.length_append, List.length_take, hσ.length, Nat.min_eq_left hwt, ih]
    show wt n σ τ + (n + (List.zipWith (wt n) (τ :: rest) rest).sum)
      = n + (wt n σ τ + (List.zipWith (wt n) (τ :: rest) rest).sum)
    omega

/-- The head vertex's word is a prefix of the walk word. -/
theorem word_prefix_wordOf (hn : 1 ≤ n) :
    ∀ (l : List (List ℕ)) (σ : List ℕ), IsPermWord n σ → (∀ x ∈ l, IsPermWord n x) →
      σ <+: wordOf n (σ :: l)
  | [], σ, _, _ => ⟨[], by simp [wordOf]⟩
  | τ :: rest, σ, hσ, hl => by
    obtain ⟨t, ht⟩ := word_prefix_wordOf hn rest τ (hl τ List.mem_cons_self)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    refine ⟨τ.drop (n - wt n σ τ) ++ t, ?_⟩
    have hover : σ.drop (wt n σ τ) = τ.take (n - wt n σ τ) :=
      (wt_spec (u := σ) (v := τ) hn (le_of_eq hσ.length)).2.2
    show σ ++ (τ.drop (n - wt n σ τ) ++ t) = σ.take (wt n σ τ) ++ wordOf n (τ :: rest)
    calc σ ++ (τ.drop (n - wt n σ τ) ++ t)
        = (σ.take (wt n σ τ) ++ σ.drop (wt n σ τ)) ++ (τ.drop (n - wt n σ τ) ++ t) := by
          rw [List.take_append_drop]
      _ = σ.take (wt n σ τ) ++ (τ.take (n - wt n σ τ) ++ (τ.drop (n - wt n σ τ) ++ t)) := by
          rw [hover, List.append_assoc]
      _ = σ.take (wt n σ τ) ++ (τ ++ t) := by
          rw [← List.append_assoc (τ.take (n - wt n σ τ)), List.take_append_drop]
      _ = σ.take (wt n σ τ) ++ wordOf n (τ :: rest) := by rw [ht]

/-- Every visited vertex's word is a factor of the walk word. -/
theorem word_infix_wordOf (hn : 1 ≤ n) :
    ∀ (l : List (List ℕ)) (v : List ℕ), v ∈ l → (∀ x ∈ l, IsPermWord n x) →
      v <:+: wordOf n l
  | [], v, hv, _ => absurd hv (List.not_mem_nil)
  | σ :: rest, v, hv, hl => by
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact (word_prefix_wordOf hn rest v (hl v List.mem_cons_self)
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))).isInfix
    · rcases rest with _ | ⟨τ, rest'⟩
      · exact absurd hv' (List.not_mem_nil)
      · have ih := word_infix_wordOf hn (τ :: rest') v hv'
          (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        show v <:+: σ.take (wt n σ τ) ++ wordOf n (τ :: rest')
        exact ih.trans (List.suffix_append _ _).isInfix

/-- A concrete (wasteful) superpermutation: the concatenation of all permutation
words.  Witnesses that superpermutations exist for every `n`. -/
noncomputable def trivialSuperperm (n : ℕ) : List ℕ :=
  (refList n).permutations.flatMap id

theorem isSuperperm_trivialSuperperm (n : ℕ) : IsSuperperm n (trivialSuperperm n) := by
  intro v hv
  have hmem : v ∈ (refList n).permutations :=
    List.mem_permutations.mpr (isPermWord_iff_perm_refList.mp hv)
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hmem
  show v <:+: (refList n).permutations.flatMap id
  rw [hl, List.flatMap_append, List.flatMap_cons]
  exact List.infix_append' _ _ _

/-! ## The per-edge defect bound (the induction step of Lemma [lem:hpv]) -/

/-- **Per-edge nonnegativity of the local defect**, for `1 ≤ n`.  (The induction step
behind `defect_nonneg` in `Coeff2/Statements.lean`; the hypothesis is necessary — at
`n = 0` the degenerate two-vertex walk over the empty alphabet has a negative defect.) -/
theorem Walk.defect_nonneg_of_pos {W : Walk n} (hn : 1 ≤ n) {i : ℕ}
    (hi : i + 1 < W.numVerts) : 0 ≤ W.defect i := by
  have hi0 : i < W.numVerts := by omega
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm hi0
  have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi
  have hwt := wt_spec (u := W.vert i) (v := W.vert (i + 1)) hn (le_of_eq hu.length)
  have hdp0 := W.dp_nonneg hi
  have hdp1 := W.dp_le_one hi
  have hdc0 := W.dc_nonneg hi
  have hdc1 := W.dc_le_one hi
  have hdv0 := W.dv_nonneg hi
  have hdv1 := W.dv_le_one hi
  unfold Walk.defect
  rcases Nat.lt_or_ge (wt n (W.vert i) (W.vert (i + 1))) 3 with hw3 | hw3
  · -- weight 1 or 2
    have hsplit : wt n (W.vert i) (W.vert (i + 1)) = 1 ∨
        wt n (W.vert i) (W.vert (i + 1)) = 2 := by omega
    -- in both cases, if `Δc = 1` we find the needed compensation
    by_cases hdc : W.dc i = 1
    · obtain ⟨hfirst, hothers⟩ := W.dc_eq_one_data hi hdc
      rcases hsplit with hw | hw
      · -- weight 1: the target is the rotation, an old vertex; `Δv = 0`
        have hdv : W.dv i = 0 := W.dv_eq_zero_of_wt_one hi (by omega)
        have hrho : W.vert (i + 1) = rho (W.vert i) := eq_rho_of_wt_one hn hu hv hw
        have hdp : W.dp i = 0 := by
          by_cases hself : rho (W.vert i) = W.vert i
          · exact W.dp_eq_zero hi (le_refl i) (by rw [hrho, hself])
          · obtain ⟨s, hs, hsv⟩ := hothers (rho (W.vert i))
              (rotClass_eq_iff.mpr ⟨1, rfl⟩).symm hself
            exact W.dp_eq_zero (s := s) hi (by omega) (by rw [hsv, hrho])
        omega
      · -- weight 2: double rotation (old vertex) or door (loop already entered)
        have hn2 : 2 ≤ n := by omega
        rcases wt_two_word_cases hn2 hu hv (by rw [← hw]; exact hwt.2.2) with hrot | hdoor
        · -- double rotation: an old vertex, `Δp = 0`
          have hdp : W.dp i = 0 := by
            by_cases hself : W.vert (i + 1) = W.vert i
            · exact W.dp_eq_zero hi (le_refl i) hself.symm
            · obtain ⟨s, hs, hsv⟩ := hothers (W.vert (i + 1))
                (by rw [hrot]; exact (rotClass_eq_iff.mpr ⟨2, rfl⟩).symm) hself
              exact W.dp_eq_zero (s := s) hi (by omega) hsv
          omega
        · -- the door: the landing loop `L(door σ) = L(ρσ)` was activated at any
          -- occurrence of `ρσ`, and one occurs at some `s0 < i`; so `Δv = 0`
          have hrhone : rho (W.vert i) ≠ W.vert i := rho_ne_self hn2 hu
          obtain ⟨s0, hs0i, hs0v⟩ := hothers (rho (W.vert i))
            (rotClass_eq_iff.mpr ⟨1, rfl⟩).symm hrhone
          have hact : W.activeLoop s0 = genLoop (rho (W.vert i)) := by
            rcases s0 with _ | t0
            · show genLoop (W.vert 0) = _
              rw [hs0v]
            · by_cases hwt0 : 2 ≤ wt n (W.vert t0) (W.vert (t0 + 1))
              · rw [W.activeLoop_of_two_le_wt hwt0, hs0v]
              · -- a rotation arrival forces an earlier occurrence of `σ` itself
                exfalso
                have ht0 : t0 < W.numVerts := by omega
                have hut0 : IsPermWord n (W.vert t0) := W.vert_isPerm ht0
                have hvt0 : IsPermWord n (W.vert (t0 + 1)) := W.vert_isPerm (by omega)
                have hw1 : wt n (W.vert t0) (W.vert (t0 + 1)) = 1 := by
                  have := (wt_spec (u := W.vert t0) (v := W.vert (t0 + 1)) hn
                    (le_of_eq hut0.length)).1
                  omega
                have hstep := eq_rho_of_wt_one hn hut0 hvt0 hw1
                rw [hs0v] at hstep
                have hsrc : W.vert t0 = W.vert i := by
                  have := List.rotate_injective 1
                    (show (W.vert t0).rotate 1 = (W.vert i).rotate 1 from hstep.symm)
                  exact this
                exact hfirst t0 (by omega) hsrc
          have hloopeq : W.activeLoop (i + 1) = W.activeLoop s0 := by
            rw [W.activeLoop_of_two_le_wt (by omega), hact, hdoor,
              genLoop_door_eq_genLoop_rho hn2 hu]
          have hdv : W.dv i = 0 := by
            rcases W.dv_cases hi with ⟨h, -⟩ | ⟨-, hnone⟩
            · exact h
            · exact absurd hloopeq.symm (hnone s0 (by omega))
          omega
    · -- `Δc = 0`
      have hdc' : W.dc i = 0 := by omega
      rcases hsplit with hw | hw
      · have hdv : W.dv i = 0 := W.dv_eq_zero_of_wt_one hi (by omega)
        omega
      · omega
  · -- weight ≥ 3: the three unit increments cannot exceed it
    omega

/-! ## §5 window machinery: `A₀` accessors and internal-edge facts -/

theorem Walk.A0_isBreak {W : Walk n} {j : ℕ} (hj : j ∈ W.A0Set) : W.IsBreak j := hj.1

theorem Walk.A0_lt_numFE {W : Walk n} {j : ℕ} (hj : j ∈ W.A0Set) : j + 1 < W.numFE :=
  hj.1.1

theorem Walk.A0_not_meetsP {W : Walk n} {j : ℕ} (hj : j ∈ W.A0Set) : ¬ W.MeetsP j :=
  fun h => hj.2 ⟨hj.1, h⟩

theorem Walk.tauIdx_lt_numVerts {W : Walk n} {i : ℕ} (hi : i < W.numFE) :
    W.tauIdx i < W.numVerts := (W.isFirstEntry_tauIdx hi).1

/-- Over an alphabet with at most one symbol there is only one permutation word. -/
theorem eq_of_isPermWord_le_one (hn : n ≤ 1) {u v : List ℕ}
    (hu : IsPermWord n u) (hv : IsPermWord n v) : u = v := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [List.length_eq_zero_iff.mp hu.length, List.length_eq_zero_iff.mp hv.length]
  · have hn1 : n = 1 := by omega
    subst hn1
    have key : ∀ w : List ℕ, IsPermWord 1 w → w = [1] := by
      intro w hw
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hw.ne_nil (le_refl 1))
      have ht : t = [] := by
        have := hw.length
        simp only [List.length_cons] at this
        exact List.length_eq_zero_iff.mp (by omega)
      subst ht
      have ha : a = 1 := by
        have := hw.toFinset_eq
        simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq] at this
        have hmem : a ∈ Finset.Icc 1 1 := by rw [← this]; simp
        simp at hmem
        exact hmem
      rw [ha]
    rw [key u hu, key v hv]

/-- Two distinct first-entered loops force at least two symbols. -/
theorem Walk.two_le_n_of_lt_numFE {W : Walk n} {j : ℕ} (hj : j + 1 < W.numFE) :
    2 ≤ n := by
  by_contra hlt
  push_neg at hlt
  have hj0 : j < W.numFE := by omega
  have hFE1 := W.isFirstEntry_tauIdx hj
  have hFE0 := W.isFirstEntry_tauIdx hj0
  have hltτ : W.tauIdx j < W.tauIdx (j + 1) := W.tauIdx_lt_tauIdx (Nat.lt_succ_self j) hj
  apply hFE1.2 (W.tauIdx j) hltτ
  obtain ⟨s, -, hs2, hs3⟩ := W.activeLoop_eq_genLoop (W.tauIdx j) hFE0.1
  obtain ⟨s', -, hs2', hs3'⟩ := W.activeLoop_eq_genLoop (W.tauIdx (j + 1)) hFE1.1
  rw [hs3, hs3',
    eq_of_isPermWord_le_one (by omega) (W.vert_isPerm hs2) (W.vert_isPerm hs2')]

/-- Every edge in the walk interval of a break `j ∈ A₀` has zero defect. -/
theorem Walk.defect_eq_zero_of_A0 {W : Walk n} (hn : 1 ≤ n) {j i : ℕ}
    (hj : j ∈ W.A0Set) (hia : W.tauIdx j ≤ i) (hib : i < W.tauIdx (j + 1))
    (hi : i + 1 < W.numVerts) : W.defect i = 0 := by
  have hnm := W.A0_not_meetsP hj
  have hle : W.defect i ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    exact hnm ⟨i, ⟨hi, hpos⟩, hia, hib⟩
  have := W.defect_nonneg_of_pos hn hi
  omega

/-- No first-entry time lies strictly between `τ_j` and `τ_{j+1}`. -/
theorem Walk.no_firstEntry_between {W : Walk n} {j t : ℕ}
    (h1 : W.tauIdx j < t) (h2 : t < W.tauIdx (j + 1)) : ¬ W.IsFirstEntryTime t := by
  intro hFE
  have hle : W.tauIdx (j + 1) ≤ t := Nat.sInf_le ⟨hFE, h1⟩
  omega

/-- An internal edge of a break window first-enters no marked 2-loop: `Δv = 0`. -/
theorem Walk.dv_zero_of_internal {W : Walk n} {j i : ℕ}
    (hia : W.tauIdx j ≤ i) (hib : i + 1 < W.tauIdx (j + 1)) (hi : i + 1 < W.numVerts) :
    W.dv i = 0 := by
  rcases W.dv_cases hi with ⟨h, -⟩ | ⟨-, hnone⟩
  · exact h
  · exfalso
    exact W.no_firstEntry_between (by omega) hib
      ⟨hi, fun s hs => hnone s (by omega)⟩

/-- The edge arriving at a first-entry time is not a rotation. -/
theorem Walk.two_le_wt_into_firstEntry {W : Walk n} {t : ℕ}
    (ht : W.IsFirstEntryTime (t + 1)) : 2 ≤ wt n (W.vert t) (W.vert (t + 1)) := by
  by_contra hlt
  apply ht.2 t (Nat.lt_succ_self t)
  show W.activeLoop t = W.activeLoop (t + 1)
  rw [show W.activeLoop (t + 1) =
    (if 2 ≤ wt n (W.vert t) (W.vert (t + 1)) then genLoop (W.vert (t + 1))
      else W.activeLoop t) from rfl, if_neg hlt]

/-- An internal edge whose source rotation class is already completed cannot have zero
defect (the "first paragraph" of Lemma [lem:orbitendclass]). -/
theorem Walk.defect_ne_zero_of_internal_completed {W : Walk n} (hn : 1 ≤ n) {j i : ℕ}
    (hia : W.tauIdx j ≤ i) (hib : i + 1 < W.tauIdx (j + 1)) (hi : i + 1 < W.numVerts)
    (hcomp : (W.pre i).Completed (rotClass (W.vert i))) : W.defect i ≠ 0 := by
  intro h0
  have hi0 : i < W.numVerts := by omega
  have hu : IsPermWord n (W.vert i) := W.vert_isPerm hi0
  have hv : IsPermWord n (W.vert (i + 1)) := W.vert_isPerm hi
  -- `Δc = 0`: the source class is already counted
  have hdc : W.dc i = 0 := by
    by_contra hne
    have hdc1 : W.dc i = 1 := by
      have h1 := W.dc_le_one hi
      have h2 := W.dc_nonneg hi
      omega
    have hfirst := (W.dc_eq_one_data hi hdc1).1
    have hmem := (W.completed_pre_iff hi0 _).mp hcomp (W.vert i) rfl
    obtain ⟨s, hs1, -, hs3⟩ := W.mem_take_vert.mp hmem
    exact hfirst s hs1 hs3
  have hdv : W.dv i = 0 := W.dv_zero_of_internal hia hib hi
  have hdp0 := W.dp_nonneg hi
  have hdp1 := W.dp_le_one hi
  have hw1 : 1 ≤ wt n (W.vert i) (W.vert (i + 1)) :=
    (wt_spec hn (le_of_eq hu.length) (v := W.vert (i + 1))).1
  -- from `d_i = 0`: `w = Δp ≤ 1`, so `w = 1` and the target is the rotation…
  have hweq : wt n (W.vert i) (W.vert (i + 1)) = 1 := by
    unfold Walk.defect at h0
    omega
  -- …but the rotation was already visited, so `Δp = 0` and `d_i = 1`.
  have hrho := eq_rho_of_wt_one hn hu hv hweq
  have hmem := (W.completed_pre_iff hi0 _).mp hcomp (rho (W.vert i))
    (rotClass_eq_iff.mpr ⟨1, rfl⟩).symm
  obtain ⟨s, hs1, -, hs3⟩ := W.mem_take_vert.mp hmem
  have hdp : W.dp i = 0 := W.dp_eq_zero (s := s) hi (by omega) (by rw [hs3, hrho])
  unfold Walk.defect at h0
  omega

/-- If `σ ∈ V(L)` and the door out of `σ` ends in the marker of `L`, the door lands in
`L` itself (the deleted words are cyclically equivalent; §5, proof of
Lemma [lem:orbitendclass]). -/
theorem genLoop_door_of_getLastD (hn : 2 ≤ n) {σ : List ℕ} {L : MarkedLoop}
    (hσ : IsPermWord n σ) (hσL : σ ∈ V n L) (hlast : (door σ).getLastD 0 = L.1) :
    genLoop (door σ) = L := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hσ.ne_nil (by omega))
  obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
    rcases t with _ | ⟨b, s⟩
    · have := hσ.length; simp at this; omega
    · exact ⟨b, s, rfl⟩
  have hdoor : door (a :: b :: s) = (s ++ [b]) ++ [a] := by
    show (a :: b :: s).drop 2 ++ [(a :: b :: s).getD 1 0, (a :: b :: s).getD 0 0] = _
    simp
  rw [hdoor, List.getLastD_concat] at hlast
  have hclass : rotClass (b :: s) = L.2 := by
    have h2 := hσL.2
    rw [← hlast] at h2
    rwa [List.erase_cons_head] at h2
  rw [hdoor]
  refine Prod.ext ?_ ?_
  · show ((s ++ [b]) ++ [a]).getLastD 0 = L.1
    rw [List.getLastD_concat]
    exact hlast
  · show rotClass ((s ++ [b]) ++ [a]).dropLast = L.2
    rw [List.dropLast_concat, ← hclass]
    exact Quotient.sound (List.IsRotated.symm ⟨1, by simp⟩)

/-! ## The canonical ride: word-level toolkit (for Lemma [lem:pinned]) -/

/-- Each ride anchor is a permutation word (`n ≥ 2`). -/
theorem isPermWord_rideAnchor (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x) (h : ℕ) :
    IsPermWord n (rideAnchor n x h) := by
  rw [rideAnchor_eq_all hn hx h]
  have hxeq : x = x.erase (x.getLastD 0) ++ [x.getLastD 0] := by
    rw [erase_getLastD hx.nodup]
    rcases List.eq_nil_or_concat x with h0 | ⟨l, b, h0⟩
    · exact absurd h0 (hx.ne_nil (by omega))
    · rw [h0, List.concat_eq_append, List.dropLast_concat, List.getLastD_concat]
  have hperm : (x.erase (x.getLastD 0)).rotate h ++ [x.getLastD 0] ~ x := by
    conv_rhs => rw [hxeq]
    exact (List.rotate_perm _ h).append_right _
  exact isPermWord_iff_perm_refList.mpr
    (hperm.trans (isPermWord_iff_perm_refList.mp hx))

/-- Every ride vertex is a permutation word. -/
theorem isPermWord_ride (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x) (h r : ℕ) :
    IsPermWord n (ride n x h r) :=
  isPermWord_rotate (isPermWord_rideAnchor hn hx h) r

/-- Every ride vertex lies in the marked 2-loop generated by the entry vertex. -/
theorem ride_mem_V (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x) (h r : ℕ) :
    ride n x h r ∈ V n (genLoop x) := by
  have hanchor : rideAnchor n x h ∈ V n (genLoop x) := by
    refine ⟨isPermWord_rideAnchor hn hx h, ?_⟩
    show rotClass ((rideAnchor n x h).erase (x.getLastD 0)) = rotClass x.dropLast
    have hα : x.getLastD 0 ∉ (x.erase (x.getLastD 0)).rotate h := by
      intro hmem
      have h2 := (List.rotate_perm _ h).mem_iff.mp hmem
      exact ((hx.nodup.mem_erase_iff).mp h2).1 rfl
    rw [rideAnchor_eq_all hn hx h, List.erase_append_right _ hα,
      List.erase_cons_head, List.append_nil, erase_getLastD hx.nodup]
    exact (rotClass_eq_iff.mpr ⟨h, rfl⟩).symm
  exact V_closed_rotate _ hanchor r

/-- The rotation class of a ride vertex is that of its anchor. -/
theorem rotClass_ride (n : ℕ) (x : List ℕ) (h r : ℕ) :
    rotClass (ride n x h r) = rotClass (rideAnchor n x h) :=
  (rotClass_eq_iff.mpr ⟨r, rfl⟩).symm

/-- The first `n−1` ride anchors have pairwise distinct rotation classes (each ride
orbit contains a unique marker-last vertex). -/
theorem rotClass_rideAnchor_ne (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x)
    {h h' : ℕ} (hh : h < n - 1) (hh' : h' < n - 1) (hne : h ≠ h') :
    rotClass (rideAnchor n x h) ≠ rotClass (rideAnchor n x h') := by
  intro hcon
  obtain ⟨l, b, rfl⟩ : ∃ l b, x = l ++ [b] := by
    rcases List.eq_nil_or_concat x with h0 | ⟨l, b, h0⟩
    · exact absurd h0 (hx.ne_nil (by omega))
    · exact ⟨l, b, by rw [h0, List.concat_eq_append]⟩
  have herase : (l ++ [b]).erase ((l ++ [b]).getLastD 0) = l := by
    rw [erase_getLastD hx.nodup, List.dropLast_concat]
  rw [rideAnchor_eq_all hn hx h, rideAnchor_eq_all hn hx h', herase,
    List.getLastD_concat] at hcon
  have hllen : l.length = n - 1 := by
    have := hx.length
    simp at this
    omega
  have hnd := hx.nodup
  rw [List.nodup_append] at hnd
  have hbl : b ∉ l := fun hb => hnd.2.2 b hb b (List.mem_singleton_self b) rfl
  have hndrot : (l.rotate h ++ [b]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.rotate_perm l h).nodup_iff.mpr hnd.1, List.nodup_singleton b, ?_⟩
    intro y hy z hz
    rw [List.mem_singleton] at hz
    subst hz
    intro hyb
    exact hbl ((List.rotate_perm l h).mem_iff.mp (hyb ▸ hy))
  have heq : l.rotate h = l.rotate h' :=
    isRotated_concat_inj hndrot (rotClass_eq_iff.mp hcon)
  exact hne (rotate_injOn_lt hnd.1 (by omega) (by omega) heq)

/-- Ride vertices with in-range indices are pairwise distinct words. -/
theorem ride_word_inj (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x)
    {h r h' r' : ℕ} (hh : h < n - 1) (hh' : h' < n - 1) (hr : r < n) (hr' : r' < n)
    (heq : ride n x h r = ride n x h' r') : h = h' ∧ r = r' := by
  have hhe : h = h' := by
    by_contra hne
    exact rotClass_rideAnchor_ne hn hx hh hh' hne
      (by rw [← rotClass_ride n x h r, ← rotClass_ride n x h' r', heq])
  subst hhe
  refine ⟨rfl, ?_⟩
  have hnd : (rideAnchor n x h).Nodup := (isPermWord_rideAnchor hn hx h).nodup
  have hlen : (rideAnchor n x h).length = n := (isPermWord_rideAnchor hn hx h).length
  exact rotate_injOn_lt hnd (by rw [hlen]; exact hr) (by rw [hlen]; exact hr') heq

/-- One rotation step along a ride orbit. -/
theorem rho_ride (n : ℕ) (x : List ℕ) (h r : ℕ) :
    rho (ride n x h r) = ride n x h (r + 1) := by
  show (ride n x h r).rotate 1 = _
  rw [ride, ride, List.rotate_rotate]

/-- The rotation out of the last vertex of a ride orbit closes the orbit back to its
anchor. -/
theorem rho_ride_top (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x) (h : ℕ) :
    rho (ride n x h (n - 1)) = rideAnchor n x h := by
  rw [rho_ride]
  show (rideAnchor n x h).rotate (n - 1 + 1) = rideAnchor n x h
  have hlen : (rideAnchor n x h).length = n := (isPermWord_rideAnchor hn hx h).length
  have h2 : (rideAnchor n x h).rotate n = rideAnchor n x h := by
    have h3 := List.rotate_length (rideAnchor n x h)
    rwa [hlen] at h3
  rw [show n - 1 + 1 = n from by omega]
  exact h2

/-- The door out of the last vertex of a ride orbit lands at the next anchor
(definitional). -/
theorem door_ride_top (n : ℕ) (x : List ℕ) (h : ℕ) :
    door (ride n x h (n - 1)) = rideAnchor n x (h + 1) := rfl

/-- The anchor sequence wraps: `R_{n−1,0} = x`. -/
theorem rideAnchor_wrap (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x) :
    rideAnchor n x (n - 1) = x := by
  rw [rideAnchor_eq_all hn hx]
  have hlen : (x.erase (x.getLastD 0)).length = n - 1 := by
    rw [erase_getLastD hx.nodup, List.length_dropLast, hx.length]
  have h2 : (x.erase (x.getLastD 0)).rotate (n - 1) = x.erase (x.getLastD 0) := by
    have h3 := List.rotate_length (x.erase (x.getLastD 0))
    rwa [hlen] at h3
  rw [h2, erase_getLastD hx.nodup]
  rcases List.eq_nil_or_concat x with h0 | ⟨l, b, h0⟩
  · exact absurd h0 (hx.ne_nil (by omega))
  · rw [h0, List.concat_eq_append, List.dropLast_concat, List.getLastD_concat]

/-- Every member of a ride-orbit rotation class is a ride vertex of that orbit. -/
theorem exists_ride_of_rotClass (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x)
    {w : List ℕ} {h : ℕ} (hw : rotClass w = rotClass (rideAnchor n x h)) :
    ∃ r < n, w = ride n x h r := by
  obtain ⟨k, hk⟩ := rotClass_eq_iff.mp hw.symm
  have hlen : (rideAnchor n x h).length = n := (isPermWord_rideAnchor hn hx h).length
  refine ⟨k % n, Nat.mod_lt _ (by omega), ?_⟩
  have hmod := List.rotate_mod (rideAnchor n x h) k
  rw [hlen] at hmod
  show w = (rideAnchor n x h).rotate (k % n)
  rw [← hk, ← hmod]

/-- Division of a block offset: `(hn + k)/n = h` for `k < n`. -/
theorem mul_add_div_eq (hn : 0 < n) (h : ℕ) {k : ℕ} (hk : k < n) :
    (h * n + k) / n = h := by
  rw [show h * n + k = k + h * n from by omega,
    Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk]
  omega

/-- Remainder of a block offset: `(hn + k) % n = k` for `k < n`. -/
theorem mul_add_mod_eq (hn : 0 < n) (h : ℕ) {k : ℕ} (hk : k < n) :
    (h * n + k) % n = k := by
  rw [show h * n + k = k + h * n from by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/-- **The mid-orbit pinning step** (§5, Lemma [lem:pinned], case `r < n−1`): if the
window at `j ∈ A₀` is fresh and pinned to the canonical ride through offset
`o = hn + r` with `r < n−1`, and offset `o+1` is still internal, then the next edge is
forced to be the rotation, pinning offset `o+1`. -/
theorem Walk.midorbit_next {W : Walk n} {j : ℕ} (hj : j ∈ W.A0Set)
    (hfresh : W.FreshWindow j) {o h r : ℕ} (ho : o = h * n + r) (hr : r < n - 1)
    (hh : h < n - 1) (hib : W.tauIdx j + o + 1 < W.tauIdx (j + 1))
    (hpin : ∀ m ≤ o, W.vert (W.tauIdx j + m) = ride n (W.xEntry j) (m / n) (m % n)) :
    W.vert (W.tauIdx j + o + 1) = ride n (W.xEntry j) h (r + 1) := by
  have hj1 : j + 1 < W.numFE := W.A0_lt_numFE hj
  have hn2 : 2 ≤ n := W.two_le_n_of_lt_numFE hj1
  have hb : W.tauIdx (j + 1) < W.numVerts := W.tauIdx_lt_numVerts hj1
  have hτ : W.tauIdx j < W.numVerts := W.tauIdx_lt_numVerts (by omega)
  have hx : IsPermWord n (W.xEntry j) := W.vert_isPerm hτ
  have hor : o = r + h * n := by omega
  have hdiv : o / n = h := by
    rw [hor, Nat.add_mul_div_right _ _ (by omega : 0 < n),
      Nat.div_eq_of_lt (by omega)]
    omega
  have hmod : o % n = r := by
    rw [hor, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hσ : W.vert (W.tauIdx j + o) = ride n (W.xEntry j) h r := by
    have h2 := hpin o (le_refl o)
    rwa [hdiv, hmod] at h2
  have hi1 : W.tauIdx j + o + 1 < W.numVerts := by omega
  have hd : W.defect (W.tauIdx j + o) = 0 :=
    W.defect_eq_zero_of_A0 (by omega) hj (by omega) (by omega) hi1
  have hdv : W.dv (W.tauIdx j + o) = 0 :=
    W.dv_zero_of_internal (by omega) hib hi1
  -- `Δc = 0`: the top rotation of the current orbit has not appeared yet
  have hdc : W.dc (W.tauIdx j + o) = 0 := by
    by_contra hne
    have hdc1 : W.dc (W.tauIdx j + o) = 1 := by
      have h1 := W.dc_le_one hi1
      have h2 := W.dc_nonneg hi1
      omega
    obtain ⟨-, hothers⟩ := W.dc_eq_one_data hi1 hdc1
    have hlast_ne : ride n (W.xEntry j) h (n - 1) ≠ W.vert (W.tauIdx j + o) := by
      rw [hσ]
      intro hcon
      have := ride_word_inj hn2 hx hh hh (by omega) (by omega) hcon
      omega
    have hcls : rotClass (ride n (W.xEntry j) h (n - 1)) =
        rotClass (W.vert (W.tauIdx j + o)) := by
      rw [hσ, rotClass_ride, rotClass_ride]
    obtain ⟨s, hs, hsv⟩ := hothers _ hcls hlast_ne
    rcases Nat.lt_or_ge s (W.tauIdx j) with hsa | hsa
    · -- before the window: freshness is violated
      have hEfe : W.Efe j = genLoop (W.xEntry j) :=
        W.activeLoop_firstEntry _ (W.isFirstEntry_tauIdx (by omega))
      apply hfresh s hsa
      rw [hEfe, hsv]
      exact ride_mem_V hn2 hx h (n - 1)
    · -- inside the window: contradicts the pinned prefix
      have hm : s - W.tauIdx j ≤ o := by omega
      have hpins := hpin (s - W.tauIdx j) hm
      rw [show W.tauIdx j + (s - W.tauIdx j) = s from by omega] at hpins
      rw [hpins] at hsv
      have hbridge : (h + 1) * n = h * n + n := by ring
      have hle : (h + 1) * n ≤ n * (n - 1) := by
        have h4 := Nat.mul_le_mul_right n (show h + 1 ≤ n - 1 by omega)
        rwa [Nat.mul_comm (n - 1) n] at h4
      have hslt : s - W.tauIdx j < n * (n - 1) := by omega
      have hh2 : (s - W.tauIdx j) / n < n - 1 := Nat.div_lt_of_lt_mul hslt
      obtain ⟨heqh, heqr⟩ := ride_word_inj hn2 hx hh2 hh
        (Nat.mod_lt _ (by omega)) (by omega) hsv
      have hdm := Nat.div_add_mod (s - W.tauIdx j) n
      rw [heqh, heqr, Nat.mul_comm n h] at hdm
      omega
  -- zero defect now forces weight 1: the rotation pins the next offset
  have hu : IsPermWord n (W.vert (W.tauIdx j + o)) := W.vert_isPerm (by omega)
  have hv : IsPermWord n (W.vert (W.tauIdx j + o + 1)) := W.vert_isPerm hi1
  have hw1 : 1 ≤ wt n (W.vert (W.tauIdx j + o)) (W.vert (W.tauIdx j + o + 1)) :=
    (wt_spec (u := W.vert (W.tauIdx j + o)) (v := W.vert (W.tauIdx j + o + 1))
      (by omega) (le_of_eq hu.length)).1
  have hdp0 := W.dp_nonneg hi1
  have hdp1 := W.dp_le_one hi1
  have hweq : wt n (W.vert (W.tauIdx j + o)) (W.vert (W.tauIdx j + o + 1)) = 1 := by
    unfold Walk.defect at hd
    omega
  rw [eq_rho_of_wt_one (by omega) hu hv hweq, hσ, rho_ride]

/-- The prefix-sum form of the monovariant: `Σ_{i<t} d_i ≥ 0` for `1 ≤ n`. -/
theorem Walk.defect_sum_nonneg_of_pos {W : Walk n} (hn : 1 ≤ n) (t : ℕ)
    (ht : t ≤ W.numVerts - 1) : 0 ≤ ∑ i ∈ Finset.range t, W.defect i := by
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_range] at hi
  have := W.numVerts_pos
  exact W.defect_nonneg_of_pos hn (by omega)

/-- The telescoped defect sum equals the prefix excess (the inner computation of
`defect_sum` in `Coeff2/Statements.lean`, restated here so that the monovariant can be
proved below it in the import order). -/
theorem Walk.defect_sum_pre (W : Walk n) (t : ℕ) (ht : t < W.numVerts) :
    ∑ i ∈ Finset.range t, W.defect i
      = ((W.pre t).wtW : ℤ) + 2 -
          (((W.pre t).pStat : ℤ) + ((W.pre t).cStat : ℤ) + ((W.pre t).vStat : ℤ)) := by
  induction t with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, W.wtW_pre_zero, W.pStat_pre_zero,
      W.cStat_pre_zero, W.vStat_pre_zero]
    norm_num
  | succ t ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    unfold Walk.defect Walk.dp Walk.dc Walk.dv
    rw [W.wtW_pre_succ ht]
    push_cast
    ring

/-- **The HPV monovariant** for `1 ≤ n`: `p + c + v ≤ wt(W) + 2` (display (1)); proof
content of `hpv_monovariant` in `Coeff2/Statements.lean`. -/
theorem Walk.monovariant_of_pos (hn : 1 ≤ n) (W : Walk n) :
    W.pStat + W.cStat + W.vStat ≤ W.wtW + 2 := by
  have hpos := W.numVerts_pos
  have hsum := W.defect_sum_pre (W.numVerts - 1) (by omega)
  have hnonneg := W.defect_sum_nonneg_of_pos hn (W.numVerts - 1) (le_refl _)
  rw [hsum, W.wtW_pre_last, W.pStat_pre_last, W.cStat_pre_last, W.vStat_pre_last]
    at hnonneg
  omega

/-- The weight defect is the total local defect (`Σ dᵢ = e(W)`, restated here below
the telescoping so that the corrected display (4) can be proved in this file). -/
theorem Walk.eStat_eq_defect_sum (W : Walk n) :
    W.eStat = ∑ i ∈ Finset.range (W.numVerts - 1), W.defect i := by
  have hpos := W.numVerts_pos
  have h := W.defect_sum_pre (W.numVerts - 1) (by omega)
  rw [h, W.wtW_pre_last, W.pStat_pre_last, W.cStat_pre_last, W.vStat_pre_last]
  unfold Walk.eStat
  push_cast
  ring

/-- **Display (4) in unbundled form**: `|P| ≤ e(W)` for `1 ≤ n` (the hypothesis is
necessary at `n = 0`).  The coefficient-2 chain (`twoparam` → `criterion` → …)
consumes this version. -/
theorem Walk.pset_ncard_le_eStat (hn : 1 ≤ n) (W : Walk n) :
    (W.Pset.ncard : ℤ) ≤ W.eStat := by
  classical
  have hPeq : W.Pset =
      ↑((Finset.range (W.numVerts - 1)).filter (fun i => 0 < W.defect i)) := by
    ext i
    simp only [Walk.Pset, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  rw [hPeq, Set.ncard_coe_finset, W.eStat_eq_defect_sum]
  calc (((Finset.range (W.numVerts - 1)).filter (fun i => 0 < W.defect i)).card : ℤ)
      = ∑ _i ∈ (Finset.range (W.numVerts - 1)).filter (fun i => 0 < W.defect i),
          (1 : ℤ) := by simp
    _ ≤ ∑ i ∈ (Finset.range (W.numVerts - 1)).filter (fun i => 0 < W.defect i),
          W.defect i :=
        Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_filter] at hi
          omega)
    _ ≤ ∑ i ∈ Finset.range (W.numVerts - 1), W.defect i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi _ => by
            rw [Finset.mem_range] at hi
            exact W.defect_nonneg_of_pos hn (by omega))

end Coeff2
