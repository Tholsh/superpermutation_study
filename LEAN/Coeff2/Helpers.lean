/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Defs

/-!
# Auxiliary lemmas (not statements of the paper)

Helper facts used by the proofs in `Coeff2/Statements.lean`.
-/

namespace Coeff2

open List

/-- Ceiling-division characterization: for `b > 0`, `k < ⌈a/b⌉ ↔ k·b < a`. -/
lemma lt_ceilDiv_iff {a b k : ℕ} (hb : 0 < b) : k < a ⌈/⌉ b ↔ k * b < a := by
  rw [← not_le, ceilDiv_le_iff_le_mul hb, not_le, Nat.mul_comm]

/-! The helper `covering_walk_exists` (covering walks exist, so that `Λ(n)` is the
minimum of a nonempty set) now lives in `Coeff2/Auxiliary.lean`, where the
edge-refinement machinery needed to build one is available. -/

/-! ## Permutation-word basics -/

theorem IsPermWord.nodup {n : ℕ} {w : List ℕ} (h : IsPermWord n w) : w.Nodup := h.1

theorem IsPermWord.toFinset_eq {n : ℕ} {w : List ℕ} (h : IsPermWord n w) :
    w.toFinset = Finset.Icc 1 n := h.2

theorem IsPermWord.length {n : ℕ} {w : List ℕ} (h : IsPermWord n w) : w.length = n := by
  have h1 := List.toFinset_card_of_nodup h.1
  rw [h.2, Nat.card_Icc] at h1
  omega

theorem IsPermWord.ne_nil {n : ℕ} {w : List ℕ} (h : IsPermWord n w) (hn : 1 ≤ n) :
    w ≠ [] := by
  intro hw
  have hlen := h.length
  rw [hw] at hlen
  simp at hlen
  omega

theorem isPermWord_rotate {n : ℕ} {w : List ℕ} (h : IsPermWord n w) (k : ℕ) :
    IsPermWord n (w.rotate k) := by
  refine ⟨(List.rotate_perm w k).nodup_iff.mpr h.1, ?_⟩
  rw [List.toFinset_eq_of_perm _ _ (List.rotate_perm w k), h.2]

theorem isPermWord_of_isRotated {n : ℕ} {w w' : List ℕ} (h : IsPermWord n w)
    (hr : w ~r w') : IsPermWord n w' := by
  obtain ⟨k, rfl⟩ := hr
  exact isPermWord_rotate h k

/-- Deleting the last symbol of a duplicate-free word: `erase` at the last symbol is
`dropLast`. -/
theorem erase_getLastD {w : List ℕ} (hw : w.Nodup) :
    w.erase (w.getLastD 0) = w.dropLast := by
  rcases List.eq_nil_or_concat w with rfl | ⟨l, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append] at hw ⊢
    have hal : a ∉ l := by
      rw [List.nodup_append] at hw
      intro ha
      exact hw.2.2 a ha a (List.mem_singleton_self a) rfl
    rw [List.getLastD_concat, List.erase_append_right _ hal, List.erase_cons_head,
      List.append_nil, List.dropLast_concat]

/-! ## Weight basics -/

theorem wt_spec {n : ℕ} {u v : List ℕ} (hn : 1 ≤ n) (hu : u.length ≤ n) :
    1 ≤ wt n u v ∧ wt n u v ≤ n ∧
      u.drop (wt n u v) = v.take (n - wt n u v) :=
  Nat.sInf_mem (⟨n, hn, le_refl n, by simp [List.drop_eq_nil_of_le hu]⟩ :
    {d | 1 ≤ d ∧ d ≤ n ∧ u.drop d = v.take (n - d)}.Nonempty)

theorem wt_le {n : ℕ} {u v : List ℕ} {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ n)
    (h3 : u.drop d = v.take (n - d)) : wt n u v ≤ d :=
  Nat.sInf_le ⟨h1, h2, h3⟩

/-- The rotation has weight 1. -/
theorem wt_rho {n : ℕ} {u : List ℕ} (hn : 1 ≤ n) (hu : IsPermWord n u) :
    wt n u (rho u) = 1 := by
  have hlen : u.length = n := hu.length
  have h1 : u.drop 1 = (rho u).take (n - 1) := by
    rw [rho, List.rotate_eq_drop_append_take (by omega),
      List.take_left' (by rw [List.length_drop]; omega)]
  have h2 := wt_le (le_refl 1) (by omega) h1
  have h3 := (wt_spec (u := u) (v := rho u) hn (by omega)).1
  omega

/-- A weight-1 edge between permutation words is the rotation: `wt(u,v) = 1 → v = ρ(u)`. -/
theorem eq_rho_of_wt_one {n : ℕ} {u v : List ℕ} (hn : 1 ≤ n) (hu : IsPermWord n u)
    (hv : IsPermWord n v) (h : wt n u v = 1) : v = rho u := by
  have hspec := (wt_spec hn (le_of_eq hu.length) (v := v)).2.2
  rw [h] at hspec
  have hvlen := hv.length
  have hulen := hu.length
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hu.ne_nil hn)
  have hdrop : (a :: t).drop 1 = t := rfl
  rw [hdrop] at hspec
  obtain ⟨z, hz⟩ : ∃ z, v.drop (n - 1) = [z] := by
    apply List.length_eq_one_iff.mp
    rw [List.length_drop]
    omega
  have hveq : v = t ++ [z] := by
    conv_lhs => rw [← List.take_append_drop (n - 1) v]
    rw [hz, ← hspec]
  have htlen : t.length = n - 1 := by
    have := hulen
    simp only [List.length_cons] at this
    omega
  have hza : z = a := by
    have hzIcc : z ∈ Finset.Icc 1 n := by
      rw [← hv.toFinset_eq]
      rw [hveq]
      simp
    have huIcc : (a :: t).toFinset = Finset.Icc 1 n := hu.toFinset_eq
    rw [List.toFinset_cons] at huIcc
    rw [← huIcc, Finset.mem_insert] at hzIcc
    rcases hzIcc with h1 | h1
    · exact h1
    · exfalso
      have hvnd := hv.nodup
      rw [hveq] at hvnd
      rw [List.nodup_append] at hvnd
      rw [List.mem_toFinset] at h1
      exact hvnd.2.2 z h1 z (List.mem_singleton_self z) rfl
  rw [hveq, hza]
  show t ++ [a] = (a :: t).rotate 1
  simp

/-! ## Rotation classes and `V(L)` -/

theorem rotClass_eq_iff {w w' : List ℕ} : rotClass w = rotClass w' ↔ w ~r w' := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem V_closed_rotate {n : ℕ} (L : MarkedLoop) {σ : List ℕ} (hσ : σ ∈ V n L)
    (k : ℕ) : σ.rotate k ∈ V n L := by
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
    obtain ⟨hperm, hcls⟩ := ih
    refine ⟨isPermWord_rotate (n := n) hσ.1 (k + 1), ?_⟩
    rw [← hcls]
    apply Quotient.sound
    have hrot : σ.rotate (k + 1) = (σ.rotate k).rotate 1 := by
      rw [List.rotate_rotate]
    rw [hrot]
    generalize σ.rotate k = y at hperm
    rcases y with _ | ⟨a, t⟩
    · simp
    · have hy : (a :: t).rotate 1 = t ++ [a] := by simp
      rw [hy]
      by_cases hα : L.1 = a
      · subst hα
        have hat : L.1 ∉ t := (List.nodup_cons.mp hperm.1).1
        rw [List.erase_append_right _ hat, List.erase_cons_head, List.append_nil,
          List.erase_cons_head]
      · by_cases hmem : L.1 ∈ t
        · rw [List.erase_append_left _ hmem,
            List.erase_cons_tail (by simpa using Ne.symm hα)]
          exact List.IsRotated.symm
            (⟨1, by simp⟩ : (a :: t.erase L.1) ~r (t.erase L.1 ++ [a]))
        · have h1 : (t ++ [a]).erase L.1 = t ++ [a] := by
            apply List.erase_of_not_mem
            simp only [List.mem_append, List.mem_singleton]
            rintro (h | h)
            · exact hmem h
            · exact hα h
          have h2 : (a :: t).erase L.1 = a :: t := by
            apply List.erase_of_not_mem
            simp only [List.mem_cons]
            rintro (h | h)
            · exact hα h
            · exact hmem h
          rw [h1, h2]
          exact List.IsRotated.symm (⟨1, by simp⟩ : (a :: t) ~r (t ++ [a]))

/-! ## Counting permutation words -/

/-- The reference listing of `[n]`: `1, 2, …, n` in increasing order. -/
def refList (n : ℕ) : List ℕ := (Finset.Icc 1 n).sort (· ≤ ·)

theorem refList_nodup (n : ℕ) : (refList n).Nodup := (Finset.Icc 1 n).sort_nodup _

theorem refList_toFinset (n : ℕ) : (refList n).toFinset = Finset.Icc 1 n :=
  (Finset.Icc 1 n).sort_toFinset _

theorem refList_length (n : ℕ) : (refList n).length = n := by
  rw [refList, Finset.length_sort, Nat.card_Icc]
  omega

theorem isPermWord_iff_perm_refList {n : ℕ} {w : List ℕ} :
    IsPermWord n w ↔ w ~ refList n := by
  constructor
  · intro h
    exact List.perm_of_nodup_nodup_toFinset_eq h.1 (refList_nodup n)
      (by rw [h.2, refList_toFinset])
  · intro h
    exact ⟨h.nodup_iff.mpr (refList_nodup n),
      by rw [List.toFinset_eq_of_perm _ _ h, refList_toFinset]⟩

/-- There are exactly `n!` permutation words of `[n]`. -/
theorem ncard_permWords (n : ℕ) : {w | IsPermWord n w}.ncard = n.factorial := by
  have hset : {w | IsPermWord n w} = ↑((refList n).permutations.toFinset) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset,
      List.mem_permutations]
    exact isPermWord_iff_perm_refList
  rw [hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (List.nodup_permutations _ (refList_nodup n)),
    List.length_permutations, refList_length]

/-! ## The successor map and the ride: one-step computations -/

/-- Rotating a word `u ++ [α]` of length `n` by `n−1` brings the last symbol to the
front. -/
theorem rotate_last {n : ℕ} (u : List ℕ) (α : ℕ) (hu : u.length = n - 1) :
    (u ++ [α]).rotate (n - 1) = α :: u := by
  rw [List.rotate_eq_drop_append_take
      (by simp only [List.length_append, hu, List.length_cons, List.length_nil]; omega),
    List.drop_left' hu, List.take_left' hu]
  rfl

/-- One step of the successor map on words of the shape `(c :: T') ++ [b, α]`
(first `n−2` symbols, then the fixed symbol `b`, then the marker `α`):
`M` rotates the first `n−2` symbols one step left. -/
theorem msucc_step {n : ℕ} (c b α : ℕ) (T' : List ℕ)
    (hlen : (c :: T').length = n - 2) (hnd : ((c :: T') ++ [b, α]).Nodup) :
    Msucc n ((c :: T') ++ [b, α]) = (T' ++ [c]) ++ [b, α] := by
  have hsplit : (c :: T') ++ [b, α] = ((c :: T') ++ [b]) ++ [α] := by simp
  have hgl : ((c :: T') ++ [b, α]).getLastD 0 = α := by
    rw [hsplit]; exact List.getLastD_concat
  have herase : ((c :: T') ++ [b, α]).erase α = (c :: T') ++ [b] := by
    have h1 := erase_getLastD hnd
    rw [hgl] at h1
    rw [h1, hsplit, List.dropLast_concat]
  have hblen : ((c :: T') ++ [b]).length = (n - 2) + 1 := by
    simp only [List.length_append, hlen, List.length_cons, List.length_nil]
  have hrot : ((c :: T') ++ [b]).rotate (n - 2) = b :: c :: T' := by
    rw [List.rotate_eq_drop_append_take (by omega),
      List.drop_left' hlen, List.take_left' hlen]
    rfl
  simp only [Msucc, hgl, herase, hrot]
  simp [List.getD]

/-- One step of the ride-anchor recursion on words of the shape `u ++ [α]`:
the next anchor rotates `u` one step left. -/
theorem door_anchor {n : ℕ} (u : List ℕ) (α : ℕ) (hu : u.length = n - 1)
    (hune : u ≠ []) :
    door ((u ++ [α]).rotate (n - 1)) = u.rotate 1 ++ [α] := by
  rw [rotate_last u α hu]
  obtain ⟨c, T', rfl⟩ := List.exists_cons_of_ne_nil hune
  rw [door]
  simp [List.getD]

/-- The anchor formula for the canonical ride: `R_{h,0} = u^{(h)} α` for every `h`,
where `u = del_α(x)` (paper §4; here proved for all `h`). -/
theorem rideAnchor_eq_all {n : ℕ} (hn : 2 ≤ n) {x : List ℕ} (hx : IsPermWord n x)
    (h : ℕ) :
    rideAnchor n x h = ((x.erase (x.getLastD 0)).rotate h) ++ [x.getLastD 0] := by
  have hxne : x ≠ [] := hx.ne_nil (by omega)
  have hu : (x.erase (x.getLastD 0)).length = n - 1 := by
    rw [erase_getLastD hx.nodup, List.length_dropLast, hx.length]
  have hxeq : x = x.erase (x.getLastD 0) ++ [x.getLastD 0] := by
    rw [erase_getLastD hx.nodup]
    rcases List.eq_nil_or_concat x with h0 | ⟨l, a, h0⟩
    · exact absurd h0 hxne
    · rw [h0, List.concat_eq_append, List.dropLast_concat, List.getLastD_concat]
  induction h with
  | zero => rw [List.rotate_zero, rideAnchor, ← hxeq]
  | succ h ih =>
    rw [rideAnchor, ih, door_anchor _ _ (by rw [List.length_rotate]; exact hu)
        (by intro h0; rw [← List.length_eq_zero_iff, List.length_rotate] at h0; omega),
      List.rotate_rotate]

end Coeff2

namespace Coeff2

open List

/-! ## Prefix walks: vertices, membership, completed classes -/

theorem Walk.vert_eq_getElem {n : ℕ} (W : Walk n) {t : ℕ} (ht : t < W.numVerts) :
    W.vert t = W.verts[t]'ht :=
  List.getD_eq_getElem _ _ ht

theorem Walk.take_succ_vert {n : ℕ} (W : Walk n) {t : ℕ} (ht : t < W.numVerts) :
    W.verts.take (t + 1) = W.verts.take t ++ [W.vert t] := by
  rw [List.take_succ, List.getElem?_eq_getElem ht, W.vert_eq_getElem ht]
  rfl

theorem Walk.mem_take_vert {n : ℕ} (W : Walk n) {w : List ℕ} {t : ℕ} :
    w ∈ W.verts.take t ↔ ∃ s, s < t ∧ s < W.numVerts ∧ W.vert s = w := by
  constructor
  · intro h
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem h
    have hilen : i < min t W.verts.length := by
      rw [← List.length_take]; exact hi
    have hi1 : i < t := lt_of_lt_of_le hilen (min_le_left _ _)
    have hi2 : i < W.numVerts := lt_of_lt_of_le hilen (min_le_right _ _)
    refine ⟨i, hi1, hi2, ?_⟩
    rw [W.vert_eq_getElem hi2, ← hiw, List.getElem_take]
    rfl
  · rintro ⟨s, hst, hsm, rfl⟩
    have hs' : s < (W.verts.take t).length := by
      rw [List.length_take]
      have hsl : s < W.verts.length := hsm
      omega
    have hmem := List.getElem_mem hs'
    have heq : (W.verts.take t)[s]'hs' = W.vert s := by
      rw [List.getElem_take]
      exact (W.vert_eq_getElem hsm).symm
    rwa [heq] at hmem

theorem Walk.completed_pre_iff {n : ℕ} (W : Walk n) {t : ℕ} (ht : t < W.numVerts)
    (O : RotClass) :
    (W.pre t).Completed O ↔ ∀ w, rotClass w = O → w ∈ W.verts.take t := by
  have hdl : ((W.pre t).verts).dropLast = W.verts.take t := by
    show (W.verts.take (t + 1)).dropLast = W.verts.take t
    rw [List.dropLast_eq_take, List.length_take, List.take_take]
    congr 1
    have hlen : t < W.verts.length := ht
    omega
  unfold Walk.Completed
  rw [hdl]

theorem Walk.completed_finite {n : ℕ} (W : Walk n) : {O | W.Completed O}.Finite := by
  apply Set.Finite.subset ((W.verts.dropLast.finite_toSet).image rotClass)
  intro O hO
  obtain ⟨w, hw⟩ := Quotient.exists_rep O
  exact ⟨w, hO w hw, hw⟩

theorem Walk.numVerts_pos {n : ℕ} (W : Walk n) : 0 < W.numVerts :=
  List.length_pos_of_ne_nil W.ne

/-! ## Prefix stability and the walk-length recursion -/

theorem Walk.pre_vert {n : ℕ} (W : Walk n) {T s : ℕ} (h : s ≤ T) :
    (W.pre T).vert s = W.vert s := by
  show (W.verts.take (T + 1)).getD s [] = W.verts.getD s []
  by_cases hs : s < W.verts.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; omega),
      List.getD_eq_getElem _ _ hs, List.getElem_take]
  · rw [List.getD_eq_default _ _ (by rw [List.length_take]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem Walk.pre_numVerts {n : ℕ} (W : Walk n) (T : ℕ) :
    (W.pre T).numVerts = min (T + 1) W.numVerts := by
  show (W.verts.take (T + 1)).length = _
  rw [List.length_take]
  rfl

theorem Walk.activeLoop_pre {n : ℕ} (W : Walk n) (T : ℕ) :
    ∀ t, t ≤ T → (W.pre T).activeLoop t = W.activeLoop t := by
  intro t
  induction t with
  | zero =>
    intro _
    show genLoop ((W.pre T).vert 0) = genLoop (W.vert 0)
    rw [W.pre_vert (Nat.zero_le T)]
  | succ t ih =>
    intro ht
    show (if 2 ≤ wt n ((W.pre T).vert t) ((W.pre T).vert (t + 1)) then
        genLoop ((W.pre T).vert (t + 1)) else (W.pre T).activeLoop t) = _
    rw [W.pre_vert (by omega : t ≤ T), W.pre_vert ht, ih (by omega)]
    rfl

/-- Appending a vertex to a nonempty list adds one overlap term to the weight sum. -/
theorem wtsum_concat (f : List ℕ → List ℕ → ℕ) :
    ∀ (l : List (List ℕ)) (x : List ℕ), l ≠ [] →
      (List.zipWith f (l ++ [x]) ((l ++ [x]).tail)).sum
        = (List.zipWith f l l.tail).sum + f (l.getLastD []) x := by
  intro l
  induction l with
  | nil => intro x h; exact absurd rfl h
  | cons a l ih =>
    intro x _
    cases l with
    | nil => simp
    | cons b t =>
      have h2 := ih x (List.cons_ne_nil b t)
      have hgl : (a :: b :: t).getLastD [] = (b :: t).getLastD [] := rfl
      simp only [List.cons_append, List.tail_cons, List.zipWith_cons_cons,
        List.sum_cons, hgl] at h2 ⊢
      omega

theorem Walk.getLastD_take {n : ℕ} (W : Walk n) {i : ℕ} (hi : i < W.numVerts) :
    (W.verts.take (i + 1)).getLastD [] = W.vert i := by
  rw [W.take_succ_vert hi, List.getLastD_concat]

theorem Walk.wtW_pre_zero {n : ℕ} (W : Walk n) : (W.pre 0).wtW = 0 := by
  show (List.zipWith (wt n) (W.verts.take 1) (W.verts.take 1).tail).sum = 0
  rw [W.take_succ_vert W.numVerts_pos, List.take_zero]
  simp

theorem Walk.wtW_pre_succ {n : ℕ} (W : Walk n) {i : ℕ} (hi : i + 1 < W.numVerts) :
    (W.pre (i + 1)).wtW = (W.pre i).wtW + wt n (W.vert i) (W.vert (i + 1)) := by
  show (List.zipWith (wt n) (W.verts.take (i + 2)) (W.verts.take (i + 2)).tail).sum = _
  rw [W.take_succ_vert hi]
  rw [wtsum_concat (wt n) _ _ (by
    have hlen : (W.verts.take (i + 1)).length = i + 1 := by
      rw [List.length_take]
      have h2 : i + 1 < W.verts.length := hi
      omega
    intro h0
    rw [h0] at hlen
    simp at hlen)]
  rw [W.getLastD_take (by omega)]
  rfl

theorem Walk.pre_verts_last {n : ℕ} (W : Walk n) :
    (W.pre (W.numVerts - 1)).verts = W.verts := by
  show W.verts.take (W.numVerts - 1 + 1) = W.verts
  have := W.numVerts_pos
  rw [show W.numVerts - 1 + 1 = W.numVerts from by omega]
  exact List.take_of_length_le (le_refl _)

/-! ## The statistics of the one-vertex prefix and of the full prefix -/

theorem Walk.pre_zero_verts {n : ℕ} (W : Walk n) : (W.pre 0).verts = [W.vert 0] := by
  show W.verts.take 1 = _
  rw [W.take_succ_vert W.numVerts_pos]
  rfl

theorem Walk.pStat_pre_zero {n : ℕ} (W : Walk n) : (W.pre 0).pStat = 1 := by
  show {w | w ∈ (W.pre 0).verts}.ncard = 1
  rw [W.pre_zero_verts]
  have h : {w | w ∈ [W.vert 0]} = {W.vert 0} := by ext w; simp
  rw [h, Set.ncard_singleton]

theorem Walk.cStat_pre_zero {n : ℕ} (W : Walk n) : (W.pre 0).cStat = 0 := by
  show {O | (W.pre 0).Completed O}.ncard = 0
  have h : {O | (W.pre 0).Completed O} = ∅ := by
    ext O
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hO
    obtain ⟨w, hw⟩ := Quotient.exists_rep O
    have hmem := hO w hw
    rw [W.pre_zero_verts] at hmem
    simp at hmem
  rw [h, Set.ncard_empty]

theorem Walk.pre_zero_numVerts {n : ℕ} (W : Walk n) : (W.pre 0).numVerts = 1 := by
  show (W.pre 0).verts.length = 1
  rw [W.pre_zero_verts]
  rfl

theorem Walk.vStat_pre_zero {n : ℕ} (W : Walk n) : (W.pre 0).vStat = 1 := by
  show {L | (W.pre 0).Entered L}.ncard = 1
  have h : {L | (W.pre 0).Entered L} = {genLoop (W.vert 0)} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, hL⟩
      rw [W.pre_zero_numVerts] at ht
      have ht0 : t = 0 := by omega
      subst ht0
      rw [← hL]
      show genLoop ((W.pre 0).vert 0) = genLoop (W.vert 0)
      rw [W.pre_vert (le_refl 0)]
    · rintro rfl
      refine ⟨0, by rw [W.pre_zero_numVerts]; omega, ?_⟩
      show genLoop ((W.pre 0).vert 0) = genLoop (W.vert 0)
      rw [W.pre_vert (le_refl 0)]
  rw [h, Set.ncard_singleton]

theorem Walk.pStat_pre_last {n : ℕ} (W : Walk n) :
    (W.pre (W.numVerts - 1)).pStat = W.pStat := by
  show {w | w ∈ (W.pre (W.numVerts - 1)).verts}.ncard = _
  rw [W.pre_verts_last]
  rfl

theorem Walk.cStat_pre_last {n : ℕ} (W : Walk n) :
    (W.pre (W.numVerts - 1)).cStat = W.cStat := by
  show {O | (W.pre (W.numVerts - 1)).Completed O}.ncard = _
  have h : ∀ O, (W.pre (W.numVerts - 1)).Completed O ↔ W.Completed O := by
    intro O
    unfold Walk.Completed
    rw [W.pre_verts_last]
  simp only [h]
  rfl

theorem Walk.vStat_pre_last {n : ℕ} (W : Walk n) :
    (W.pre (W.numVerts - 1)).vStat = W.vStat := by
  show {L | (W.pre (W.numVerts - 1)).Entered L}.ncard = _
  have h : ∀ L, (W.pre (W.numVerts - 1)).Entered L ↔ W.Entered L := by
    intro L
    unfold Walk.Entered
    have hnum : (W.pre (W.numVerts - 1)).numVerts = W.numVerts := by
      show (W.pre (W.numVerts - 1)).verts.length = _
      rw [W.pre_verts_last]
      rfl
    rw [hnum]
    constructor
    · rintro ⟨t, ht, hL⟩
      exact ⟨t, ht, by rw [← W.activeLoop_pre (W.numVerts - 1) t (by omega)]; exact hL⟩
    · rintro ⟨t, ht, hL⟩
      exact ⟨t, ht, by rw [W.activeLoop_pre (W.numVerts - 1) t (by omega)]; exact hL⟩
  simp only [h]
  rfl

theorem Walk.wtW_pre_last {n : ℕ} (W : Walk n) :
    (W.pre (W.numVerts - 1)).wtW = W.wtW := by
  show (List.zipWith (wt n) (W.pre (W.numVerts - 1)).verts
      ((W.pre (W.numVerts - 1)).verts).tail).sum = _
  rw [W.pre_verts_last]
  rfl

/-! ## Active-loop and first-entry basics -/

theorem Walk.firstEntry_zero {n : ℕ} (W : Walk n) : W.IsFirstEntryTime 0 :=
  ⟨W.numVerts_pos, fun s hs => absurd hs (Nat.not_lt_zero s)⟩

theorem Walk.firstEntrySet_finite {n : ℕ} (W : Walk n) :
    (setOf W.IsFirstEntryTime).Finite :=
  (Set.finite_Iio W.numVerts).subset (fun _ ht => ht.1)

theorem Walk.numFE_eq_card {n : ℕ} (W : Walk n) :
    W.numFE = W.firstEntrySet_finite.toFinset.card := by
  show (setOf W.IsFirstEntryTime).ncard = _
  rw [Set.ncard_eq_toFinset_card _ W.firstEntrySet_finite]

/-- The enumeration `tauIdx` agrees with mathlib's `Nat.nth` on the valid range. -/
theorem Walk.tauIdx_eq_nth {n : ℕ} (W : Walk n) :
    ∀ i, i < W.numFE → W.tauIdx i = Nat.nth W.IsFirstEntryTime i := by
  intro i
  induction i with
  | zero =>
    intro _
    show (0 : ℕ) = _
    rw [Nat.nth_zero_of_zero W.firstEntry_zero]
  | succ i ih =>
    intro hi
    have hii : i < W.numFE := by omega
    have hcard : i + 1 < W.firstEntrySet_finite.toFinset.card := by
      rw [← W.numFE_eq_card]; exact hi
    show sInf {t | W.IsFirstEntryTime t ∧ W.tauIdx i < t} = _
    rw [ih hii]
    conv_rhs => rw [Nat.nth_eq_sInf]
    apply congrArg sInf
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hpx, hlt⟩
      refine ⟨hpx, fun k hk => ?_⟩
      rcases Nat.lt_or_eq_of_le (by omega : k ≤ i) with h | h
      · exact lt_trans (Nat.nth_lt_nth_of_lt_card W.firstEntrySet_finite h
          (by omega)) hlt
      · subst h; exact hlt
    · rintro ⟨hpx, hall⟩
      exact ⟨hpx, hall i (Nat.lt_succ_self i)⟩

theorem Walk.isFirstEntry_tauIdx {n : ℕ} (W : Walk n) {i : ℕ} (hi : i < W.numFE) :
    W.IsFirstEntryTime (W.tauIdx i) := by
  rw [W.tauIdx_eq_nth i hi]
  exact Nat.nth_mem_of_lt_card W.firstEntrySet_finite
    (by rw [← W.numFE_eq_card]; exact hi)

theorem Walk.tauIdx_lt_tauIdx {n : ℕ} (W : Walk n) {i k : ℕ} (hik : i < k)
    (hk : k < W.numFE) : W.tauIdx i < W.tauIdx k := by
  rw [W.tauIdx_eq_nth i (by omega), W.tauIdx_eq_nth k hk]
  exact Nat.nth_lt_nth_of_lt_card W.firstEntrySet_finite hik
    (by rw [← W.numFE_eq_card]; exact hk)

theorem Walk.tauIdx_le_tauIdx {n : ℕ} (W : Walk n) {i k : ℕ} (hik : i ≤ k)
    (hk : k < W.numFE) : W.tauIdx i ≤ W.tauIdx k := by
  rcases Nat.lt_or_eq_of_le hik with h | h
  · exact le_of_lt (W.tauIdx_lt_tauIdx h hk)
  · subst h; exact le_refl _

/-- The entered loops are exactly the active loops at first-entry times. -/
theorem Walk.entered_eq_image {n : ℕ} (W : Walk n) :
    {L | W.Entered L} = W.activeLoop '' (setOf W.IsFirstEntryTime) := by
  ext L
  constructor
  · rintro ⟨t, ht, hL⟩
    have hne : {s | s < W.numVerts ∧ W.activeLoop s = L}.Nonempty := ⟨t, ht, hL⟩
    obtain ⟨hT1, hT2⟩ := Nat.sInf_mem hne
    refine ⟨sInf {s | s < W.numVerts ∧ W.activeLoop s = L}, ⟨hT1, ?_⟩, hT2⟩
    intro s hs hcon
    have hle : sInf {s | s < W.numVerts ∧ W.activeLoop s = L} ≤ s :=
      Nat.sInf_le ⟨by omega, by rw [hcon, hT2]⟩
    omega
  · rintro ⟨t, htFE, rfl⟩
    exact ⟨t, htFE.1, rfl⟩

theorem Walk.activeLoop_injOn_firstEntries {n : ℕ} (W : Walk n) :
    Set.InjOn W.activeLoop (setOf W.IsFirstEntryTime) := by
  rintro t ht t' ht' heq
  by_contra hne
  rcases Nat.lt_or_ge t t' with h | h
  · exact ht'.2 t h heq
  · exact ht.2 t' (by omega) heq.symm

/-- At a first-entry time, the active loop is the loop generated by the vertex. -/
theorem Walk.activeLoop_firstEntry {n : ℕ} (W : Walk n) (t : ℕ)
    (ht : W.IsFirstEntryTime t) : W.activeLoop t = genLoop (W.vert t) := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [Walk.activeLoop]
    split_ifs with h
    · rfl
    · exfalso
      apply ht.2 t (Nat.lt_succ_self t)
      rw [Walk.activeLoop]
      simp [if_neg h]

/-! ## First visits of orbits and the first-visit owner -/

theorem Walk.entered_finite {n : ℕ} (W : Walk n) : {L | W.Entered L}.Finite := by
  rw [W.entered_eq_image]
  exact W.firstEntrySet_finite.image _

theorem Walk.omega_finite {n : ℕ} (W : Walk n) (O : RotClass) :
    (W.OmegaSet O).Finite :=
  W.entered_finite.subset (fun _ hL => hL.1)

theorem Walk.vert_isPerm {n : ℕ} (W : Walk n) {t : ℕ} (ht : t < W.numVerts) :
    IsPermWord n (W.vert t) :=
  W.isPerm _ (by rw [W.vert_eq_getElem ht]; exact List.getElem_mem _)

theorem Walk.sVisit_spec {n : ℕ} (W : Walk n) {O : RotClass}
    (hne : {t | t < W.numVerts ∧ rotClass (W.vert t) = O}.Nonempty) :
    W.sVisit O < W.numVerts ∧ rotClass (W.vert (W.sVisit O)) = O :=
  Nat.sInf_mem hne

theorem Walk.sVisit_le {n : ℕ} (W : Walk n) {O : RotClass} {t : ℕ}
    (ht : t < W.numVerts) (hO : rotClass (W.vert t) = O) : W.sVisit O ≤ t :=
  Nat.sInf_le ⟨ht, hO⟩

/-- The first visit of an orbit is not a rotation arrival, so it activates the loop of
its vertex (paper §5, justification that `F(O) ∈ Ω(O)`). -/
theorem Walk.activeLoop_sVisit {n : ℕ} (W : Walk n) {O : RotClass}
    (hne : {t | t < W.numVerts ∧ rotClass (W.vert t) = O}.Nonempty) :
    W.activeLoop (W.sVisit O) = genLoop (W.vert (W.sVisit O)) := by
  obtain ⟨hlt, hcls⟩ := W.sVisit_spec hne
  rcases hval : W.sVisit O with _ | s
  · rfl
  · rw [hval] at hlt hcls
    show (if 2 ≤ wt n (W.vert s) (W.vert (s + 1)) then genLoop (W.vert (s + 1))
      else W.activeLoop s) = genLoop (W.vert (s + 1))
    split_ifs with hw
    · rfl
    · exfalso
      have hperm1 : IsPermWord n (W.vert (s + 1)) := W.vert_isPerm hlt
      have hperm0 : IsPermWord n (W.vert s) := W.vert_isPerm (by omega)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h1 : W.vert (s + 1) = [] := List.length_eq_zero_iff.mp hperm1.length
        have h2 : W.vert 0 = [] :=
          List.length_eq_zero_iff.mp (W.vert_isPerm W.numVerts_pos).length
        have h0mem : (0 : ℕ) ∈ {t | t < W.numVerts ∧ rotClass (W.vert t) = O} :=
          ⟨W.numVerts_pos, by rw [h2, ← h1]; exact hcls⟩
        have hle : W.sVisit O ≤ 0 := Nat.sInf_le h0mem
        omega
      · have hw1 : wt n (W.vert s) (W.vert (s + 1)) = 1 := by
          have := (wt_spec hn (le_of_eq hperm0.length) (v := W.vert (s + 1))).1
          omega
        have hrho := eq_rho_of_wt_one hn hperm0 hperm1 hw1
        have hcls' : rotClass (W.vert s) = O := by
          rw [← hcls, hrho]
          exact rotClass_eq_iff.mpr ⟨1, rfl⟩
        have hle : W.sVisit O ≤ s := Nat.sInf_le ⟨by omega, hcls'⟩
        omega

theorem Walk.tauLoop_spec {n : ℕ} (W : Walk n) {L : MarkedLoop} (hL : W.Entered L) :
    W.tauLoop L < W.numVerts ∧ W.activeLoop (W.tauLoop L) = L :=
  Nat.sInf_mem hL

theorem Walk.tauLoop_le {n : ℕ} (W : Walk n) {L : MarkedLoop} {t : ℕ}
    (ht : t < W.numVerts) (hact : W.activeLoop t = L) : W.tauLoop L ≤ t :=
  Nat.sInf_le ⟨ht, hact⟩


/-- The first entry time of the `i`-th first-entered loop is `τ_i`. -/
theorem Walk.tauLoop_Efe {n : ℕ} (W : Walk n) {i : ℕ} (hi : i < W.numFE) :
    W.tauLoop (W.Efe i) = W.tauIdx i := by
  have hFE := W.isFirstEntry_tauIdx hi
  apply le_antisymm
  · exact W.tauLoop_le hFE.1 rfl
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := W.tauLoop_spec ⟨W.tauIdx i, hFE.1, rfl⟩
    exact hFE.2 _ hcon h2

/-- When `𝒞(j)` is nonempty, the chosen charge lies in it. -/
theorem Walk.charge_mem {n : ℕ} (W : Walk n) {j : ℕ} (h : (W.chargeSet j).Nonempty) :
    W.charge j ∈ W.chargeSet j := by
  unfold Walk.charge
  split
  next hpos => exact WellFounded.min_mem _ _ hpos
  next hneg => exact absurd h hneg

/-- Bound for members of `G_{O,L}`-fibers: they are valid break indices. -/
theorem Walk.gfiber_lt_numFE {n : ℕ} (W : Walk n) {s : RotClass × MarkedLoop} {j : ℕ}
    (hj : j ∈ W.Gfiber s) : j + 1 < W.numFE :=
  hj.1.1.1.1

theorem Walk.gfiber_finite {n : ℕ} (W : Walk n) (s : RotClass × MarkedLoop) :
    (W.Gfiber s).Finite :=
  (Set.finite_Iio W.numFE).subset (fun j hj => by
    have := W.gfiber_lt_numFE hj
    simp only [Set.mem_Iio]
    omega)

end Coeff2
