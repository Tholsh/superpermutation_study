import Coeff2.CharlieEganOccupationLift
import Mathlib.Data.List.Cycle

/-!
# Egan's local rule on literal words and its insertion-phase projection

The procedure is a baseline construction, not an optimality criterion.
No deviation from its rule is declared impossible. The actual cyclic
successor test is retained, including the wrap-around case.
-/

namespace Coeff2.Charlieplex.EganProcedure
open EganOccupationLift Finset
variable {α : Type*} [DecidableEq α]

def one (p : List α) : List α := p.rotate 1
def two (p : List α) : List α := p.drop 2 ++ (p.take 2).reverse

def cyclicNext (z : α) (p : List α) : α := p.nextOr z (p.headD z)

/-- `pred` is the cyclic predecessor policy on the old alphabet. -/
def ruleWeight (z : α) (pred : α → α) : List α → ℕ
  | [] => 1
  | f :: tail => if f = z then 1 else if cyclicNext z tail = pred f then 2 else 1

def ruleStep (z : α) (pred : α → α) (p : List α) : List α :=
  if ruleWeight z pred p = 2 then two p else one p

/-- Natural labels 1..N, as in Egan's published procedure. -/
def predecessor (N f : ℕ) : ℕ := if f = 1 then N - 1 else f - 1
def eganWeight (N : ℕ) (p : List ℕ) : ℕ := ruleWeight N (predecessor N) p
def eganStep (N : ℕ) (p : List ℕ) : List ℕ := ruleStep N (predecessor N) p

theorem ruleWeight_one_or_two (z : α) (pred : α → α) (p : List α) :
    ruleWeight z pred p = 1 ∨ ruleWeight z pred p = 2 := by
  cases p with
  | nil => exact Or.inl rfl
  | cons f t => simp only [ruleWeight]; split <;> (try {exact Or.inl rfl}); split <;> simp

/-- The cyclic test really reads the next literal symbol. -/
theorem cyclicNext_eq_next (z : α) (p : List α) (hz : z ∈ p) :
    cyclicNext z p = p.next z hz := by
  cases p with
  | nil => simp at hz
  | cons f t => rfl

theorem cyclicNext_rotate (z : α) (p : List α) (hp : p.Nodup) (hz : z ∈ p) (k : ℕ) :
    cyclicNext z (p.rotate k) = cyclicNext z p := by
  rw [cyclicNext_eq_next z _ (List.mem_rotate.mpr hz), cyclicNext_eq_next z p hz]
  exact List.isRotated_next_eq (List.IsRotated.forall p k)
    ((List.IsRotated.forall p k).nodup_iff.mpr hp) _

theorem nextOr_insertIdx (z d : α) (p : List α) (hz : z ∉ p) (i : ℕ) :
    (p.insertIdx i z).nextOr z d = p[i]?.getD d := by
  induction p generalizing i with
  | nil => cases i <;> simp
  | cons a p ih =>
    have hza : z ≠ a := fun he => hz (by simp [he])
    have hzp : z ∉ p := fun h => hz (by simp [h])
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.insertIdx_succ_cons, List.getElem?_cons_succ]
      rw [List.nextOr_cons_of_ne _ _ _ _ hza, ih hzp]

theorem cyclicNext_insertIdx (z b : α) (tail : List α) (hz : z ∉ b :: tail) (i : ℕ) :
    cyclicNext z ((b :: tail).insertIdx i z) = (b :: tail)[i]?.getD b := by
  cases i with
  | zero => simp [cyclicNext]
  | succ i =>
    change ((b :: tail).insertIdx (i+1) z).nextOr z b = _
    exact nextOr_insertIdx z b (b :: tail) hz (i+1)

/-- The unique non-front gap yielding projected depth two. Gap zero is
represented at the cyclic end, so this index is always positive. -/
def specialGap (p : List α) (r : α) : ℕ :=
  if p.idxOf r = 0 then p.length else p.idxOf r

theorem specialGap_bounds (b r : α) (tail : List α) (hr : r ∈ b :: tail) :
    1 ≤ specialGap (b :: tail) r ∧ specialGap (b :: tail) r ≤ (b :: tail).length := by
  have hi := List.idxOf_lt_length_of_mem hr
  simp only [specialGap]
  split <;> simp_all
  omega

theorem cyclicNext_positive_gap (z b r : α) (tail : List α)
    (hp : (b :: tail).Nodup) (hz : z ∉ b :: tail) (hr : r ∈ b :: tail)
    (i : ℕ) (hi : 1 ≤ i) (hle : i ≤ (b :: tail).length) :
    cyclicNext z ((b :: tail).insertIdx i z) = r ↔ i = specialGap (b :: tail) r := by
  rw [cyclicNext_insertIdx z b tail hz i]
  have hj := List.idxOf_lt_length_of_mem hr
  have hv : (b :: tail)[(b :: tail).idxOf r] = r := List.getElem_idxOf hj
  have hz0 : (b :: tail).idxOf r = 0 ↔ b = r := by
    simpa [eq_comm] using (List.idxOf_eq_zero_iff_head_eq (by simp) (a := r) (l := b :: tail))
  by_cases hilt : i < (b :: tail).length
  · rw [List.getElem?_eq_getElem hilt, Option.getD_some]
    have heq : (b :: tail)[i] = r ↔ i = (b :: tail).idxOf r := by
      conv_lhs => rw [← hv]
      exact hp.getElem_inj_iff
    rw [heq, specialGap]
    split <;> omega
  · have hil : i = (b :: tail).length := by omega
    subst i
    simp only [List.getElem?_length, Option.getD_none, specialGap]
    by_cases hzero : (b :: tail).idxOf r = 0
    · simp [hz0.mp hzero]
    · rw [if_neg hzero]
      constructor
      · intro h; exact False.elim (hzero (hz0.mpr h))
      · intro h; omega

theorem delete_one_insert (z f : α) (tail : List α) (hz : z ∉ f :: tail)
    (i : ℕ) (hi : i ≤ tail.length) :
    (one ((f :: tail).insertIdx (i+1) z)).erase z = one (f :: tail) := by
  have ht : z ∉ tail := fun h => hz (by simp [h])
  have hm : z ∈ tail.insertIdx i z := (List.mem_insertIdx hi).mpr (Or.inl rfl)
  simp only [List.insertIdx_succ_cons, one, List.rotate_cons_succ, List.rotate_zero]
  rw [List.erase_append_left _ hm, erase_insertIdx z tail ht i hi]

theorem delete_two_insert_second (z f : α) (tail : List α) (hz : z ∉ f :: tail) :
    (two (f :: z :: tail)).erase z = one (f :: tail) := by
  have ht : z ∉ tail := fun h => hz (by simp [h])
  simp only [two, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rw [List.erase_append_right _ ht]
  simp [one]

theorem delete_two_insert_later (z f b : α) (tail : List α) (hz : z ∉ f :: b :: tail)
    (i : ℕ) (hi : i ≤ tail.length) :
    (two ((f :: b :: tail).insertIdx (i+2) z)).erase z = two (f :: b :: tail) := by
  have ht : z ∉ tail := fun h => hz (by simp [h])
  have hm : z ∈ tail.insertIdx i z := (List.mem_insertIdx hi).mpr (Or.inl rfl)
  simp only [List.insertIdx_succ_cons, two, List.drop_succ_cons, List.drop_zero,
    List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]
  rw [List.erase_append_left _ hm, erase_insertIdx z tail ht i hi]

/-- Pointwise all-n projection, retaining the unique exceptional insertion
port. This is not an assertion that the lower Egan successor is the image. -/
theorem delete_ruleStep_insert (z f b : α) (tail : List α) (pred : α → α)
    (hp : (f :: b :: tail).Nodup) (hz : z ∉ f :: b :: tail)
    (hr : pred f ∈ b :: tail) (i : ℕ) (hi : i ≤ (f :: b :: tail).length) :
    (ruleStep z pred ((f :: b :: tail).insertIdx i z)).erase z =
      if i = 0 then f :: b :: tail
      else if i = specialGap (b :: tail) (pred f) + 1 then two (f :: b :: tail)
      else one (f :: b :: tail) := by
  have hzf : f ≠ z := fun he => hz (by simp [he])
  have hzt : z ∉ b :: tail := fun h => hz (by simp [h])
  have hpt : (b :: tail).Nodup := (List.nodup_cons.mp hp).2
  have hb := specialGap_bounds b (pred f) tail hr
  cases i with
  | zero =>
    simp only [List.insertIdx_zero, ruleStep, ruleWeight,
      Nat.reduceEqDiff, ite_false, ite_true, one, List.rotate_cons_succ, List.rotate_zero]
    rw [List.erase_append_right _ hz]
    simp
  | succ i =>
    cases i with
    | zero =>
      have hgap : 1 ≠ specialGap (b :: tail) (pred f) + 1 := by omega
      simp only [List.insertIdx_succ_cons, List.insertIdx_zero, ruleStep, ruleWeight, if_neg hzf]
      split <;> simp only [ite_true, ite_false, Nat.reduceEqDiff]
      · exact delete_two_insert_second z f (b :: tail) hz
      · exact delete_one_insert z f (b :: tail) hz 0 (by omega)
    | succ i =>
      have htest := cyclicNext_positive_gap z b (pred f) tail hpt hzt hr (i+1) (by omega) (by simpa using hi)
      have hidx : i + 2 = specialGap (b :: tail) (pred f) + 1 ↔ i+1 = specialGap (b :: tail) (pred f) := by omega
      by_cases hc : cyclicNext z ((b :: tail).insertIdx (i+1) z) = pred f
      · have he : i+2 = specialGap (b :: tail) (pred f) + 1 := hidx.mpr (htest.mp hc)
        simp only [List.insertIdx_succ_cons] at hc
        have hw : ruleWeight z pred ((f :: b :: tail).insertIdx (i+2) z) = 2 := by
          simp only [List.insertIdx_succ_cons, ruleWeight, if_neg hzf, if_pos hc]
        rw [if_neg (by omega : i+1+1 ≠ 0), if_pos he, ruleStep, hw, if_pos rfl]
        exact delete_two_insert_later z f b tail hz i (by simpa using hi)
      · have he : i+2 ≠ specialGap (b :: tail) (pred f) + 1 := fun h => hc (htest.mpr (hidx.mp h))
        simp only [List.insertIdx_succ_cons] at hc
        have hw : ruleWeight z pred ((f :: b :: tail).insertIdx (i+2) z) = 1 := by
          simp only [List.insertIdx_succ_cons, ruleWeight, if_neg hzf, if_neg hc]
        rw [if_neg (by omega : i+1+1 ≠ 0), if_neg he, ruleStep, hw, if_neg (by decide)]
        exact delete_one_insert z f (b :: tail) hz (i+1) (by simpa using hi)

theorem predecessor_in_old_tail (n f : ℕ) (tail : List ℕ) (hn : 2 ≤ n)
    (hp : (f :: tail).Perm (List.range' 1 n)) : predecessor (n+1) f ∈ tail := by
  have hf : 1 ≤ f ∧ f < 1+n := List.mem_range'_1.mp (hp.mem_iff.mp (by simp))
  have hr : 1 ≤ predecessor (n+1) f ∧ predecessor (n+1) f < 1+n ∧ predecessor (n+1) f ≠ f := by
    unfold predecessor
    split <;> omega
  have hm := hp.mem_iff.mpr (List.mem_range'_1.mpr ⟨hr.1, hr.2.1⟩)
  exact (List.mem_cons.mp hm).resolve_left hr.2.2

/-- The generic phase theorem applies to Egan's actual natural-label rule,
with the required predecessor membership derived from the permutation. -/
theorem delete_eganStep_insert (n f b : ℕ) (tail : List ℕ) (hn : 2 ≤ n)
    (hp : (f :: b :: tail).Perm (List.range' 1 n))
    (i : ℕ) (hi : i ≤ (f :: b :: tail).length) :
    (eganStep (n+1) ((f :: b :: tail).insertIdx i (n+1))).erase (n+1) =
      if i = 0 then f :: b :: tail
      else if i = specialGap (b :: tail) (predecessor (n+1) f) + 1 then two (f :: b :: tail)
      else one (f :: b :: tail) := by
  apply delete_ruleStep_insert
  · exact hp.nodup_iff.mpr (List.nodup_range')
  · intro h
    have := List.mem_range'_1.mp (hp.mem_iff.mp h)
    omega
  · exact predecessor_in_old_tail n f (b :: tail) hn hp
  · exact hi

theorem three_bucket_sum (n k a b c : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∑ i ∈ range (n+1), if i=0 then a else if i=k then c else b) = a+(n-1)*b+c := by
  let F := fun i : ℕ => if i=0 then a else if i=k then c else b
  have hzero : 0 ∈ range (n+1) := by simp
  have hkm : k ∈ (range (n+1)).erase 0 := by simp; omega
  have h1 := sum_erase_add (range (n+1)) F hzero
  have h2 := sum_erase_add ((range (n+1)).erase 0) F hkm
  have hrest : (∑ i ∈ ((range (n+1)).erase 0).erase k, F i) = (n-1)*b := by
    calc
      _ = ∑ _i ∈ ((range (n+1)).erase 0).erase k, b := by
        apply sum_congr rfl
        intro i hi
        obtain ⟨hik, hi0, _⟩ := by simpa only [mem_erase] using hi
        simp [F, hik, hi0]
      _ = _ := by rw [sum_const_nat (fun _ _ => rfl), card_erase_of_mem hkm,
        card_erase_of_mem hzero, card_range]; simp
  have hf0 : F 0 = a := by simp [F]
  have hfk : F k = c := by simp [F, show k ≠ 0 by omega]
  rw [hrest, hfk] at h2
  rw [hf0, ← h2] at h1
  change (∑ i ∈ range (n+1), F i) = _
  omega

/-- Exact integer transfer operator for every insertion phase of a literal
permutation. Test functions may be occupation indicators or integer costs. -/
theorem projected_rule_sum (z f b : α) (tail : List α) (pred : α → α)
    (hp : (f :: b :: tail).Nodup) (hz : z ∉ f :: b :: tail)
    (hr : pred f ∈ b :: tail) (φ : List α → ℕ) :
    (∑ i ∈ range ((f :: b :: tail).length+1),
      φ ((ruleStep z pred ((f :: b :: tail).insertIdx i z)).erase z)) =
      φ (f :: b :: tail) + (tail.length+1)*φ (one (f :: b :: tail)) + φ (two (f :: b :: tail)) := by
  have hgap := specialGap_bounds b (pred f) tail hr
  calc
    _ = ∑ i ∈ range ((f :: b :: tail).length+1),
        if i=0 then φ (f :: b :: tail)
        else if i=specialGap (b :: tail) (pred f)+1 then φ (two (f :: b :: tail))
        else φ (one (f :: b :: tail)) := by
      apply sum_congr rfl
      intro i hi
      rw [delete_ruleStep_insert z f b tail pred hp hz hr i (Nat.le_of_lt_succ (mem_range.mp hi))]
      split <;> (try rfl)
      split <;> rfl
    _ = _ := by
      rw [three_bucket_sum _ _ _ _ _ (by omega) (by simpa using Nat.add_le_add_right hgap.2 1)]
      simp

theorem ruleStep_perm (z : α) (pred : α → α) (p : List α) :
    (ruleStep z pred p).Perm p := by
  unfold ruleStep
  split
  · change (p.drop 2 ++ (p.take 2).reverse).Perm p
    exact ((List.reverse_perm (p.take 2)).append_left (p.drop 2)).trans
      (by simpa using (List.perm_append_comm (l₁ := p.drop 2) (l₂ := p.take 2)))
  · exact List.rotate_perm p 1

/-- All insertion phases are retained as choices. This tests immediate
occupation only, not the existence of a budget-feasible completion. -/
def unblockedInsertionChoices (z : α) (pred : α → α) (p : List α)
    (occupied : Finset (List α)) : Finset ℕ :=
  (range (p.length+1)).filter fun i => ruleStep z pred (p.insertIdx i z) ∉ occupied

/-- Exact local right/blocked count when the occupied set contains complete
deletion fibers. Arbitrary partial upper occupation is not assumed saturated. -/
theorem unblocked_lift_count (z f b : α) (tail : List α) (pred : α → α)
    (hp : (f :: b :: tail).Nodup) (hz : z ∉ f :: b :: tail)
    (hr : pred f ∈ b :: tail) (U : Finset (List α)) (hU : ∀ p ∈ U, z ∉ p) :
    (unblockedInsertionChoices z pred (f :: b :: tail) (occupationLift z U)).card =
      (if f :: b :: tail ∈ U then 0 else 1) +
      (tail.length+1)*(if one (f :: b :: tail) ∈ U then 0 else 1) +
      (if two (f :: b :: tail) ∈ U then 0 else 1) := by
  rw [unblockedInsertionChoices, card_eq_sum_ones, sum_filter]
  calc
    _ = ∑ i ∈ range ((f :: b :: tail).length+1),
      (if (ruleStep z pred ((f :: b :: tail).insertIdx i z)).erase z ∈ U then 0 else 1) := by
      apply sum_congr rfl
      intro i hi
      have hzchild : z ∈ (f :: b :: tail).insertIdx i z :=
        (List.mem_insertIdx (Nat.le_of_lt_succ (mem_range.mp hi))).mpr (Or.inl rfl)
      have hznext := (ruleStep_perm z pred ((f :: b :: tail).insertIdx i z)).mem_iff.mpr hzchild
      simp only [mem_occupationLift z U _ hU, hznext, true_and]
      split <;> simp_all
    _ = _ := projected_rule_sum z f b tail pred hp hz hr (fun q => if q ∈ U then 0 else 1)

def innerTurn (z : α) (pred : α → α) : List α → List α
  | [] => []
  | f :: tail => if ruleWeight z pred (f :: tail) = 2 then f :: tail.rotate 1 else f :: tail

def innerUnturn (z : α) (pred : α → α) : List α → List α
  | [] => []
  | f :: tail => if ruleWeight z pred (f :: tail) = 2
      then f :: tail.rotate (tail.length-1) else f :: tail

theorem ruleWeight_inner_phase (z f : α) (tail : List α) (pred : α → α)
    (hp : tail.Nodup) (hz : z ∈ tail) (k : ℕ) :
    ruleWeight z pred (f :: tail.rotate k) = ruleWeight z pred (f :: tail) := by
  simp only [ruleWeight, cyclicNext_rotate z tail hp hz k]

theorem innerUnturn_innerTurn (z : α) (pred : α → α) (p : List α)
    (hp : p.Nodup) (hz : z ∈ p) : innerUnturn z pred (innerTurn z pred p) = p := by
  cases p with
  | nil => simp [innerTurn, innerUnturn]
  | cons f tail =>
    have hpt : tail.Nodup := (List.nodup_cons.mp hp).2
    by_cases hf : f = z
    · simp [innerTurn, innerUnturn, ruleWeight, hf]
    have hzt : z ∈ tail := (List.mem_cons.mp hz).resolve_left (Ne.symm hf)
    have hpos : 1 ≤ tail.length := List.length_pos_of_mem hzt
    by_cases hw : ruleWeight z pred (f :: tail) = 2
    · simp only [innerTurn, if_pos hw, innerUnturn,
        ruleWeight_inner_phase z f tail pred hpt hzt 1, List.length_rotate, List.rotate_rotate]
      rw [show 1+(tail.length-1)=tail.length by omega, List.rotate_length]
    · simp only [innerTurn, if_neg hw, innerUnturn]

theorem ruleStep_eq_outer_inner (z : α) (pred : α → α) (p : List α) :
    ruleStep z pred p = one (innerTurn z pred p) := by
  cases p with
  | nil => simp [ruleStep, ruleWeight, one, innerTurn]
  | cons f tail =>
    simp only [ruleStep, innerTurn]
    split
    · cases tail with
      | nil => simp [one, two]
      | cons b tail => exact (marked_cycle_port_step f b tail).symm
    · rfl

/-- Local cycle-cover property from first principles: no two distinct
permutations have the same Egan successor. It does not count global cycles. -/
theorem ruleStep_injective (z : α) (pred : α → α) {p q : List α}
    (hp : p.Nodup) (hq : q.Nodup) (hzp : z ∈ p) (hzq : z ∈ q)
    (he : ruleStep z pred p = ruleStep z pred q) : p = q := by
  rw [ruleStep_eq_outer_inner, ruleStep_eq_outer_inner] at he
  have hi := List.rotate_injective 1 he
  have h := congrArg (innerUnturn z pred) hi
  simpa only [innerUnturn_innerTurn z pred p hp hzp, innerUnturn_innerTurn z pred q hq hzq] using h

theorem ruleStep_covers_permutations (z : α) (pred : α → α) (A : List α)
    (hA : A.Nodup) (hz : z ∈ A) :
    A.permutations.toFinset.image (ruleStep z pred) = A.permutations.toFinset := by
  have hsub : A.permutations.toFinset.image (ruleStep z pred) ⊆ A.permutations.toFinset := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr
      ((ruleStep_perm z pred p).trans (List.mem_permutations.mp (List.mem_toFinset.mp hp))))
  apply eq_of_subset_of_card_le hsub
  have hinj : Set.InjOn (ruleStep z pred) (A.permutations.toFinset : Set (List α)) := by
    intro p hp q hq he
    have hpp := List.mem_permutations.mp (List.mem_toFinset.mp hp)
    have hqp := List.mem_permutations.mp (List.mem_toFinset.mp hq)
    exact ruleStep_injective z pred (hpp.nodup_iff.mpr hA) (hqp.nodup_iff.mpr hA)
      (hpp.mem_iff.mpr hz) (hqp.mem_iff.mpr hz) he
  rw [card_image_of_injOn hinj]

theorem unblockedInsertionChoices_anti (z : α) (pred : α → α) (p : List α)
    {U V : Finset (List α)} (hUV : U ⊆ V) :
    unblockedInsertionChoices z pred p V ⊆ unblockedInsertionChoices z pred p U := by
  intro i hi
  obtain ⟨hi, hn⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨hi, fun h => hn (hUV h)⟩

/-- Conservative quotient envelopes give certified local counting bounds.
Neither an envelope nor a projected set is declared to be the full cache. -/
theorem unblockedInsertionChoices_bounds (z : α) (pred : α → α) (p : List α)
    (U lower upper : Finset (List α)) (hlo : lower ⊆ U) (hhi : U ⊆ upper) :
    (unblockedInsertionChoices z pred p upper).card ≤ (unblockedInsertionChoices z pred p U).card ∧
    (unblockedInsertionChoices z pred p U).card ≤ (unblockedInsertionChoices z pred p lower).card :=
  ⟨card_le_card (unblockedInsertionChoices_anti z pred p hhi),
    card_le_card (unblockedInsertionChoices_anti z pred p hlo)⟩

def eganStart (N : ℕ) : List ℕ := (List.range' 2 (N-2)).reverse ++ [N,1]
def spliceDeparture (N : ℕ) : List ℕ := [1,N] ++ (List.range' 2 (N-2)).reverse
def pathWeight (N : ℕ) (p : List ℕ) : ℕ := if p = spliceDeparture N then 1 else eganWeight N p
def pathStep (N : ℕ) (p : List ℕ) : List ℕ := if pathWeight N p = 2 then two p else one p

def pathStates (N : ℕ) : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | k+1, p => p :: pathStates N k (pathStep N p)

def emittedSymbols (N : ℕ) : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | k+1, p => (p.take (pathWeight N p)).reverse ++ emittedSymbols N k (pathStep N p)

def constructedWord (N : ℕ) : List ℕ :=
  eganStart N ++ emittedSymbols N (N.factorial-1) (eganStart N)

/-- This finite checker uses literal contiguous substrings, not graph labels. -/
def coversAlphabet (A word : List α) : Bool :=
  A.permutations'.all fun p => decide (p.IsInfix word)

theorem coversAlphabet_iff (A word : List α) :
    coversAlphabet A word = true ↔ ∀ p : List α, p.Perm A → p.IsInfix word := by
  simp only [coversAlphabet, List.all_eq_true, decide_eq_true_eq, List.mem_permutations']

/-- The literal procedural iterator emits exactly its requested state count. -/
theorem pathStates_length (N k : ℕ) (p : List ℕ) : (pathStates N k p).length = k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [pathStates, ih]

end Coeff2.Charlieplex.EganProcedure
