import Coeff2.CharlieClockMacro

/-!
# A safe forward-clock budget

Packet slots P and wrap slots W are subsets of a finite set of positions.
Every position costs 1, a packet costs an additional g, and a wrap doubles
that position's cost. Thus g = N^2 - 1 models the R/O clock at order N >= 1.

The finite-slot bound is independent of radix. The application below derives
the wrap set from ordered clock execution. Literal attachment/occupation may
remove arrangements; the bound does not assume those arrangements are legal.
Backward packets are NOT modeled by this forward-only theorem.
-/
namespace Coeff2.Charlieplex.ClockBudget

open scoped BigOperators
open ClockMacro

section Slots
variable {α : Type*} [Fintype α] [DecidableEq α]

def slotCost (g : ℕ) (P W : Finset α) : ℕ :=
  ∑ i, (if i ∈ P then 1 + g else 1) * (if i ∈ W then 2 else 1)

def lowerBound (L f w g : ℕ) : ℕ :=
  L + g * f + w + g * (f - (L - w))

omit [Fintype α] in
theorem cell_expansion (g : ℕ) (P W : Finset α) (i : α) :
    (if i ∈ P then 1 + g else 1) * (if i ∈ W then 2 else 1) =
      1 + (if i ∈ P then g else 0) + (if i ∈ W then 1 else 0) +
        (if i ∈ P ∩ W then g else 0) := by
  by_cases hp : i ∈ P <;> by_cases hw : i ∈ W
  all_goals simp [hp, hw]
  omega

theorem exact_slot_cost (g : ℕ) (P W : Finset α) :
    slotCost g P W = Fintype.card α + g * P.card + W.card + g * (P ∩ W).card := by
  unfold slotCost
  simp_rw [cell_expansion]
  have indicator (S : Finset α) (v : ℕ) : (∑ i, if i ∈ S then v else 0) = v * S.card := by
    simp [mul_comm]
  simp only [Finset.sum_add_distrib]
  rw [indicator P g, indicator W 1, indicator (P ∩ W) g]
  simp

/-- At most L-w packets fit outside the wrap positions. -/
theorem forced_wraps (P W : Finset α) :
    P.card - (Fintype.card α - W.card) ≤ (P ∩ W).card := by
  have h := Finset.card_inter_add_card_union P W
  have hu := Finset.card_le_univ (P ∪ W)
  have hw := Finset.card_le_univ W
  omega

theorem lowerBound_le_cost (g : ℕ) (P W : Finset α) :
    lowerBound (Fintype.card α) P.card W.card g ≤ slotCost g P W := by
  rw [exact_slot_cost]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left g (forced_wraps P W)) _

/-- Fill nonwrap slots first. This existence theorem concerns FREE slots;
it neither constructs nor promises a legal literal attachment. -/
theorem exists_fewest_wraps (W : Finset α) (f : ℕ) (hf : f ≤ Fintype.card α) :
    ∃ P : Finset α, P.card = f ∧
      (P ∩ W).card = f - (Fintype.card α - W.card) := by
  let A := Finset.univ \ W
  have ha : A.card = Fintype.card α - W.card := by
    simp [A, Finset.card_sdiff_of_subset]
  by_cases hfa : f ≤ A.card
  · obtain ⟨P, hp, hc⟩ := Finset.exists_subset_card_eq hfa
    have hi : P ∩ W = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (Finset.mem_sdiff.mp (hp (Finset.mem_inter.mp hi).1)).2
        (Finset.mem_inter.mp hi).2
    exact ⟨P, hc, by rw [hi, Finset.card_empty]; omega⟩
  · obtain ⟨P, hp, _, hc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ A) (by omega : A.card ≤ f) (by simpa using hf)
    have hu : P ∪ W = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      by_cases hi : i ∈ W
      · exact Finset.mem_union_right P hi
      · exact Finset.mem_union_left W (hp (by simp [A, hi]))
    have hcard := Finset.card_inter_add_card_union P W
    rw [hu, Finset.card_univ, hc] at hcard
    have hw := Finset.card_le_univ W
    exact ⟨P, hc, by omega⟩

theorem exists_optimal_slots (g : ℕ) (W : Finset α) (f : ℕ)
    (hf : f ≤ Fintype.card α) :
    ∃ P : Finset α, P.card = f ∧
      slotCost g P W = lowerBound (Fintype.card α) f W.card g := by
  obtain ⟨P, hc, hi⟩ := exists_fewest_wraps W f hf
  refine ⟨P, hc, ?_⟩
  rw [exact_slot_cost, hc, hi]
  rfl

/-- This is a rejection test, not a claim that a passing state can complete. -/
theorem reject_over_budget (g spent budget : ℕ) (P W : Finset α)
    (h : budget < spent + lowerBound (Fintype.card α) P.card W.card g) :
    budget < spent + slotCost g P W :=
  lt_of_lt_of_le h (Nat.add_le_add_left (lowerBound_le_cost g P W) spent)

end Slots

/-- Both R and O move one phase backwards. A packet has base cost 1+g;
a connector has base cost 1. Either doubles at phase zero. -/
def forward (m g : ℕ) (packet : Bool) : Macro m :=
  ⟨-1, fun j => (if packet then 1 + g else 1) * (if j = 0 then 2 else 1)⟩

def forwardPlan (m L g : ℕ) (P : Finset (Fin L)) : List (Macro m) :=
  List.ofFn (fun i => forward m g (decide (i ∈ P)))

def wrapSlots {m : ℕ} (L : ℕ) (j : ZMod m) : Finset (Fin L) :=
  Finset.univ.filter (fun i => j - (i.val : ZMod m) = 0)

theorem forwardPlan_shift (m L g : ℕ) (P : Finset (Fin L)) :
    (compile (forwardPlan m L g P)).shift = -(L : ZMod m) := by
  simpa [forwardPlan] using
    uniform_shift (fun i : Fin L => forward m g (decide (i ∈ P))) (-1) (fun _ => rfl)

theorem forwardPlan_end_phase (m L g spent : ℕ) (P : Finset (Fin L)) (j : ZMod m) :
    (run (forwardPlan m L g P) (j, spent)).1 = j - (L : ZMod m) := by
  rw [← compile_correct]
  change j + (compile (forwardPlan m L g P)).shift = _
  rw [forwardPlan_shift]
  exact (sub_eq_add_neg j (L : ZMod m)).symm

theorem forwardPlan_cost (m L g : ℕ) (P : Finset (Fin L)) (j : ZMod m) :
    (compile (forwardPlan m L g P)).cost j = slotCost g P (wrapSlots L j) := by
  unfold forwardPlan
  rw [uniform_cost _ (-1) (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simp [forward, wrapSlots, sub_eq_add_neg]

/-- All orders/radices and all finite forward R/O programs, not a corpus fit. -/
theorem forwardPlan_lowerBound (m L g : ℕ) (P : Finset (Fin L)) (j : ZMod m) :
    lowerBound L P.card (wrapSlots L j).card g ≤
      (compile (forwardPlan m L g P)).cost j := by
  rw [forwardPlan_cost]
  simpa using lowerBound_le_cost g P (wrapSlots L j)

theorem forwardPlan_reject (m L g spent budget : ℕ) (P : Finset (Fin L))
    (j : ZMod m) (h : budget < spent + lowerBound L P.card (wrapSlots L j).card g) :
    budget < (run (forwardPlan m L g P) (j, spent)).2 := by
  rw [← compile_correct]
  exact lt_of_lt_of_le h (Nat.add_le_add_left (forwardPlan_lowerBound m L g P j) spent)

/-- Prune ALL orders of these counts at once, without inspecting P. -/
theorem reject_all_forward_orders (m L g f spent budget : ℕ) (j : ZMod m)
    (h : budget < spent + lowerBound L f (wrapSlots L j).card g) :
    ∀ P : Finset (Fin L), P.card = f →
      budget < (run (forwardPlan m L g P) (j, spent)).2 := by
  intro P hc
  apply forwardPlan_reject
  simpa [hc] using h

/-- The bound is attained in the free R/O clock model, at every start phase. -/
theorem exists_optimal_forward_order (m L g f : ℕ) (j : ZMod m) (hf : f ≤ L) :
    ∃ P : Finset (Fin L), P.card = f ∧
      (compile (forwardPlan m L g P)).cost j = lowerBound L f (wrapSlots L j).card g := by
  obtain ⟨P, hc, hp⟩ := exists_optimal_slots g (wrapSlots L j) f (by simpa using hf)
  exact ⟨P, hc, by simpa [forwardPlan_cost] using hp⟩

theorem packet_base_cost (N : ℕ) (h : 1 ≤ N) : 1 + (N^2 - 1) = N^2 := by
  have : 1 ≤ N^2 := by nlinarith
  omega

end Coeff2.Charlieplex.ClockBudget
