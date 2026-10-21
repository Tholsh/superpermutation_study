import Coeff2.CharlieThreeLevelBoundary

/-! Two separated literal routes may exchange occupation. Neither route
needs to preserve its footprint individually. All crossing windows remain
inside `emitted`; the intervening text is left untouched. -/
namespace Coeff2.Charlieplex.CoordinatedExchange
open LiteralReservoir ThreeLevelBoundary

theorem exchange (n : ℕ) (boundary oldFirst newFirst middle oldSecond newSecond
    after : List ℕ)
    (hfirst : endBoundary n boundary oldFirst = endBoundary n boundary newFirst)
    (hsecond : endBoundary n
        (endBoundary n (endBoundary n boundary newFirst) middle) oldSecond =
      endBoundary n
        (endBoundary n (endBoundary n boundary newFirst) middle) newSecond)
    (hjoint : (emitted n boundary oldFirst).toFinset ∪
        (emitted n (endBoundary n (endBoundary n boundary newFirst) middle)
          oldSecond).toFinset =
      (emitted n boundary newFirst).toFinset ∪
        (emitted n (endBoundary n (endBoundary n boundary newFirst) middle)
          newSecond).toFinset) :
    (emitted n boundary (oldFirst ++ middle ++ oldSecond ++ after)).toFinset =
      (emitted n boundary (newFirst ++ middle ++ newSecond ++ after)).toFinset := by
  simp only [emitted_append, endBoundary_append, hfirst, hsecond,
    List.toFinset_append]
  ext p
  have hm := congrArg (fun s : Finset (List ℕ) => p ∈ s) hjoint
  simp only [Finset.mem_union] at hm ⊢
  tauto

/-- The exchange concludes literal coverage in the original word language.
Only the joint occupation identity is required, not two isolated identities. -/
theorem literal_exchange (n : ℕ) (hn : 1 ≤ n)
    (before oldFirst newFirst middle oldSecond newSecond after : List ℕ)
    (hfirst : endBoundary n (lastSymbols (n-1) before) oldFirst =
      endBoundary n (lastSymbols (n-1) before) newFirst)
    (hsecond : endBoundary n
        (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle)
        oldSecond =
      endBoundary n
        (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle)
        newSecond)
    (hjoint : (emitted n (lastSymbols (n-1) before) oldFirst).toFinset ∪
        (emitted n
          (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle)
          oldSecond).toFinset =
      (emitted n (lastSymbols (n-1) before) newFirst).toFinset ∪
        (emitted n
          (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle)
          newSecond).toFinset) :
    IsSuperperm n (before ++ (oldFirst ++ middle ++ oldSecond ++ after)) ↔
      IsSuperperm n (before ++ (newFirst ++ middle ++ newSecond ++ after)) := by
  have h := exchange n (lastSymbols (n-1) before) oldFirst newFirst middle
    oldSecond newSecond after hfirst hsecond hjoint
  have ho := run_occupation n (literalStateOf n before)
    (oldFirst ++ middle ++ oldSecond ++ after)
  have hp := run_occupation n (literalStateOf n before)
    (newFirst ++ middle ++ newSecond ++ after)
  rw [literalStateRun_correct n hn] at ho hp
  rw [← literalOccupation_covers_iff n _, ← literalOccupation_covers_iff n _]
  change (∀ p, IsPermWord n p → p ∈
    (literalStateOf n (before ++ (oldFirst ++ middle ++ oldSecond ++ after))).occupied) ↔
    (∀ p, IsPermWord n p → p ∈
      (literalStateOf n (before ++ (newFirst ++ middle ++ newSecond ++ after))).occupied)
  rw [ho, hp]
  simp only [literalStateOf]
  rw [h]

#print axioms exchange
#print axioms literal_exchange
end Coeff2.Charlieplex.CoordinatedExchange
