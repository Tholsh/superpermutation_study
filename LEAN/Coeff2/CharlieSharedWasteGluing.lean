import Coeff2.CharlieSharedWasteResponse

/-!
# Exact response composition and a repeat-permitting shared-waste certificate

This module extends, rather than replaces, the existing literal gluing layer.
No word, kernel, phase assignment or short completion is assumed to exist.
Every cost improvement theorem consumes actual words and actual labelled
occupation. The response composition theorem is the exact feasible-profile
law on which a finite building-block min-plus DP can operate.
-/
namespace Coeff2.Charlieplex.SharedWasteGluing
open LiteralReservoir ThreeLevelBoundary PacketAssembly SharedWasteResponse

abbrev State := List ℕ × Finset (List ℕ)

def advance (n : ℕ) (s : State) (word : List ℕ) : State :=
  (endBoundary n s.1 word, s.2 ∪ (emitted n s.1 word).toFinset)

theorem advance_append (n : ℕ) (s : State) (left right : List ℕ) :
    advance n s (left ++ right) = advance n (advance n s left) right := by
  simp only [advance, endBoundary_append, emitted_append, List.toFinset_append,
    Finset.union_assoc]

/-- Literal response families may contain arbitrary strings, not atomic tours.
The alphabet test is explicit; repeats remain permitted. -/
def Responds (n : ℕ) (family : Set (List ℕ)) (s t : State) (cost : ℤ) : Prop :=
  ∃ word ∈ family, literalAlphabetTest n word = true ∧
    advance n s word = t ∧ appendCharge n s.1 s.2 word = cost

def concatFamily (A B : Set (List ℕ)) : Set (List ℕ) :=
  {word | ∃ left ∈ A, ∃ right ∈ B, word = left ++ right}

/-- Exact min-plus FEASIBLE-cost profile: the shared state retains occupation. -/
theorem response_compose (n : ℕ) (A B : Set (List ℕ)) (s t : State) (c : ℤ) :
    Responds n (concatFamily A B) s t c ↔
      ∃ r a b, Responds n A s r a ∧ Responds n B r t b ∧ c = a + b := by
  constructor
  · rintro ⟨word, ⟨left, hl, right, hr, rfl⟩, ha, ht, hc⟩
    have hal : literalAlphabetTest n left = true ∧ literalAlphabetTest n right = true := by
      simpa only [literalAlphabetTest, List.all_append, Bool.and_eq_true] using ha
    refine ⟨advance n s left, appendCharge n s.1 s.2 left,
      appendCharge n (advance n s left).1 (advance n s left).2 right,
      ⟨left, hl, hal.1, rfl, rfl⟩,
      ⟨right, hr, hal.2, ?_, rfl⟩, ?_⟩
    · simpa only [advance_append] using ht
    · rw [← hc, appendCharge_append]
      rfl
  · rintro ⟨r, a, b, ⟨left, hl, hal, hsl, hca⟩,
      ⟨right, hr, har, hrt, hcb⟩, rfl⟩
    refine ⟨left ++ right, ⟨left, hl, right, hr, rfl⟩, ?_, ?_, ?_⟩
    · simpa only [literalAlphabetTest, List.all_append, Bool.and_eq_true] using And.intro hal har
    · rw [advance_append, hsl, hrt]
    · rw [appendCharge_append, hca]
      change a + appendCharge n (advance n s left).1 (advance n s left).2 right = _
      rw [hsl, hcb]

def BestResponse (n : ℕ) (family : Set (List ℕ)) (s t : State) (cost : ℤ) : Prop :=
  Responds n family s t cost ∧ ∀ other, Responds n family s t other → cost ≤ other

/-- Taking the minimum of this complete feasible profile is exact DP. No
claim that its state table is small, or that one corpus vocabulary is complete. -/
theorem best_response_compose (n : ℕ) (A B : Set (List ℕ)) (s t : State) (c : ℤ) :
    BestResponse n (concatFamily A B) s t c ↔
      (∃ r a b, Responds n A s r a ∧ Responds n B r t b ∧ c = a+b) ∧
      ∀ r a b, Responds n A s r a → Responds n B r t b → c ≤ a+b := by
  constructor
  · rintro ⟨hc, hleast⟩
    refine ⟨(response_compose n A B s t c).mp hc, ?_⟩
    intro r a b ha hb
    exact hleast (a+b) ((response_compose n A B s t (a+b)).mpr ⟨r,a,b,ha,hb,rfl⟩)
  · rintro ⟨hc, hleast⟩
    refine ⟨(response_compose n A B s t c).mpr hc, ?_⟩
    intro other ho
    obtain ⟨r,a,b,ha,hb,rfl⟩ := (response_compose n A B s t other).mp ho
    exact hleast r a b ha hb

theorem charge_glue_factor (n : ℕ) (hn : 1 ≤ n) (U : Finset (List ℕ))
    (a b : List ℕ) (k : ℕ) (hs : IsSeam a b k) (hk : n-1 ≤ k) :
    charge n U (glue a b k) = charge n U a + charge n U b +
      ((extraShared n U a b (b.take k)).card - charge n U (b.take k)) := by
  have h := interaction_factor n hn U a b k hs hk
  unfold interaction at h
  omega

/-- Shared-waste saving is compared with the OLD interaction, not zero.
Joint footprint equality is sufficient; per-piece ownership is not required.
Fixed exterior frames permit replacement in any literal surrounding context. -/
theorem sharedWaste_shorter_in_context (n : ℕ) (hn : 1 ≤ n)
    (U : Finset (List ℕ)) (a b c d before after : List ℕ) (k l : ℕ)
    (hold : IsSeam a b k) (hnew : IsSeam c d l)
    (hk : n-1 ≤ k) (hl : n-1 ≤ l)
    (hfirst : (glue a b k).take (n-1) = (glue c d l).take (n-1))
    (hlast : lastSymbols (n-1) (glue a b k) = lastSymbols (n-1) (glue c d l))
    (hocc : footprint n a ∪ footprint n b = footprint n c ∪ footprint n d)
    (halpha : literalAlphabetTest n (glue a b k) = literalAlphabetTest n (glue c d l))
    (hgain : charge n U c + charge n U d +
        ((extraShared n U c d (d.take l)).card - charge n U (d.take l)) <
      charge n U a + charge n U b +
        ((extraShared n U a b (b.take k)).card - charge n U (b.take k))) :
    (before ++ glue c d l ++ after).length < (before ++ glue a b k ++ after).length ∧
      (Valid n (before ++ glue a b k ++ after) ↔ Valid n (before ++ glue c d l ++ after)) := by
  have heq : footprint n (glue a b k) = footprint n (glue c d l) := by
    rw [footprint_glue n hn a b k hold hk, footprint_glue n hn c d l hnew hl, hocc]
  have ho : (literalStateOf n (glue a b k)).occupied =
      (literalStateOf n (glue c d l)).occupied := heq
  have hwold : n-1 ≤ (glue a b k).length := by
    have hka := hold.1
    simp only [glue, List.length_append]
    omega
  have hwnew : n-1 ≤ (glue c d l).length := by
    have hlc := hnew.1
    simp only [glue, List.length_append]
    omega
  have hcharge : charge n U (glue c d l) < charge n U (glue a b k) := by
    rw [charge_glue_factor n hn U c d l hnew hl, charge_glue_factor n hn U a b k hold hk]
    exact hgain
  have hlen : (glue c d l).length < (glue a b k).length := by
    unfold charge at hcharge
    rw [heq] at hcharge
    omega
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  exact ContextReplacement.replace_valid n hn before (glue a b k) (glue c d l)
    after hwold hwnew hfirst hlast ho halpha

/-- The existing two-separated-region theorem with its literal length gate.
No equal-multiplicity or no-repeat restriction is imposed. -/
theorem coordinated_shorter (n : ℕ) (hn : 1 ≤ n)
    (before oldFirst newFirst middle oldSecond newSecond after : List ℕ)
    (hfirst : endBoundary n (lastSymbols (n-1) before) oldFirst =
      endBoundary n (lastSymbols (n-1) before) newFirst)
    (hsecond : endBoundary n
      (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle) oldSecond =
      endBoundary n
      (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle) newSecond)
    (hjoint : (emitted n (lastSymbols (n-1) before) oldFirst).toFinset ∪
      (emitted n (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle) oldSecond).toFinset =
      (emitted n (lastSymbols (n-1) before) newFirst).toFinset ∪
      (emitted n (endBoundary n (endBoundary n (lastSymbols (n-1) before) newFirst) middle) newSecond).toFinset)
    (hgain : newFirst.length + newSecond.length < oldFirst.length + oldSecond.length) :
    (before ++ (newFirst ++ middle ++ newSecond ++ after)).length <
      (before ++ (oldFirst ++ middle ++ oldSecond ++ after)).length ∧
    (IsSuperperm n (before ++ (oldFirst ++ middle ++ oldSecond ++ after)) ↔
      IsSuperperm n (before ++ (newFirst ++ middle ++ newSecond ++ after))) := by
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  exact CoordinatedExchange.literal_exchange n hn before oldFirst newFirst middle
    oldSecond newSecond after hfirst hsecond hjoint

end Coeff2.Charlieplex.SharedWasteGluing
