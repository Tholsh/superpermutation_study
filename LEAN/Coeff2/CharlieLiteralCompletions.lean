import Coeff2.CharlieLiteralState

/-! Explicit finite continuation vocabulary. These definitions restore the
literal completion API used by the binomial/occupation modules. No supplied
realization axiom or corpus restriction is used. -/
namespace Coeff2.Charlieplex

def literalSuffixes (n : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | h+1 => (Finset.Icc 1 n).biUnion fun a =>
      (literalSuffixes n h).image (List.cons a)

theorem mem_literalSuffixes (n h : ℕ) (w : List ℕ) :
    w ∈ literalSuffixes n h ↔
      w.length = h ∧ ∀ a ∈ w, 1 ≤ a ∧ a ≤ n := by
  induction h generalizing w with
  | zero => cases w <;> simp [literalSuffixes]
  | succ h ih =>
    cases w with
    | nil => simp [literalSuffixes]
    | cons a rest =>
      simp [literalSuffixes, ih, Finset.mem_Icc, and_assoc, and_left_comm, and_comm]

def literalSuccessfulSuffixes (n budget h : ℕ) (state : LiteralSearchState) :
    Finset (List ℕ) :=
  (literalSuffixes n h).filter fun w =>
    literalStateAccept n budget (literalStateRun n state w) = true

theorem mem_literalSuccessfulSuffixes (n budget h : ℕ) (hn : 1 ≤ n)
    (text w : List ℕ) :
    w ∈ literalSuccessfulSuffixes n budget h (literalStateOf n text) ↔
      w.length = h ∧ (∀ a ∈ text ++ w, 1 ≤ a ∧ a ≤ n) ∧
        (text ++ w).length = budget ∧ IsSuperperm n (text ++ w) := by
  rw [literalSuccessfulSuffixes, Finset.mem_filter, mem_literalSuffixes,
    literalStateRun_accept_iff n budget hn]
  constructor
  · rintro ⟨⟨hl, _⟩, ha, hb, hc⟩
    exact ⟨hl, ha, hb, hc⟩
  · rintro ⟨hl, ha, hb, hc⟩
    exact ⟨⟨hl, fun a hm => ha a (List.mem_append_right text hm)⟩, ha, hb, hc⟩

theorem literalSuccessfulSuffixes_succ (n budget h : ℕ)
    (state : LiteralSearchState) :
    literalSuccessfulSuffixes n budget (h+1) state =
      (Finset.Icc 1 n).biUnion fun a =>
        (literalSuccessfulSuffixes n budget h (literalStateStep n state a)).image
          (List.cons a) := by
  ext w
  cases w <;> simp [literalSuccessfulSuffixes, literalSuffixes, literalStateRun, and_assoc]

def literalBellmanCount (n budget : ℕ) : ℕ → LiteralSearchState → ℕ
  | 0, state => if literalStateAccept n budget state then 1 else 0
  | h+1, state => ∑ a ∈ Finset.Icc 1 n,
      literalBellmanCount n budget h (literalStateStep n state a)

theorem literalBellmanCount_eq_card (n budget h : ℕ) (state : LiteralSearchState) :
    literalBellmanCount n budget h state =
      (literalSuccessfulSuffixes n budget h state).card := by
  induction h generalizing state with
  | zero =>
      cases hs : literalStateAccept n budget state <;>
        simp [literalBellmanCount, literalSuccessfulSuffixes, literalSuffixes,
          Finset.filter_singleton, literalStateRun, hs]
  | succ h ih =>
      rw [literalSuccessfulSuffixes_succ, Finset.card_biUnion]
      · simp [literalBellmanCount, Finset.card_image_of_injective _
          (List.cons_injective), ih]
      · intro a _ b _ hne
        apply Finset.disjoint_left.mpr
        intro xs ha hb
        obtain ⟨as, _, has⟩ := Finset.mem_image.mp ha
        obtain ⟨bs, _, hbs⟩ := Finset.mem_image.mp hb
        exact hne (List.cons.inj (has.trans hbs.symm)).1

#print axioms mem_literalSuccessfulSuffixes
#print axioms literalBellmanCount_eq_card

def literalPrefixFamily (n budget h : ℕ) (prefixes : Finset (List ℕ)) :
    Finset (List ℕ) :=
  prefixes.biUnion fun text =>
    (literalSuccessfulSuffixes n budget h (literalStateOf n text)).image (text ++ ·)

theorem literalPrefixFamily_eq_shared_suffixes (n budget h : ℕ)
    (prefixes : Finset (List ℕ)) (state : LiteralSearchState)
    (hsame : ∀ text ∈ prefixes, literalStateOf n text = state) :
    literalPrefixFamily n budget h prefixes =
      (prefixes.product (literalSuccessfulSuffixes n budget h state)).image
        (fun pair => pair.1 ++ pair.2) := by
  ext w
  simp only [literalPrefixFamily, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨text, ht, suffix, hs, he⟩
    exact ⟨(text, suffix), Finset.mem_product.mpr
      ⟨ht, by simpa [hsame text ht] using hs⟩, he⟩
  · rintro ⟨⟨text, suffix⟩, hm, he⟩
    obtain ⟨ht, hs⟩ := Finset.mem_product.mp hm
    exact ⟨text, ht, suffix, by simpa [hsame text ht] using hs, he⟩

theorem literalPrefixFamily_card_same_state (n budget h : ℕ)
    (prefixes : Finset (List ℕ)) (state : LiteralSearchState)
    (hsame : ∀ text ∈ prefixes, literalStateOf n text = state) :
    (literalPrefixFamily n budget h prefixes).card =
      prefixes.card * literalBellmanCount n budget h state := by
  rw [literalPrefixFamily_eq_shared_suffixes n budget h prefixes state hsame]
  have hi : Set.InjOn (fun pair : List ℕ × List ℕ => pair.1 ++ pair.2)
      (prefixes.product (literalSuccessfulSuffixes n budget h state)) := by
    intro x hx y hy he
    have hxs := (Finset.mem_product.mp hx).2
    have hys := (Finset.mem_product.mp hy).2
    have hxl := ((mem_literalSuffixes n h x.2).mp (Finset.mem_filter.mp hxs).1).1
    have hyl := ((mem_literalSuffixes n h y.2).mp (Finset.mem_filter.mp hys).1).1
    obtain ⟨hl, hr⟩ := List.append_inj' he (hxl.trans hyl.symm)
    exact Prod.ext hl hr
  rw [Finset.card_image_of_injOn hi]
  calc
    _ = prefixes.card * (literalSuccessfulSuffixes n budget h state).card :=
      Finset.card_product prefixes (literalSuccessfulSuffixes n budget h state)
    _ = _ := by rw [← literalBellmanCount_eq_card]

#print axioms literalPrefixFamily_card_same_state

end Coeff2.Charlieplex
