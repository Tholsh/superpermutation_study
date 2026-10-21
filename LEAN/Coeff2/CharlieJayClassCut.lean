import Mathlib

/-! A class connectivity cut for a single parent circuit, independent of N.
It is invalid to impose this hypothesis on an arbitrary multi-parent cover. -/
namespace Coeff2.Charlieplex.JayClassCut

def advance {α : Type*} (f : α → α) (x : α) : ℕ → α
  | 0 => x
  | n+1 => f (advance f x n)

theorem walk_escapes {α : Type*} (f : α → α) (S : Set α) (x : α)
    (n : ℕ) (hx : x ∈ S) (hn : advance f x n ∉ S) :
    ∃ i, i < n ∧ advance f x i ∈ S ∧ f (advance f x i) ∉ S := by
  induction n with
  | zero => exact False.elim (hn hx)
  | succ n ih =>
    by_cases h : advance f x n ∈ S
    · exact ⟨n, by omega, h, hn⟩
    · obtain ⟨i, hi, hin, hout⟩ := ih h
      exact ⟨i, by omega, hin, hout⟩

/-- A successor whose orbit reaches every class must exit each nonempty
proper subset. This is the exact logical premise of the solver's >=1 cuts. -/
theorem necessary_exit {α : Type*} (f : α → α) (S : Set α)
    (connected : ∀ x y, ∃ n, advance f x n = y)
    (inside : ∃ x, x ∈ S) (outside : ∃ y, y ∉ S) :
    ∃ x, x ∈ S ∧ f x ∉ S := by
  obtain ⟨x, hx⟩ := inside
  obtain ⟨y, hy⟩ := outside
  obtain ⟨n, hn⟩ := connected x y
  have hnot : advance f x n ∉ S := by rwa [hn]
  obtain ⟨i, _, hin, hout⟩ := walk_escapes f S x n hx hnot
  exact ⟨advance f x i, hin, hout⟩

#print axioms necessary_exit
end Coeff2.Charlieplex.JayClassCut
