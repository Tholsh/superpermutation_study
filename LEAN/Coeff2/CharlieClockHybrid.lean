import Coeff2.CharlieClockBidirectional

/-!
# Certified closed-tail Bellman algorithm

This is the recurrence used by the prototype: recurse while B remains, then
replace the whole R/O search by its closed exact minimum. Counts decrease on
every recursive call. Equality with `optimum` proves the shortcut loses no
type-clock optimum. Memoization is a separate implementation choice.
-/
namespace Coeff2.Charlieplex.ClockBellman

open ClockBudget

def hybrid {m : ℕ} (g base wrap f o b : ℕ) (j : ZMod m) : ℕ :=
  let C := clock m g base wrap
  match f, o, b with
  | f, o, 0 => lowerBound (f+o) f (wrapCount m (f+o) j.val) g
  | 0, 0, b+1 => C.backward.cost j + hybrid g base wrap 0 0 b (j + C.backward.shift)
  | f+1, 0, b+1 => min
      (C.packet.cost j + hybrid g base wrap f 0 (b+1) (j + C.packet.shift))
      (C.backward.cost j + hybrid g base wrap (f+1) 0 b (j + C.backward.shift))
  | 0, o+1, b+1 => min
      (C.connector.cost j + hybrid g base wrap 0 o (b+1) (j + C.connector.shift))
      (C.backward.cost j + hybrid g base wrap 0 (o+1) b (j + C.backward.shift))
  | f+1, o+1, b+1 => min
      (C.packet.cost j + hybrid g base wrap f (o+1) (b+1) (j + C.packet.shift))
      (min (C.connector.cost j + hybrid g base wrap (f+1) o (b+1) (j + C.connector.shift))
           (C.backward.cost j + hybrid g base wrap (f+1) (o+1) b (j + C.backward.shift)))
termination_by f + o + b

theorem hybrid_eq_optimum {m : ℕ} [NeZero m] (g base wrap f o b : ℕ) (j : ZMod m) :
    hybrid g base wrap f o b j = optimum (clock m g base wrap) f o b j := by
  cases b with
  | zero => rw [hybrid, optimum_zero_backward]
  | succ b =>
    cases f with
    | zero =>
      cases o with
      | zero => rw [hybrid, optimum, hybrid_eq_optimum g base wrap 0 0 b]
      | succ o =>
        rw [hybrid, optimum, hybrid_eq_optimum g base wrap 0 o (b+1),
          hybrid_eq_optimum g base wrap 0 (o+1) b]
    | succ f =>
      cases o with
      | zero =>
        rw [hybrid, optimum, hybrid_eq_optimum g base wrap f 0 (b+1),
          hybrid_eq_optimum g base wrap (f+1) 0 b]
      | succ o =>
        rw [hybrid, optimum, hybrid_eq_optimum g base wrap f (o+1) (b+1),
          hybrid_eq_optimum g base wrap (f+1) o (b+1),
          hybrid_eq_optimum g base wrap (f+1) (o+1) b]
termination_by f + o + b

theorem hybrid_feasible_iff {m : ℕ} [NeZero m]
    (g base wrap f o b spent budget : ℕ) (j : ZMod m) :
    (∃ xs, Schedule f o b xs ∧ spent + wordCost (clock m g base wrap) xs j ≤ budget) ↔
      spent + hybrid g base wrap f o b j ≤ budget := by
  rw [hybrid_eq_optimum]
  exact feasible_iff _ f o b spent budget j

theorem hybrid_reject_all_orders {m : ℕ} [NeZero m]
    (g base wrap f o b spent budget : ℕ) (j : ZMod m)
    (h : budget < spent + hybrid g base wrap f o b j) :
    ∀ xs, Schedule f o b xs → budget < spent + wordCost (clock m g base wrap) xs j := by
  rw [hybrid_eq_optimum] at h
  exact reject_all_orders _ f o b spent budget j h

/-- Restricting the type-word family cannot lower its optimum. The predicate
may encode actual ports/occupation, but this theorem does not supply that
encoding or assume it is complete. -/
theorem reject_restricted_family {m : ℕ} [NeZero m]
    (g base wrap f o b spent budget : ℕ) (j : ZMod m) (allowed : List Kind → Prop)
    (h : budget < spent + hybrid g base wrap f o b j) :
    ¬ ∃ xs, allowed xs ∧ Schedule f o b xs ∧
      spent + wordCost (clock m g base wrap) xs j ≤ budget := by
  rintro ⟨xs, _, hs, hc⟩
  have hh := hybrid_reject_all_orders g base wrap f o b spent budget j h xs hs
  omega

end Coeff2.Charlieplex.ClockBellman
