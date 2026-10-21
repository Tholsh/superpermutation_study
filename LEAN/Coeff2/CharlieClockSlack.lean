import Coeff2.CharlieClockHybrid

/-!
# Exact Bellman excess ledger

The clock optimum is a potential, not a literal feasibility certificate.
Every type word has exactly its initial potential plus nonnegative local
excesses as its cost. A tight budget forces every excess to vanish.
No claim that a tight move always has a literal continuation is made.
-/
namespace Coeff2.Charlieplex.ClockBellman

def potential {m : ℕ} (C : Model m) (xs : List Kind) (j : ZMod m) : ℕ :=
  optimum C (xs.count .packet) (xs.count .connector) (xs.count .backward) j

theorem potential_cons_le {m : ℕ} (C : Model m) (k : Kind)
    (xs : List Kind) (j : ZMod m) :
    potential C (k :: xs) j ≤ (C.move k).cost j +
      potential C xs (j + (C.move k).shift) := by
  cases k with
  | packet => simpa [potential, Model.move] using
      optimum_le_packet C (xs.count .packet) (xs.count .connector) (xs.count .backward) j
  | connector => simpa [potential, Model.move] using
      optimum_le_connector C (xs.count .packet) (xs.count .connector) (xs.count .backward) j
  | backward => simpa [potential, Model.move] using
      optimum_le_backward C (xs.count .packet) (xs.count .connector) (xs.count .backward) j

def excesses {m : ℕ} (C : Model m) : List Kind → ZMod m → List ℕ
  | [], _ => []
  | k :: xs, j =>
    ((C.move k).cost j + potential C xs (j + (C.move k).shift) -
      potential C (k :: xs) j) :: excesses C xs (j + (C.move k).shift)

theorem cost_eq_potential_add_excess {m : ℕ} (C : Model m)
    (xs : List Kind) (j : ZMod m) :
    wordCost C xs j = potential C xs j + (excesses C xs j).sum := by
  induction xs generalizing j with
  | nil => simp [potential, optimum, excesses]
  | cons k xs ih =>
    have hb := potential_cons_le C k xs j
    rw [wordCost_cons, ih, excesses, List.sum_cons]
    omega

theorem budget_iff_excess {m : ℕ} (C : Model m)
    (xs : List Kind) (j : ZMod m) (allowance : ℕ) :
    wordCost C xs j ≤ potential C xs j + allowance ↔
      (excesses C xs j).sum ≤ allowance := by
  rw [cost_eq_potential_add_excess]
  omega

theorem tight_iff_every_excess_zero {m : ℕ} (C : Model m)
    (xs : List Kind) (j : ZMod m) :
    wordCost C xs j = potential C xs j ↔
      ∀ e ∈ excesses C xs j, e = 0 := by
  rw [cost_eq_potential_add_excess]
  have hz : potential C xs j + (excesses C xs j).sum = potential C xs j ↔
      (excesses C xs j).sum = 0 := by omega
  rw [hz, List.sum_eq_zero_iff]

/-- Counts do not encode order or literal occupation. This only identifies
the potential already certified by the closed-tail algorithm. -/
theorem potential_eq_hybrid {m f o b : ℕ} [NeZero m]
    (g base wrap : ℕ) {xs : List Kind} (h : Schedule f o b xs) (j : ZMod m) :
    potential (clock m g base wrap) xs j = hybrid g base wrap f o b j := by
  rw [potential, h.counts.1, h.counts.2.1, h.counts.2.2, hybrid_eq_optimum]

#print axioms cost_eq_potential_add_excess
#print axioms budget_iff_excess
#print axioms tight_iff_every_excess_zero
#print axioms potential_eq_hybrid
end Coeff2.Charlieplex.ClockBellman
