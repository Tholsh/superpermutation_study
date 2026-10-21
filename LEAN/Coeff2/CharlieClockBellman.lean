import Coeff2.CharlieClockWrapCount

/-!
# Exact three-type clock optimization

The recurrence retains the current phase and all three remaining counts.
Its correctness theorem ranges over every ordered type word of those counts.
The model is arbitrary: the optimization proof does not assume particular
clock prices, commutativity, or admissibility of literal attachments.
-/
namespace Coeff2.Charlieplex.ClockBellman

open ClockMacro

inductive Kind | packet | connector | backward
  deriving DecidableEq, Repr

structure Model (m : ℕ) where
  packet : Macro m
  connector : Macro m
  backward : Macro m

def Model.move {m : ℕ} (C : Model m) : Kind → Macro m
  | .packet => C.packet
  | .connector => C.connector
  | .backward => C.backward

def wordCost {m : ℕ} (C : Model m) (xs : List Kind) (j : ZMod m) : ℕ :=
  (compile (xs.map C.move)).cost j

@[simp] theorem wordCost_nil {m : ℕ} (C : Model m) (j : ZMod m) :
    wordCost C [] j = 0 := rfl

@[simp] theorem wordCost_cons {m : ℕ} (C : Model m) (k : Kind)
    (xs : List Kind) (j : ZMod m) :
    wordCost C (k :: xs) j = (C.move k).cost j +
      wordCost C xs (j + (C.move k).shift) := rfl

/-- The entire type-word family, not one representative per cost profile. -/
inductive Schedule : ℕ → ℕ → ℕ → List Kind → Prop
  | nil : Schedule 0 0 0 []
  | packet {f o b xs} : Schedule f o b xs → Schedule (f+1) o b (.packet :: xs)
  | connector {f o b xs} : Schedule f o b xs → Schedule f (o+1) b (.connector :: xs)
  | backward {f o b xs} : Schedule f o b xs → Schedule f o (b+1) (.backward :: xs)

theorem Schedule.length {f o b : ℕ} {xs : List Kind} (h : Schedule f o b xs) :
    xs.length = f + o + b := by
  induction h <;> simp_all <;> omega

theorem Schedule.counts {f o b : ℕ} {xs : List Kind} (h : Schedule f o b xs) :
    xs.count .packet = f ∧ xs.count .connector = o ∧ xs.count .backward = b := by
  induction h <;> simp_all

theorem schedule_counts (xs : List Kind) :
    Schedule (xs.count .packet) (xs.count .connector) (xs.count .backward) xs := by
  induction xs with
  | nil => exact .nil
  | cons k xs ih =>
    cases k
    · simpa using Schedule.packet ih
    · simpa using Schedule.connector ih
    · simpa using Schedule.backward ih

theorem schedule_iff_counts {f o b : ℕ} {xs : List Kind} :
    Schedule f o b xs ↔
      xs.count .packet = f ∧ xs.count .connector = o ∧ xs.count .backward = b := by
  refine ⟨Schedule.counts, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  exact schedule_counts xs

theorem Schedule.perm {f o b : ℕ} {xs ys : List Kind}
    (hx : Schedule f o b xs) (hy : Schedule f o b ys) : xs.Perm ys := by
  apply List.perm_iff_count.mpr
  intro k
  cases k with
  | packet => exact hx.counts.1.trans hy.counts.1.symm
  | connector => exact hx.counts.2.1.trans hy.counts.2.1.symm
  | backward => exact hx.counts.2.2.trans hy.counts.2.2.symm

/-- Structural count recurrence. Every available first move is included.
No numeric infinity sentinel is needed for unavailable moves. -/
def optimum {m : ℕ} (C : Model m) (f o b : ℕ) (j : ZMod m) : ℕ :=
  match f, o, b with
  | 0, 0, 0 => 0
  | f+1, 0, 0 => C.packet.cost j + optimum C f 0 0 (j + C.packet.shift)
  | 0, o+1, 0 => C.connector.cost j + optimum C 0 o 0 (j + C.connector.shift)
  | 0, 0, b+1 => C.backward.cost j + optimum C 0 0 b (j + C.backward.shift)
  | f+1, o+1, 0 => min
      (C.packet.cost j + optimum C f (o+1) 0 (j + C.packet.shift))
      (C.connector.cost j + optimum C (f+1) o 0 (j + C.connector.shift))
  | f+1, 0, b+1 => min
      (C.packet.cost j + optimum C f 0 (b+1) (j + C.packet.shift))
      (C.backward.cost j + optimum C (f+1) 0 b (j + C.backward.shift))
  | 0, o+1, b+1 => min
      (C.connector.cost j + optimum C 0 o (b+1) (j + C.connector.shift))
      (C.backward.cost j + optimum C 0 (o+1) b (j + C.backward.shift))
  | f+1, o+1, b+1 => min
      (C.packet.cost j + optimum C f (o+1) (b+1) (j + C.packet.shift))
      (min (C.connector.cost j + optimum C (f+1) o (b+1) (j + C.connector.shift))
           (C.backward.cost j + optimum C (f+1) (o+1) b (j + C.backward.shift)))
termination_by f + o + b

theorem optimum_le_packet {m : ℕ} (C : Model m) (f o b : ℕ) (j : ZMod m) :
    optimum C (f+1) o b j ≤ C.packet.cost j + optimum C f o b (j + C.packet.shift) := by
  cases o <;> cases b <;> rw [optimum]
  all_goals exact min_le_left _ _

theorem optimum_le_connector {m : ℕ} (C : Model m) (f o b : ℕ) (j : ZMod m) :
    optimum C f (o+1) b j ≤ C.connector.cost j + optimum C f o b (j + C.connector.shift) := by
  cases f <;> cases b <;> rw [optimum]
  · exact min_le_left _ _
  · exact min_le_right _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem optimum_le_backward {m : ℕ} (C : Model m) (f o b : ℕ) (j : ZMod m) :
    optimum C f o (b+1) j ≤ C.backward.cost j + optimum C f o b (j + C.backward.shift) := by
  cases f <;> cases o <;> rw [optimum]
  · exact min_le_right _ _
  · exact min_le_right _ _
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem optimum_le_every_word {m f o b : ℕ} (C : Model m) {xs : List Kind}
    (h : Schedule f o b xs) (j : ZMod m) : optimum C f o b j ≤ wordCost C xs j := by
  induction h generalizing j with
  | nil => rw [optimum, wordCost_nil]
  | @packet f o b xs h ih =>
    exact le_trans (optimum_le_packet C f o b j) (Nat.add_le_add_left (ih _) _)
  | @connector f o b xs h ih =>
    exact le_trans (optimum_le_connector C f o b j) (Nat.add_le_add_left (ih _) _)
  | @backward f o b xs h ih =>
    exact le_trans (optimum_le_backward C f o b j) (Nat.add_le_add_left (ih _) _)

private theorem witness_min {α : Type*} (P : α → Prop) (c : α → ℕ) {a b : ℕ}
    (ha : ∃ x, P x ∧ c x = a) (hb : ∃ x, P x ∧ c x = b) :
    ∃ x, P x ∧ c x = min a b := by
  by_cases h : a ≤ b
  · simpa [min_eq_left h] using ha
  · simpa [min_eq_right (by omega : b ≤ a)] using hb

private theorem witness_packet {m f o b v : ℕ} (C : Model m) (j : ZMod m)
    (h : ∃ xs, Schedule f o b xs ∧ wordCost C xs (j + C.packet.shift) = v) :
    ∃ xs, Schedule (f+1) o b xs ∧ wordCost C xs j = C.packet.cost j + v := by
  obtain ⟨xs, hs, hc⟩ := h
  exact ⟨.packet :: xs, .packet hs, by simpa [Model.move] using congrArg (C.packet.cost j + ·) hc⟩

private theorem witness_connector {m f o b v : ℕ} (C : Model m) (j : ZMod m)
    (h : ∃ xs, Schedule f o b xs ∧ wordCost C xs (j + C.connector.shift) = v) :
    ∃ xs, Schedule f (o+1) b xs ∧ wordCost C xs j = C.connector.cost j + v := by
  obtain ⟨xs, hs, hc⟩ := h
  exact ⟨.connector :: xs, .connector hs, by simpa [Model.move] using congrArg (C.connector.cost j + ·) hc⟩

private theorem witness_backward {m f o b v : ℕ} (C : Model m) (j : ZMod m)
    (h : ∃ xs, Schedule f o b xs ∧ wordCost C xs (j + C.backward.shift) = v) :
    ∃ xs, Schedule f o (b+1) xs ∧ wordCost C xs j = C.backward.cost j + v := by
  obtain ⟨xs, hs, hc⟩ := h
  exact ⟨.backward :: xs, .backward hs, by simpa [Model.move] using congrArg (C.backward.cost j + ·) hc⟩

theorem optimum_attained {m : ℕ} (C : Model m) (f o b : ℕ) (j : ZMod m) :
    ∃ xs, Schedule f o b xs ∧ wordCost C xs j = optimum C f o b j := by
  cases f with
  | zero =>
    cases o with
    | zero =>
      cases b with
      | zero => exact ⟨[], .nil, by rw [optimum, wordCost_nil]⟩
      | succ b =>
        rw [optimum]
        exact witness_backward C j (optimum_attained C 0 0 b _)
    | succ o =>
      cases b with
      | zero =>
        rw [optimum]
        exact witness_connector C j (optimum_attained C 0 o 0 _)
      | succ b =>
        rw [optimum]
        exact witness_min _ _
          (witness_connector C j (optimum_attained C 0 o (b+1) _))
          (witness_backward C j (optimum_attained C 0 (o+1) b _))
  | succ f =>
    cases o with
    | zero =>
      cases b with
      | zero =>
        rw [optimum]
        exact witness_packet C j (optimum_attained C f 0 0 _)
      | succ b =>
        rw [optimum]
        exact witness_min _ _
          (witness_packet C j (optimum_attained C f 0 (b+1) _))
          (witness_backward C j (optimum_attained C (f+1) 0 b _))
    | succ o =>
      cases b with
      | zero =>
        rw [optimum]
        exact witness_min _ _
          (witness_packet C j (optimum_attained C f (o+1) 0 _))
          (witness_connector C j (optimum_attained C (f+1) o 0 _))
      | succ b =>
        rw [optimum]
        exact witness_min _ _
          (witness_packet C j (optimum_attained C f (o+1) (b+1) _))
          (witness_min _ _
            (witness_connector C j (optimum_attained C (f+1) o (b+1) _))
            (witness_backward C j (optimum_attained C (f+1) (o+1) b _)))
termination_by f + o + b

theorem feasible_iff {m : ℕ} (C : Model m) (f o b spent budget : ℕ) (j : ZMod m) :
    (∃ xs, Schedule f o b xs ∧ spent + wordCost C xs j ≤ budget) ↔
      spent + optimum C f o b j ≤ budget := by
  constructor
  · rintro ⟨xs, hs, hc⟩
    exact le_trans (Nat.add_le_add_left (optimum_le_every_word C hs j) spent) hc
  · intro h
    obtain ⟨xs, hs, hc⟩ := optimum_attained C f o b j
    exact ⟨xs, hs, by simpa [hc] using h⟩

theorem reject_all_orders {m : ℕ} (C : Model m) (f o b spent budget : ℕ) (j : ZMod m)
    (h : budget < spent + optimum C f o b j) :
    ∀ xs, Schedule f o b xs → budget < spent + wordCost C xs j := by
  intro xs hs
  exact lt_of_lt_of_le h (Nat.add_le_add_left (optimum_le_every_word C hs j) spent)

end Coeff2.Charlieplex.ClockBellman
