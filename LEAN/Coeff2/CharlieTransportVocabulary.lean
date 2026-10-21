import Mathlib.Data.List.Rotate
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Forbidden clock adjacencies survive fresh-letter insertion

These are literal-list transport invariants and finite-state counting tools.
They do not claim that an improved superpermutation has been constructed,
or that the native endpoint-vocabulary count has been reflected into Lean.
-/
namespace Coeff2.Charlieplex.TransportVocabulary

variable {α : Type*}

/-- A directed pair is absent at every cyclic cut of the literal list. -/
def AvoidCyclicPair (a b : α) (w : List α) : Prop :=
  ∀ j : ℕ, ¬ [a,b].IsInfix (w.rotate j)

/-- Filtering changes the rotation distance by the number of retained
letters before the old cut. No approximation or abstract phase is assumed. -/
theorem filter_rotate (keep : α → Bool) (w : List α) (j : ℕ) :
    (w.rotate j).filter keep =
      (w.filter keep).rotate ((w.take (j % w.length)).filter keep).length := by
  have hs := congrArg (List.filter keep) (List.take_append_drop (j % w.length) w)
  rw [List.filter_append] at hs
  rw [List.rotate_eq_drop_append_take_mod, List.filter_append]
  rw [← hs, List.rotate_append_length_eq]

/-- A pair retained by a filter cannot appear before filtering unless it
also appears afterwards. This includes pairs crossing the circular cut. -/
theorem avoid_of_filter (keep : α → Bool) (a b : α) (w : List α)
    (ha : keep a = true) (hb : keep b = true)
    (h : AvoidCyclicPair a b (w.filter keep)) : AvoidCyclicPair a b w := by
  intro j hj
  have hf := hj.filter keep
  have hk : [a,b].IsInfix
      ((w.filter keep).rotate ((w.take (j % w.length)).filter keep).length) := by
    simpa only [List.filter_cons, ha, hb, List.filter_nil, if_true, filter_rotate]
      using hf
  exact h _ hk

theorem avoid_rotate (a b : α) (w : List α) (k : ℕ)
    (h : AvoidCyclicPair a b w) : AvoidCyclicPair a b (w.rotate k) := by
  intro j hj
  exact h (k+j) (by simpa only [List.rotate_rotate] using hj)

/-- Inserting a fresh letter different from the two marked letters at an
arbitrary gap preserves absence of that directed pair. -/
theorem avoid_insert [DecidableEq α] (a b z : α) (left right : List α)
    (hza : z ≠ a) (hzb : z ≠ b) (hz : z ∉ left ++ right)
    (h : AvoidCyclicPair a b (left ++ right)) :
    AvoidCyclicPair a b (left ++ z :: right) := by
  let keep : α → Bool := fun x => decide (x ≠ z)
  have he : (left ++ z :: right).filter keep = left ++ right := by
    have hl : left.filter keep = left := List.filter_eq_self.mpr (by
      intro x hx
      have hn : x ≠ z := fun e => hz (List.mem_append_left right (e ▸ hx))
      simpa [keep] using hn)
    have hr : right.filter keep = right := List.filter_eq_self.mpr (by
      intro x hx
      have hn : x ≠ z := fun e => hz (List.mem_append_right left (e ▸ hx))
      simpa [keep] using hn)
    rw [List.filter_append, List.filter_cons, hl, hr]
    simp [keep]
  apply avoid_of_filter keep a b _ (by simp [keep, Ne.symm hza])
    (by simp [keep, Ne.symm hzb])
  simpa only [he] using h

/-- A finite transport history, retaining the two marked old symbols as
old symbols. Newly inserted symbols are not allowed to impersonate them. -/
inductive FreshTransport (a b : α) : List α → List α → Prop
  | refl (w : List α) : FreshTransport a b w w
  | insert {w left right : List α} {z : α}
      (previous : FreshTransport a b w (left ++ right))
      (hza : z ≠ a) (hzb : z ≠ b) (hz : z ∉ left ++ right) :
      FreshTransport a b w (left ++ z :: right)
  | rotate {w v : List α} (previous : FreshTransport a b w v) (j : ℕ) :
      FreshTransport a b w (v.rotate j)

/-- The exclusion persists through arbitrarily many literal insertions
and representative rotations, not merely through one tested alphabet size. -/
theorem avoid_transport [DecidableEq α] {a b : α} {base result : List α}
    (history : FreshTransport a b base result) (hbase : AvoidCyclicPair a b base) :
    AvoidCyclicPair a b result := by
  induction history with
  | refl => exact hbase
  | insert previous hza hzb hz ih => exact avoid_insert _ _ _ _ _ hza hzb hz ih
  | rotate previous j ih => exact avoid_rotate _ _ _ _ ih

/-- Excluding even one impossible endpoint strictly reduces a finite state
universe. The endpoint type and its interpretation remain explicit. -/
theorem admissible_card_lt {V : Type*} [Fintype V] (P : V → Prop)
    [DecidablePred P] (v : V) (hv : ¬ P v) :
    Fintype.card {v // P v} < Fintype.card V := by
  apply Fintype.card_lt_of_injective_not_surjective
    (fun v : {v // P v} => v.val) Subtype.val_injective
  intro hs
  obtain ⟨u, hu⟩ := hs v
  exact hv (hu ▸ u.property)

/-- In the unsaturated state-count branch, one excluded endpoint saves at
least two in the bound when the overlap length is at least two. This is an
arithmetic consequence, not an existence proof for a new word. -/
theorem two_saved_from_one_state (base c v ell : ℕ)
    (hv : 1 ≤ v) (hvc : v ≤ c) (hell : 2 ≤ ell) :
    base + ell * min c (v-1) + 2 ≤ base + ell * min c v := by
  rw [Nat.min_eq_right hvc, Nat.min_eq_right (by omega : v-1 ≤ c)]
  have he : v-1+1=v := by omega
  nlinarith

#print axioms filter_rotate
#print axioms avoid_of_filter
#print axioms avoid_rotate
#print axioms avoid_insert
#print axioms avoid_transport
#print axioms admissible_card_lt
#print axioms two_saved_from_one_state
end Coeff2.Charlieplex.TransportVocabulary
