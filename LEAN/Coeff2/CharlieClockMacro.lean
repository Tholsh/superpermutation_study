import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Ordered clock macros

A macro stores a phase displacement and the exact appended cost at every
starting phase. This compresses a fixed TYPE word, not a literal occupation
state. No exchange of literal ports or occupied permutations is asserted.
Composition is chronological: `a.then b` means perform `a`, then `b`.
-/
namespace Coeff2.Charlieplex.ClockMacro

open scoped BigOperators

structure Macro (m : ℕ) where
  shift : ZMod m
  cost : ZMod m → ℕ

@[ext] theorem Macro.ext {m : ℕ} {a b : Macro m}
    (hs : a.shift = b.shift) (hc : ∀ j, a.cost j = b.cost j) : a = b := by
  cases a
  cases b
  simp_all
  exact funext hc

def identity (m : ℕ) : Macro m := ⟨0, fun _ => 0⟩

def Macro.then {m : ℕ} (a b : Macro m) : Macro m :=
  ⟨a.shift + b.shift, fun j => a.cost j + b.cost (j + a.shift)⟩

def Macro.eval {m : ℕ} (a : Macro m) (s : ZMod m × ℕ) : ZMod m × ℕ :=
  (s.1 + a.shift, s.2 + a.cost s.1)

theorem identity_then {m : ℕ} (a : Macro m) : (identity m).then a = a := by
  ext <;> simp [identity, Macro.then]

theorem then_identity {m : ℕ} (a : Macro m) : a.then (identity m) = a := by
  ext <;> simp [identity, Macro.then]

theorem then_assoc {m : ℕ} (a b c : Macro m) :
    (a.then b).then c = a.then (b.then c) := by
  ext <;> simp [Macro.then, add_assoc]

theorem eval_then {m : ℕ} (a b : Macro m) (s : ZMod m × ℕ) :
    (a.then b).eval s = b.eval (a.eval s) := by
  simp [Macro.then, Macro.eval, add_assoc]

def compile {m : ℕ} : List (Macro m) → Macro m
  | [] => identity m
  | a :: rest => a.then (compile rest)

/-- The uncompressed clock interpreter; no assumption of commutativity. -/
def run {m : ℕ} : List (Macro m) → ZMod m × ℕ → ZMod m × ℕ
  | [], s => s
  | a :: rest, s => run rest (a.eval s)

theorem compile_correct {m : ℕ} (ops : List (Macro m)) (s : ZMod m × ℕ) :
    (compile ops).eval s = run ops s := by
  induction ops generalizing s with
  | nil => simp [compile, identity, Macro.eval, run]
  | cons a rest ih => simp only [compile, run, eval_then, ih]

theorem compile_append {m : ℕ} (xs ys : List (Macro m)) :
    compile (xs ++ ys) = (compile xs).then (compile ys) := by
  induction xs with
  | nil => simp [compile, identity_then]
  | cons a rest ih => simp only [List.cons_append, compile, ih, then_assoc]

/-- Equal increments make the phase at slot i independent of its TYPE. -/
theorem uniform_shift {m L : ℕ} (ops : Fin L → Macro m) (d : ZMod m)
    (h : ∀ i, (ops i).shift = d) :
    (compile (List.ofFn ops)).shift = (L : ZMod m) * d := by
  induction L with
  | zero => simp [compile, identity]
  | succ L ih =>
    rw [List.ofFn_succ]
    change (ops 0).shift + (compile (List.ofFn (fun i => ops i.succ))).shift = _
    rw [h, ih (fun i => ops i.succ) (fun i => h i.succ)]
    push_cast
    ring

theorem uniform_cost {m L : ℕ} (ops : Fin L → Macro m) (d : ZMod m)
    (h : ∀ i, (ops i).shift = d) (j : ZMod m) :
    (compile (List.ofFn ops)).cost j =
      ∑ i : Fin L, (ops i).cost (j + (i.val : ZMod m) * d) := by
  induction L generalizing j with
  | zero => simp [compile, identity]
  | succ L ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    change (ops 0).cost j +
      (compile (List.ofFn (fun i => ops i.succ))).cost (j + (ops 0).shift) = _
    rw [h, ih (fun i => ops i.succ) (fun i => h i.succ)]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    ring

end Coeff2.Charlieplex.ClockMacro
