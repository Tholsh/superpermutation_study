import Coeff2.CharliePacketAssembly
import Mathlib.Data.Finset.Max

/-!
Literal phase/order assembly. No old successor, balanced circuit, or cheap
attachment is assumed. The algorithm works for arbitrary finite words.
The final budget theorem is an exact criterion, not a choice/existence theorem.
-/
namespace Coeff2.Charlieplex.PhaseOrder
open PacketAssembly
variable {α : Type*} [DecidableEq α]

instance (u v : List α) (k : ℕ) : Decidable (IsSeam u v k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def seams (u v : List α) : Finset ℕ :=
  (Finset.range (min u.length v.length + 1)).filter (IsSeam u v)

theorem zero_mem (u v : List α) : 0 ∈ seams u v := by
  simp [seams, IsSeam]

def overlap (u v : List α) : ℕ := (seams u v).max' ⟨0, zero_mem u v⟩

theorem overlap_seam (u v : List α) : IsSeam u v (overlap u v) := by
  exact (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

theorem seam_le_overlap (u v : List α) (k : ℕ) (h : IsSeam u v k) :
    k ≤ overlap u v := by
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := h.1; have := h.2.1; omega), h⟩

omit [DecidableEq α] in
theorem seam_prefix {u v w : List α} {k : ℕ} (h : IsSeam u v k)
    (hp : v.IsPrefix w) : IsSeam u w k := by
  obtain ⟨t, rfl⟩ := hp
  refine ⟨h.1, ?_, ?_⟩
  · simp only [List.length_append]; have := h.2.1; omega
  · rw [List.take_append_of_le_length h.2.1]; exact h.2.2

/-- Assemble from the right, using the maximum overlap of adjacent pieces.
This also handles contained pieces and overlaps longer than n. -/
def word : List (List α) → List α
  | [] => []
  | [p] => p
  | p :: q :: ps => glue p (word (q :: ps)) (overlap p q)

def seamSum : List (List α) → ℕ
  | [] => 0
  | [_] => 0
  | p :: q :: ps => overlap p q + seamSum (q :: ps)

theorem head_prefix (p : List α) (ps : List (List α)) :
    p.IsPrefix (word (p :: ps)) := by
  cases ps with
  | nil => exact ⟨[], by simp [word]⟩
  | cons q ps => exact ⟨_, rfl⟩

theorem word_length (ps : List (List α)) :
    (word ps).length + seamSum ps = (ps.map List.length).sum := by
  induction ps with
  | nil => simp [word, seamSum]
  | cons p ps ih =>
    cases ps with
    | nil => simp [word, seamSum]
    | cons q qs =>
      have h := glue_length p (word (q :: qs)) (overlap p q)
        (seam_prefix (overlap_seam p q) (head_prefix q qs))
      simp only [word, seamSum, List.map_cons, List.sum_cons] at *
      omega

theorem word_contains (ps : List (List α)) :
    ∀ p ∈ ps, p.IsInfix (word ps) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    cases ps with
    | nil => intro q h; have he := List.mem_singleton.mp h; subst q; exact ⟨[], [], by simp [word]⟩
    | cons q qs =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact glue_left _ _ _
      · exact (ih t ht).trans (glue_right _ _ _
          (seam_prefix (overlap_seam p q) (head_prefix q qs)))

/-- Order is any permutation of the whole phase-selected literal catalog. -/
theorem reordered_covers (catalog ordered : List (List α))
    (ho : ordered.Perm catalog) (alphabet : List α)
    (hc : ∀ p : List α, p.Perm alphabet → ∃ w ∈ catalog, p.IsInfix w) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix (word ordered) := by
  intro p hp
  obtain ⟨w, hw, hi⟩ := hc p hp
  exact hi.trans (word_contains ordered w (ho.mem_iff.mpr hw))

/-- Phases are shared by all children of one parent. Different parents need
not share a phase, port, or successor. -/
def phaseCatalog {ι : Type*} (parents : List ι)
    (packets : ι → ℕ → List (List α)) (phase : ι → ℕ) : List (List α) :=
  parents.flatMap (fun i => packets i (phase i))

/-- Exact literal occupation, not just equal cardinalities, is the interface
to the packet generator. This theorem does NOT fill that generator obligation
with a course-set equality: it asks for actual literal infix witnesses. -/
theorem phase_order_covers {ι : Type*} (parents : List ι)
    (packets : ι → ℕ → List (List α)) (oldPhase newPhase : ι → ℕ)
    (ordered : List (List α)) (alphabet : List α)
    (hc : ∀ p : List α, p.Perm alphabet →
      ∃ w ∈ phaseCatalog parents packets oldPhase, p.IsInfix w)
    (hinvariant : ∀ i ∈ parents, ∀ p : List α, p.Perm alphabet →
      ((∃ w ∈ packets i (oldPhase i), p.IsInfix w) ↔
       (∃ w ∈ packets i (newPhase i), p.IsInfix w)))
    (ho : ordered.Perm (phaseCatalog parents packets newPhase)) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix (word ordered) := by
  apply reordered_covers _ ordered ho alphabet
  intro p hp
  obtain ⟨w, hw, hi⟩ := hc p hp
  obtain ⟨i, hm, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v, hv, hvi⟩ := (hinvariant i hm p hp).mp ⟨w, hw, hi⟩
  exact ⟨v, List.mem_flatMap.mpr ⟨i, hm, hv⟩, hvi⟩

def deficit (n : ℕ) (ps : List (List α)) : ℤ :=
  (ps.length - 1 : ℕ) * (n - 3 : ℕ) - (seamSum ps : ℤ)

/-- Integer identity: above-baseline overlaps give negative seam deficits. -/
theorem exact_ledger (n B : ℕ) (hn : 3 ≤ n)
    (catalog ordered : List (List α)) (ho : ordered.Perm catalog)
    (hlen : catalog.length = (n - 2).factorial)
    (hcost : (catalog.map List.length).sum =
      (n - 2).factorial * (n*n + n - 3) + 2*B) :
    ((word ordered).length : ℤ) =
      (n:ℤ)^2 * (n-2 : ℕ).factorial + (n-3 : ℕ) + 2*B + deficit n ordered := by
  have hl : ordered.length = (n-2).factorial := ho.length_eq.trans hlen
  have hp := Nat.factorial_pos (n-2)
  have hs := (ho.map List.length).sum_eq
  have hw := word_length ordered
  rw [hs, hcost] at hw
  have hc : (n*n + n - 3 : ℕ) = n*n + (n-3) := by omega
  have hm : ordered.length - 1 + 1 = (n-2).factorial := by omega
  have hz := congrArg (fun a : ℕ => (a:ℤ)) hw
  have hzm := congrArg (fun a : ℕ => (a:ℤ)) hm
  simp only [hc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz hzm
  unfold deficit
  nlinarith

/-- This is the obligation for the phase/order selector; it does not assume
that the selector is cheap and then call that an all-n construction. -/
theorem beats_egan_iff (n B : ℕ) (hn : 3 ≤ n)
    (catalog ordered : List (List α)) (ho : ordered.Perm catalog)
    (hlen : catalog.length = (n-2).factorial)
    (hcost : (catalog.map List.length).sum =
      (n-2).factorial * (n*n+n-3) + 2*B) :
    ((word ordered).length : ℤ) <
      (n:ℤ)^2 * (n-2 : ℕ).factorial + (n-3 : ℕ) + (n-3 : ℕ).factorial ↔
      (2*B : ℤ) + deficit n ordered < (n-3 : ℕ).factorial := by
  rw [exact_ledger n B hn catalog ordered ho hlen hcost]
  omega

theorem expanded_egan (n : ℕ) (hn : 3 ≤ n) :
    n^2 * (n-2).factorial + (n-3) + (n-3).factorial =
      n.factorial + (n-1).factorial + (n-2).factorial + (n-3).factorial + (n-3) := by
  have base (r : ℕ) :
      (r+3)^2 * (r+1).factorial + r.factorial + r =
        (r+3).factorial + (r+2).factorial + (r+1).factorial + r.factorial + r := by
    rw [Nat.factorial_succ (r+2), Nat.factorial_succ (r+1)]
    ring
  have h := base (n-3)
  have h3 : n-3+3 = n := by omega
  have h2 : n-3+2 = n-1 := by omega
  have h1 : n-3+1 = n-2 := by omega
  rw [h3, h2, h1] at h
  omega

/-- A phase exchange can change both literal ports and order. Equal total
piece lengths and equal realized overlap sums suffice for neutral length. -/
theorem neutral_exchange (ps qs : List (List α))
    (hc : (ps.map List.length).sum = (qs.map List.length).sum)
    (hs : seamSum ps = seamSum qs) : (word ps).length = (word qs).length := by
  have hp := word_length ps
  have hq := word_length qs
  omega

/-- The observed neutral seam redistribution is algebraically independent of
the frame width. Realizability at another n is a separate obligation. -/
theorem neutral_seam_trade (k : ℤ) :
    -2*(k-3) - 2*(k-2) + 10*(k-1) - 6*k = 0 := by ring

-- Kernel-checked executable smoke, including containment and a long seam.
example : word ([[0,1,2,3], [2,3], [3,4]] : List (List ℕ)) = [0,1,2,3,4] := by decide
example : overlap ([0,1,0,1,0,1] : List ℕ) [0,1,0,1,2] = 4 := by decide

#print axioms overlap_seam
#print axioms seam_le_overlap
#print axioms word_length
#print axioms reordered_covers
#print axioms phase_order_covers
#print axioms exact_ledger
#print axioms beats_egan_iff
#print axioms expanded_egan
#print axioms neutral_exchange
#print axioms neutral_seam_trade
end Coeff2.Charlieplex.PhaseOrder
