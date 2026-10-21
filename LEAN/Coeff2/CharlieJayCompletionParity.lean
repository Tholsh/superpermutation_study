import Mathlib

/-! Finite port-operator parity certificates for N7 and N8, allowing every
valid deficit. Counts include the internal cycle created by deficit1.
These constrain the standard completed-parent spelling, not all words. -/
namespace Coeff2.Charlieplex.JayCompletionParity

def tau (h d p : ℕ) : ℕ :=
  if d = 0 then (p+h-1)%h else if d = 1 then p
  else if p < h-d+1 then p+d-1 else if p = h-d+1 then d-2 else p-(h-d+2)
def step (h d : ℕ) (ps : List ℕ) := ps.map (tau h d)
/-- Constructor-recursive enumeration so finite certificates can reduce in
the kernel without relying on the optimized library permutation enumerator. -/
def insertEvery (a : ℕ) : List ℕ → List (List ℕ)
  | [] => [[a]]
  | b::bs => (a::b::bs) :: ((insertEvery a bs).map (b::·))
def permute : List ℕ → List (List ℕ)
  | [] => [[]]
  | a::as => (permute as).flatMap (insertEvery a)
def permutations (h : ℕ) := permute (List.range h)

/-- One least-labeled element per orbit of a valid permutation. -/
def orbitCount (ps : List ℕ) : ℕ :=
  (List.range ps.length).countP fun p =>
    (List.range ps.length).all fun k =>
      p ≤ Nat.rec p (fun _ q => ps[q]!) k

def run (h : ℕ) : List ℕ → List ℕ → List ℕ
  | [], ps => ps
  | d::ds, ps => run h ds (step h d ps)
def internal : List ℕ → ℕ
  | [] => 0
  | d::ds => (if d=1 then 1 else 0) + internal ds

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem local8 : ∀ ps ∈ permutations 5, ∀ d ∈ List.range 6,
    step 5 d ps ∈ permutations 5 ∧
    (orbitCount (step 5 d ps) + d + (if d=1 then 1 else 0))%2 =
      orbitCount ps %2 := by decide

theorem local7 : ∀ ps ∈ permutations 4, ∀ d ∈ List.range 5,
    step 4 d ps ∈ permutations 4 ∧
    (orbitCount (step 4 d ps) + 1 + (if d=1 then 1 else 0))%2 =
      orbitCount ps %2 := by decide

theorem accumulated8 (ds ps : List ℕ)
    (hp : ps ∈ permutations 5) (hd : ∀ d ∈ ds, d < 6) :
    run 5 ds ps ∈ permutations 5 ∧
    (orbitCount (run 5 ds ps) + ds.sum + internal ds)%2 =
      orbitCount ps %2 := by
  induction ds generalizing ps with
  | nil => simp [run, internal, hp]
  | cons d ds ih =>
    have hl := local8 ps hp d (List.mem_range.mpr (hd d (by simp)))
    have hi := ih (step 5 d ps) hl.1 (by intro a ha; exact hd a (by simp [ha]))
    refine ⟨hi.1, ?_⟩
    simp only [run, List.sum_cons, internal]
    omega

theorem accumulated7 (ds ps : List ℕ)
    (hp : ps ∈ permutations 4) (hd : ∀ d ∈ ds, d < 5) :
    run 4 ds ps ∈ permutations 4 ∧
    (orbitCount (run 4 ds ps) + ds.length + internal ds)%2 =
      orbitCount ps %2 := by
  induction ds generalizing ps with
  | nil => simp [run, internal, hp]
  | cons d ds ih =>
    have hl := local7 ps hp d (List.mem_range.mpr (hd d (by simp)))
    have hi := ih (step 4 d ps) hl.1 (by intro a ha; exact hd a (by simp [ha]))
    refine ⟨hi.1, ?_⟩
    simp only [run, List.length_cons, internal]
    omega

/-- Total completed trails: through-port cycles plus deficit1 cycles. -/
def trails (h : ℕ) (ds : List ℕ) :=
  orbitCount (run h ds (List.range h)) + internal ds

theorem eight_bill_odd (ds : List ℕ) (hd : ∀ d ∈ ds, d < 6) :
    (46080 + ds.sum + 5*trails 5 ds)%2 = 1 := by
  have hp : List.range 5 ∈ permutations 5 := by decide
  have hi := (accumulated8 ds (List.range 5) hp hd).2
  have hc : orbitCount (List.range 5) = 5 := by decide
  rw [hc] at hi
  simp only [trails]
  omega

/-- Deeper deficits do not remove the even-trail obstruction at N7:
24 rows and EVERY valid deficit, including internal deficit1 cycles. -/
theorem seven_trails_even (ds : List ℕ) (hd : ∀ d ∈ ds, d < 5)
    (hl : ds.length = 24) : trails 4 ds %2 = 0 := by
  have hp : List.range 4 ∈ permutations 4 := by decide
  have hi := (accumulated7 ds (List.range 4) hp hd).2
  have hc : orbitCount (List.range 4) = 4 := by decide
  rw [hc, hl] at hi
  simp only [trails]
  omega

theorem seven_at_least_two_trails (ds : List ℕ)
    (hd : ∀ d ∈ ds, d < 5) (hl : ds.length = 24) :
    2 ≤ trails 4 ds := by
  have hp : List.range 4 ∈ permutations 4 := by decide
  have hr := (accumulated7 ds (List.range 4) hp hd).1
  have positive : ∀ ps ∈ permutations 4, 0 < orbitCount ps := by decide
  have he := seven_trails_even ds hd hl
  have ho := positive _ hr
  simp only [trails] at *
  omega

theorem eight_bill_ne_46180 (ds : List ℕ) (hd : ∀ d ∈ ds, d < 6) :
    46080 + ds.sum + 5*trails 5 ds ≠ 46180 := by
  have h := eight_bill_odd ds hd
  omega

theorem eight_next_target (ds : List ℕ) (hd : ∀ d ∈ ds, d < 6)
    (hbound : 46080 + ds.sum + 5*trails 5 ds ≤ 46180) :
    46080 + ds.sum + 5*trails 5 ds ≤ 46179 := by
  have h := eight_bill_odd ds hd
  omega

#print axioms local8
#print axioms eight_bill_odd
#print axioms seven_trails_even
#print axioms seven_at_least_two_trails
end Coeff2.Charlieplex.JayCompletionParity
