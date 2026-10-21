import Coeff2.ParityCycles
import Coeff2.CharlieEganComponentGraph

/-!
# Complete rotation courses with phase detours

Literal rotation and marked-loop laws, with repetitions permitted. The bounded
phase reduction preserves a full course's endpoint and occupation, not its
length: it is suitable for minimization / length-at-most, not exact-length
enumeration. The two-loop union below is an occupation theorem, not a global
completion theorem. No claim that the 46188 construction lifts is made.
-/
namespace Coeff2.Charlieplex.PhaseDetour
open Finset EganOccupationLift EganComponentGraph

def departure (p : List ℕ) (q : ℕ) : List ℕ := p.rotate (p.length - 1 + q)
def courseNext (p : List ℕ) : List ℕ := door (departure p 0)
def courseOccupation (p : List ℕ) (q : ℕ) : Finset (List ℕ) :=
  (range (p.length + q)).image (fun i => p.rotate i)

/-- The initial word is included, so n+q windows are emitted by n-1+q appends. -/
theorem occupation_saturated (p : List ℕ) (hp : 0 < p.length) (q : ℕ) :
    courseOccupation p q = courseOccupation p 0 := by
  ext w
  simp only [courseOccupation, mem_image, mem_range, Nat.add_zero]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i % p.length, Nat.mod_lt i hp, List.rotate_mod p i⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩

theorem departure_residue (p : List ℕ) (q : ℕ) :
    departure p q = departure p (q % p.length) := by
  unfold departure
  rw [← List.rotate_rotate, ← List.rotate_rotate]
  simpa only [List.length_rotate] using
    (List.rotate_mod (p.rotate (p.length - 1)) q).symm

/-- Same actual exit and same union with every prior occupation set. -/
theorem phase_residue_preserves_state (p : List ℕ) (hp : 0 < p.length)
    (q : ℕ) (occupied : Finset (List ℕ)) :
    (departure p q, occupied ∪ courseOccupation p q) =
    (departure p (q % p.length), occupied ∪ courseOccupation p (q % p.length)) := by
  rw [departure_residue, occupation_saturated p hp q,
    occupation_saturated p hp (q % p.length)]

theorem phase_residue_cost (n q : ℕ) :
    (n - 1 + q) = (n - 1 + q % n) + n * (q / n) := by
  have := Nat.mod_add_div q n
  omega

/-- A whole extra lap is strictly dominated once the orbit is covered. -/
theorem full_lap_strictly_costlier (n q : ℕ) (hn : 0 < n) (hq : n ≤ q) :
    n - 1 + q % n < n - 1 + q := by
  have := Nat.mod_lt q hn
  omega

/-- Extra turns enter a different ordinary course, rather than introducing
an unrelated abstract switch. -/
theorem course_transport (p : List ℕ) (q : ℕ) :
    door (departure p q) = courseNext (p.rotate q) := by
  unfold courseNext departure
  rw [List.length_rotate, List.rotate_rotate, Nat.add_zero, Nat.add_comm]

theorem rotate_departure {n : ℕ} {p : List ℕ} (hn : 1 ≤ n)
    (hp : IsPermWord n p) (q : ℕ) : rho (departure p q) = p.rotate q := by
  unfold rho departure
  rw [List.rotate_rotate, hp.length]
  have he : n - 1 + q + 1 = n + q := by omega
  rw [he, ← hp.length, ← List.rotate_rotate, List.rotate_length]

/-- The held-symbol marked-loop label is exactly the label at shifted entry. -/
theorem detour_marked_loop {n : ℕ} {p : List ℕ} (hn : 2 ≤ n)
    (hp : IsPermWord n p) (q : ℕ) :
    genLoop (door (departure p q)) = genLoop (p.rotate q) := by
  have h := genLoop_door_eq_genLoop_rho hn
    (isPermWord_rotate hp (p.length - 1 + q))
  change genLoop (door (departure p q)) = genLoop (rho (departure p q)) at h
  exact h.trans (congrArg genLoop (rotate_departure (by omega) hp q))

/-- Zero detour stays in the original marked loop. -/
theorem ordinary_course_loop {n : ℕ} {p : List ℕ} (hn : 2 ≤ n)
    (hp : IsPermWord n p) : genLoop (courseNext p) = genLoop p := by
  simpa [courseNext] using detour_marked_loop hn hp 0

section AdjacentLoops
variable {α : Type*} [DecidableEq α]

/-- Pointed representatives of two adjacent-marker loops share exactly the
two opposite orders of the adjacent markers; every symbol is retained. -/
theorem adjacent_fiber_intersection (a b : α) (t : List α)
    (hab : a ≠ b) (ha : a ∉ t) (hb : b ∉ t) :
    insertionFiber a (b :: t) ∩ insertionFiber b (a :: t) =
      {a :: b :: t, b :: a :: t} := by
  rw [fiber_intersection_two_candidates a b b a t t
    (by simp [hab, ha]) (by simp [hab.symm, hb]) hab.symm]
  apply filter_eq_self.mpr
  intro w hw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with rfl | rfl
  · apply mem_inter.mpr
    constructor
    · exact mem_insertionFiber.mpr ⟨0, by omega, by simp⟩
    · exact mem_insertionFiber.mpr ⟨1, by simp, by simp⟩
  · apply mem_inter.mpr
    constructor
    · exact mem_insertionFiber.mpr ⟨1, by simp, by simp⟩
    · exact mem_insertionFiber.mpr ⟨0, by omega, by simp⟩

theorem adjacent_fiber_intersection_card (a b : α) (t : List α)
    (hab : a ≠ b) (ha : a ∉ t) (hb : b ∉ t) :
    (insertionFiber a (b :: t) ∩ insertionFiber b (a :: t)).card = 2 := by
  rw [adjacent_fiber_intersection a b t hab ha hb]
  simp [hab]

/-- With a common pointing symbol, n = length(t)+3. Thus this is 2n-4
distinct rotation cycles, not 2(n-1) independently occupiable cycles. -/
theorem adjacent_fiber_union_card (a b : α) (t : List α)
    (hab : a ≠ b) (ha : a ∉ t) (hb : b ∉ t) :
    (insertionFiber a (b :: t) ∪ insertionFiber b (a :: t)).card =
      2 * t.length + 2 := by
  have hi := adjacent_fiber_intersection_card a b t hab ha hb
  have hleft := insertionFiber_card a (b :: t) (by simp [hab, ha])
  have hright := insertionFiber_card b (a :: t) (by simp [hab.symm, hb])
  have hsum := card_union_add_card_inter (insertionFiber a (b :: t))
    (insertionFiber b (a :: t))
  simp only [List.length_cons] at hleft hright
  omega

/-- Bridge to literal marked-cycle permutation sets from the existing Egan
module: the two common roots stand for two entire rotation orbits. -/
theorem adjacent_marked_cycles_intersection (z a b : α) (t : List α)
    (hta : (z :: a :: t).Nodup) (htb : (z :: b :: t).Nodup)
    (ha : a ∉ z :: b :: t) (hb : b ∉ z :: a :: t) :
    markedCycle a (z :: b :: t) ∩ markedCycle b (z :: a :: t) =
      rootedOrbits z {a :: b :: t, b :: a :: t} := by
  rw [component_intersection z a b (b :: t) (a :: t) htb hta ha hb]
  rw [adjacent_fiber_intersection a b t
    (fun h => ha (by simp [h])) (fun h => ha (by simp [h]))
    (fun h => hb (by simp [h]))]

end AdjacentLoops

/-- Conservation of orbit slots when the observed deficits -2,-2,+4 are
kept fixed. This count alone does not imply equality of literal footprints. -/
theorem balanced_packet_counts (n : ℕ) (hn : 3 ≤ n) :
    2 * (n - 3) + (n + 3) = 3 * (n - 1) := by omega

theorem balanced_long_within_two_loop_capacity (n : ℕ) (hn : 3 ≤ n) :
    n + 3 ≤ 2 * n - 4 ↔ 7 ≤ n := by omega

/-- Promoting all three sizes by their distance from the top radix is not
the same as preserving the balanced deficit pattern; it balances only at 8. -/
theorem naive_packet_scaling_balances_only_at_eight (n : ℕ) (hn : 3 ≤ n) :
    2 * (n - 3) + (2 * n - 5) = 3 * (n - 1) ↔ n = 8 := by omega

/-- Exact budget in the explicitly restricted class C1=(n-1)! and
C2=(n-2)!. The caller must establish the literal length identity; this
theorem deliberately does not infer it for arbitrary superpermutations. -/
theorem restricted_budget_iff (base L repeats deep saving n : ℕ)
    (hledger : L = base + repeats + deep) :
    L + saving ≤ base + (n - 3).factorial ↔
      repeats + deep + saving ≤ (n - 3).factorial := by omega

/-- Nonnegative future phase and bridge charges cannot rescue an already
overspent prefix, when the final ledger class is fixed as above. -/
theorem overspent_prefix_rejects (spent future budget : ℕ)
    (hover : budget < spent) : ¬ spent + future ≤ budget := by omega

/-- The literal witness's *six-piece* occupation packet has this parameterized
count. It is not obtained by keeping the three-group multiplicities fixed. -/
theorem two_marker_packet_count (n : ℤ) :
    (n - 4) * (n - 3) + 2 * (2 * n - 5) = (n - 1) * (n - 2) := by ring

def pieceCost (n cycles extra : ℤ) : ℤ := (n + 1) * cycles + n - 2 + extra

/-- Same number of pieces and cycles, two repetitions: +2 internal symbols.
Coverage of the parametric packet is checked independently in C++, not assumed
to follow from this polynomial identity. -/
theorem two_marker_packet_internal_cost (n : ℤ) :
    (n - 4) * pieceCost n (n - 3) 0 + 2 * pieceCost n (2 * n - 5) 1 =
      (n - 2) * pieceCost n (n - 1) 0 + 2 := by unfold pieceCost; ring

/-- The exchanged internal paths are longer. Savings must come from overlaps
at the changed ports. These overlap sums must be realized, not just bounded. -/
theorem two_marker_packet_net_saving (internal oldOverlap newOverlap : ℤ) :
    (internal - oldOverlap) - (internal + 2 - newOverlap) =
      newOverlap - oldOverlap - 2 := by ring

end Coeff2.Charlieplex.PhaseDetour
