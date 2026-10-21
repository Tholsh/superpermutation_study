import Coeff2.CharlieTwoMarkerPartition

/-!
# Literal seam assembly and its exact length ledger

This is the output-side interface for packet constructions. A seam must match
actual symbols; independently optimistic overlaps are not accepted. The module
does not prove the remaining course-generator-to-packet-footprint obligation.
-/
namespace Coeff2.Charlieplex.PacketAssembly
variable {α : Type*}

def glue (u v : List α) (k : ℕ) : List α := u ++ v.drop k

def IsSeam (u v : List α) (k : ℕ) : Prop :=
  k ≤ u.length ∧ k ≤ v.length ∧ u.drop (u.length - k) = v.take k

theorem glue_eq_prefix_append (u v : List α) (k : ℕ) (h : IsSeam u v k) :
    glue u v k = u.take (u.length - k) ++ v := by
  unfold glue
  conv_lhs => lhs; rw [← List.take_append_drop (u.length - k) u]
  rw [List.append_assoc, h.2.2, List.take_append_drop]

theorem glue_left (u v : List α) (k : ℕ) : u.IsInfix (glue u v k) :=
  List.infix_append_left

theorem glue_right (u v : List α) (k : ℕ) (h : IsSeam u v k) :
    v.IsInfix (glue u v k) := by
  rw [glue_eq_prefix_append u v k h]
  exact List.infix_append_right

theorem glue_length (u v : List α) (k : ℕ) (h : IsSeam u v k) :
    (glue u v k).length + k = u.length + v.length := by
  simp only [glue, List.length_append, List.length_drop]
  have := h.2.1
  omega

/-- A certificate retains the word, every input piece, and the realized seam
total. Any ordering is allowed; every seam is checked against the accumulated
word. Zero overlap is always possible. -/
inductive Assembled : List (List α) → List α → ℕ → Prop
  | empty : Assembled [] [] 0
  | append {pieces : List (List α)} {w : List α} {overlap : ℕ}
      (prev : Assembled pieces w overlap) (p : List α) (k : ℕ)
      (seam : IsSeam w p k) :
      Assembled (pieces ++ [p]) (glue w p k) (overlap + k)

theorem assembled_length {pieces : List (List α)} {w : List α} {overlap : ℕ}
    (h : Assembled pieces w overlap) :
    w.length + overlap = (pieces.map List.length).sum := by
  induction h with
  | empty => simp
  | @append ps w o prev p k hs ih =>
    have hg := glue_length w p k hs
    simp only [List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

theorem assembled_contains {pieces : List (List α)} {w : List α} {overlap : ℕ}
    (h : Assembled pieces w overlap) : ∀ p ∈ pieces, p.IsInfix w := by
  induction h with
  | empty => simp
  | @append ps w o prev p k hs ih =>
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | he
    · exact (ih q hq).trans (glue_left w p k)
    · subst q; exact glue_right w p k hs

/-- Literal permutation coverage is preserved by certified seams, including
repeated windows. No injectivity or corpus length is assumed. -/
theorem assembled_covers {pieces : List (List α)} {w : List α} {overlap : ℕ}
    (h : Assembled pieces w overlap) (alphabet : List α)
    (hc : ∀ p : List α, p.Perm alphabet → ∃ piece ∈ pieces, p.IsInfix piece) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix w := by
  intro p hp
  obtain ⟨piece, hm, hi⟩ := hc p hp
  exact hi.trans (assembled_contains h piece hm)

/-- For the parameterized packet family, supply its independently proved or
checked internal-length sum. The conclusion concerns the actual output word. -/
theorem packet_length_ledger {pieces : List (List α)} {w : List α} {overlap : ℕ}
    (h : Assembled pieces w overlap) (n switchedPackets : ℕ)
    (hcost : (pieces.map List.length).sum =
      (n - 2).factorial * (n*n + n - 3) + 2*switchedPackets) :
    w.length + overlap = (n - 2).factorial * (n*n + n - 3) + 2*switchedPackets :=
  (assembled_length h).trans hcost

theorem target_length_iff {pieces : List (List α)} {w : List α} {overlap : ℕ}
    (h : Assembled pieces w overlap) (target : ℕ) :
    w.length ≤ target ↔ (pieces.map List.length).sum ≤ target + overlap := by
  have := assembled_length h
  omega

#print axioms glue_length
#print axioms assembled_length
#print axioms assembled_covers
#print axioms packet_length_ledger
#print axioms target_length_iff
end Coeff2.Charlieplex.PacketAssembly
