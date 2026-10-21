import Coeff2.CharlieBoundarySpine

/-!
# Necessary attachment cuts for literal row payloads

Vertices below are literal boundary words. Edges are obtained from the actual
prefix and suffix of an emitted piece, not from parity or a surrogate cost.
These are necessary inequalities for a construction joining all required
endpoints in one directed component. They do not prove that a short choice
exists, nor that every superpermutation belongs to that one-component family.
The native optimizer and its numerical bounds are not reflected into Lean.
-/
namespace Coeff2.Charlieplex.LiteralAttachmentCut

variable {V α : Type*}

inductive Reach (edge : V → V → Prop) : V → V → Prop
  | refl (u : V) : Reach edge u u
  | step {u v w : V} (prev : Reach edge u v) (next : edge v w) :
      Reach edge u w

theorem reach_closed {edge : V → V → Prop} {S : V → Prop}
    (closed : ∀ u v, S u → edge u v → S v) {u v : V}
    (walk : Reach edge u v) (inside : S u) : S v := by
  induction walk with
  | refl => exact inside
  | step prev next ih => exact closed _ _ ih next

theorem reach_crosses {edge : V → V → Prop} {S : V → Prop}
    {u v : V} (walk : Reach edge u v) (inside : S u) (outside : ¬ S v) :
    ∃ a b, S a ∧ edge a b ∧ ¬ S b := by
  classical
  by_contra none
  have closed : ∀ a b, S a → edge a b → S b := by
    intro a b ha hab
    by_contra hb
    exact none ⟨a, b, ha, hab, hb⟩
  exact outside (reach_closed closed walk inside)

def head (h : ℕ) (piece : List α) : List α := piece.take h
def tail (h : ℕ) (piece : List α) : List α :=
  piece.drop (piece.length - h)

def LiteralEdge (h : ℕ) (pieces : List (List α))
    (u v : List α) : Prop :=
  ∃ piece ∈ pieces, u = head h piece ∧ v = tail h piece

def Endpoint (h : ℕ) (required : List (List α)) (u : List α) : Prop :=
  ∃ piece ∈ required, u = head h piece ∨ u = tail h piece

def JoinsRequired (h : ℕ) (pieces required : List (List α)) : Prop :=
  ∀ u v, Endpoint h required u → Endpoint h required v →
    Reach (LiteralEdge h pieces) u v

noncomputable def outgoingCount (h : ℕ) (pieces : List (List α))
    (S : List α → Prop) : ℕ := by
  classical
  exact (pieces.filter fun p => S (head h p) ∧ ¬ S (tail h p)).length

theorem literal_crossing {h : ℕ} {pieces : List (List α)}
    {S : List α → Prop} {u v : List α}
    (walk : Reach (LiteralEdge h pieces) u v)
    (inside : S u) (outside : ¬ S v) :
    ∃ piece ∈ pieces, S (head h piece) ∧ ¬ S (tail h piece) := by
  obtain ⟨a, b, ha, ⟨p, hp, ea, eb⟩, hb⟩ := reach_crosses walk inside outside
  exact ⟨p, hp, ea ▸ ha, eb ▸ hb⟩

theorem outgoing_pos {h : ℕ} {pieces : List (List α)} {S : List α → Prop}
    (crossing : ∃ p ∈ pieces, S (head h p) ∧ ¬ S (tail h p)) :
    1 ≤ outgoingCount h pieces S := by
  classical
  obtain ⟨p, hp, hi, ho⟩ := crossing
  have hm : p ∈ pieces.filter (fun q => S (head h q) ∧ ¬ S (tail h q)) := by
    simp [hp, hi, ho]
  have hn : pieces.filter (fun q => S (head h q) ∧ ¬ S (tail h q)) ≠ [] := by
    intro he
    rw [he] at hm
    simp at hm
  have hl := List.length_pos_of_ne_nil hn
  unfold outgoingCount
  omega

noncomputable def indicator (P : Prop) : ℤ := by
  classical
  exact if P then 1 else 0

/-- Both endpoint witnesses are conditional. A later selection is allowed
to move all required occupation inside S; no fixed-root assumption is hidden. -/
theorem conditional_literal_cut {h : ℕ} {pieces required : List (List α)}
    {S : List α → Prop}
    (joins : JoinsRequired h pieces required) :
    (outgoingCount h pieces S : ℤ) ≥
      indicator (∃ u, Endpoint h required u ∧ S u) +
      indicator (∃ v, Endpoint h required v ∧ ¬ S v) - 1 := by
  classical
  by_cases hi : ∃ u, Endpoint h required u ∧ S u
  · by_cases ho : ∃ v, Endpoint h required v ∧ ¬ S v
    · have hp : 1 ≤ outgoingCount h pieces S := by
        obtain ⟨u, hu, su⟩ := hi
        obtain ⟨v, hv, sv⟩ := ho
        exact outgoing_pos (literal_crossing (joins u v hu hv) su sv)
      simp only [indicator, if_pos hi, if_pos ho]
      omega
    · simp only [indicator, if_pos hi, if_neg ho]
      omega
  · by_cases ho : ∃ v, Endpoint h required v ∧ ¬ S v <;>
      simp [indicator, hi, ho]

/-- If another occupation class forces an outside endpoint, only the inside
class witness remains conditional. Native one-hot selection turns that
indicator into the sum of selected choices having an endpoint in S. -/
theorem compulsory_outside_cut {h : ℕ} {pieces required : List (List α)}
    {S : List α → Prop} (joins : JoinsRequired h pieces required)
    (outside : ∃ v, Endpoint h required v ∧ ¬ S v) :
    (outgoingCount h pieces S : ℤ) ≥
      indicator (∃ u, Endpoint h required u ∧ S u) := by
  have hc := conditional_literal_cut (S := S) joins
  simpa only [indicator, if_pos outside, add_sub_cancel_right] using hc

/-- Counts incoming arcs of a finite directed multigraph. Parallel arcs
are intentionally counted repeatedly, as in an integer connector ledger. -/
noncomputable def incomingCount (edges : List (V × V)) (S : V → Prop) : ℕ := by
  classical
  exact (edges.filter fun e => ¬ S e.1 ∧ S e.2).length

theorem incoming_pos {edges : List (V × V)} {S : V → Prop}
    (crossing : ∃ a b, (a,b) ∈ edges ∧ ¬ S a ∧ S b) :
    1 ≤ incomingCount edges S := by
  classical
  obtain ⟨a, b, he, ha, hb⟩ := crossing
  have hm : (a,b) ∈ edges.filter (fun e => ¬ S e.1 ∧ S e.2) := by
    simp [he, ha, hb]
  have hn : edges.filter (fun e => ¬ S e.1 ∧ S e.2) ≠ [] := by
    intro hn
    rw [hn] at hm
    simp at hm
  have hp := List.length_pos_of_ne_nil hn
  unfold incomingCount
  omega

/-- Unlike the mutual-reachability cut, this applies to an OPEN Euler trail.
The chosen source may be anywhere. Every required endpoint must be reached
from it; if S contains that source, its presence cancels the cut obligation.
This is the inequality used by the two-terminal bucket-network model. -/
theorem rooted_incoming_cut (edges : List (V × V)) (S Q : V → Prop) (root : V)
    (reaches : ∀ v, Q v → Reach (fun a b => (a,b) ∈ edges) root v) :
    (incomingCount edges S : ℤ) + indicator (S root) ≥
      indicator (∃ v, Q v ∧ S v) := by
  classical
  by_cases hi : ∃ v, Q v ∧ S v
  · by_cases hr : S root
    · simp [indicator, hi, hr]
    · have hp : 1 ≤ incomingCount edges S := by
        obtain ⟨v, hq, hs⟩ := hi
        have crossing := reach_crosses (S := fun a => ¬ S a)
          (reaches v hq) hr (by simpa using hs)
        obtain ⟨a, b, ha, he, hb⟩ := crossing
        exact incoming_pos ⟨a, b, he, ha, by simpa using hb⟩
      simp only [indicator, if_pos hi, if_neg hr]
      omega
  · by_cases hr : S root
    · simp only [indicator, if_neg hi, if_pos hr]
      omega
    · simp [indicator, hi, hr]

#print axioms reach_crosses
#print axioms literal_crossing
#print axioms conditional_literal_cut
#print axioms compulsory_outside_cut
#print axioms rooted_incoming_cut
end Coeff2.Charlieplex.LiteralAttachmentCut
