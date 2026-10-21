import Coeff2.CharliePacketAssembly

/-!
# Literal boundary-spine expansion

An emitted component returns to the same literal boundary frame. It can
therefore be inserted without changing any subsequent spine decision.
The word-level coverage and cost conclusions below are unconditional once
the explicit run is supplied. No existence of an economical spine is assumed
as a theorem, and no global optimality of the native heuristics is claimed.
-/
namespace Coeff2.Charlieplex.BoundarySpine
variable {α : Type*}

/-- A literal execution: emit a spine symbol, or insert a word which starts
and ends at the current frame. `cost` is the total inserted payload length. -/
inductive Run : List α → List α → List α → List (List α) → ℕ → Prop
  | start (frame : List α) : Run frame frame frame [] 0
  | letter {spine word tail : List α} {a : α} {pieces : List (List α)} {cost : ℕ}
      (prev : Run spine word (a :: tail) pieces cost) (b : α) :
      Run (spine ++ [b]) (word ++ [b]) (tail ++ [b]) pieces cost
  | loop {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
      (prev : Run spine word frame pieces cost) (body : List α)
      (returns : frame.IsSuffix (frame ++ body)) :
      Run spine (word ++ body) frame (pieces ++ [frame ++ body]) (cost + body.length)

private theorem suffix_letter {frame word : List α} {a b : α}
    (h : (a :: frame).IsSuffix word) :
    (frame ++ [b]).IsSuffix (word ++ [b]) := by
  obtain ⟨before, hb⟩ := h
  refine ⟨before ++ [a], ?_⟩
  rw [← hb]
  simp [List.append_assoc]

/-- Both the unexpanded spine and the actual output retain the same frame. -/
theorem run_suffix {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
    (h : Run spine word frame pieces cost) :
    frame.IsSuffix spine ∧ frame.IsSuffix word := by
  induction h with
  | start f => exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | letter prev b ih => exact ⟨suffix_letter ih.1, suffix_letter ih.2⟩
  | @loop s w f ps c prev body hr ih =>
    obtain ⟨before, hb⟩ := ih.2
    obtain ⟨inside, hi⟩ := hr
    refine ⟨ih.1, before ++ inside, ?_⟩
    rw [List.append_assoc, hi, ← List.append_assoc, hb]

/-- No factorial-size word has to be rebuilt in order to price a spine. -/
theorem run_length {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
    (h : Run spine word frame pieces cost) : word.length = spine.length + cost := by
  induction h with
  | start f => simp
  | letter prev b ih => simp only [List.length_append, List.length_singleton]; omega
  | loop prev body hr ih => simp only [List.length_append]; omega

/-- Every inserted word survives as a contiguous factor, not just as a set
of abstract occupations. -/
theorem run_contains {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
    (h : Run spine word frame pieces cost) : ∀ p ∈ pieces, p.IsInfix word := by
  induction h with
  | start f => simp
  | letter prev b ih =>
    intro p hp
    exact (ih p hp).trans List.infix_append_left
  | @loop s w f ps c prev body hr ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact (ih p hp).trans List.infix_append_left
    · have he : p = f ++ body := List.mem_singleton.mp hp
      subst p
      obtain ⟨before, hb⟩ := (run_suffix prev).2
      refine ⟨before, [], ?_⟩
      simpa only [List.append_nil, ← List.append_assoc] using congrArg (fun x => x ++ body) hb

/-- Direct superpermutation application: actual permutation lists are factors
of the expanded word. Repeated permutation windows are permitted. -/
theorem run_covers {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
    (h : Run spine word frame pieces cost) (alphabet : List α)
    (hc : ∀ p : List α, p.Perm alphabet → ∃ piece ∈ pieces, p.IsInfix piece) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix word := by
  intro p hp
  obtain ⟨piece, hm, hi⟩ := hc p hp
  exact hi.trans (run_contains h piece hm)

/-- Expanded Egan expression in terms of the boundary radix r = n-3. -/
theorem factorial_base (r : ℕ) :
    (r+3)^2 * (r+1).factorial + r.factorial + r =
      (r+3).factorial + (r+2).factorial + (r+1).factorial + r.factorial + r := by
  have h₂ : (r+2).factorial = (r+2) * (r+1).factorial := Nat.factorial_succ (r+1)
  have h₃ : (r+3).factorial = (r+3) * (r+2).factorial := Nat.factorial_succ (r+2)
  rw [h₃, h₂]
  ring

/-- Gain is the reduction in component count minus the packet repetition
cost. W counts boundary frames which are not a first component encounter.
This identity is conditional on the explicit occupation and first-hit counts;
it does NOT provide a short spine or choose a packet tiling. -/
theorem gain_minus_delay {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
    (h : Run spine word frame pieces cost) (r B C G W : ℕ)
    (hc : cost = (r+3)^2 * (r+1).factorial + 2*B)
    (hg : G + C + 2*B = r.factorial)
    (hw : spine.length + 1 = r + C + W) :
    word.length + G + 1 =
      (r+3).factorial + (r+2).factorial + (r+1).factorial + r.factorial + r + W := by
  have hl := run_length h
  have hf := factorial_base r
  omega

/-- Once an actual run is supplied, beating Egan-minus-one has an exact
integer condition: the local gain must exceed the spine's wasted visits. -/
theorem beats_minus_one_iff (L E G W : ℕ) (h : L + G + 1 = E + W) :
    L + 2 ≤ E ↔ W + 1 ≤ G := by omega

section Visits
variable {β : Type*} [DecidableEq β]

def seen : List (Option β) → Finset β
  | [] => ∅
  | none :: rest => seen rest
  | some c :: rest => insert c (seen rest)

theorem seen_card_le (visits : List (Option β)) : (seen visits).card ≤ visits.length := by
  induction visits with
  | nil => simp [seen]
  | cons x rest ih =>
    cases x with
    | none => simp only [seen, List.length_cons]; omega
    | some c =>
      by_cases hc : c ∈ seen rest
      · simp [seen, hc]; omega
      · simp [seen, hc]; omega

/-- Blank frames plus repeated component encounters; exact, not statistical. -/
def delay (visits : List (Option β)) : ℕ := visits.length - (seen visits).card

theorem visits_accounted (visits : List (Option β)) :
    (seen visits).card + delay visits = visits.length := by
  have := seen_card_le visits
  unfold delay
  omega

/-- Apply the literal port-owner map to EVERY length-k spine window. -/
def boundaryVisits (owner : List α → Option β) (k : ℕ) (spine : List α) : List (Option β) :=
  (List.range (spine.length + 1 - k)).map (fun i => owner ((spine.drop i).take k))

omit [DecidableEq β] in
theorem boundary_visits_length (owner : List α → Option β) (k : ℕ) (spine : List α)
    (hk : k ≤ spine.length + 1) :
    (boundaryVisits owner k spine).length + k = spine.length + 1 := by
  simp only [boundaryVisits, List.length_map, List.length_range]
  omega

/-- The delay in the length theorem can be COMPUTED from literal boundary
windows. The remaining hypotheses are real coverage and component-cost
identities, not an asserted cheap-completion oracle. -/
theorem gain_minus_literal_delay [Fintype β]
    {spine word frame : List α} {pieces : List (List α)} {cost : ℕ}
    (h : Run spine word frame pieces cost) (owner : List α → Option β) (r B G : ℕ)
    (hc : cost = (r+3)^2 * (r+1).factorial + 2*B)
    (hg : G + Fintype.card β + 2*B = r.factorial)
    (hr : r ≤ spine.length + 1)
    (hcover : seen (boundaryVisits owner r spine) = Finset.univ) :
    word.length + G + 1 =
      (r+3).factorial + (r+2).factorial + (r+1).factorial + r.factorial + r +
        delay (boundaryVisits owner r spine) := by
  apply gain_minus_delay h r B (Fintype.card β) G (delay (boundaryVisits owner r spine)) hc hg
  have hcount := visits_accounted (boundaryVisits owner r spine)
  rw [hcover, Finset.card_univ] at hcount
  have hlen := boundary_visits_length owner r spine hr
  omega
end Visits

example : 46188 + 42 + 1 = 46205 + 26 := by decide
example : 408969 + 288 + 1 = 408966 + 292 := by decide

#print axioms run_suffix
#print axioms run_length
#print axioms run_contains
#print axioms run_covers
#print axioms factorial_base
#print axioms gain_minus_delay
#print axioms beats_minus_one_iff
#print axioms gain_minus_literal_delay
end Coeff2.Charlieplex.BoundarySpine
