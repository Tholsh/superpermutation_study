import Coeff2.CharlieRecursiveClockLift

/-!
# Literal attachment rewrites and the all-order savings obligation

Paths retain actual boundary strings and literal arc words. Removing a closed
optional excursion preserves the endpoints; spelling and coverage are not
inferred from a scalar cost. No economical normalizer or all-n improvement
is assumed to exist here.
-/
namespace Coeff2.Charlieplex.AttachmentReduction
open PacketAssembly
variable {α : Type*}

structure Arc (α : Type*) where
  entry : List α
  payload : List α
  exit : List α
  returns : exit.IsSuffix (entry ++ payload)

def Arc.word (a : Arc α) : List α := a.entry ++ a.payload

inductive Path : List α → List α → List (Arc α) → Prop
  | nil (f : List α) : Path f f []
  | cons (a : Arc α) {f : List α} {as : List (Arc α)}
      (rest : Path a.exit f as) : Path a.entry f (a :: as)

def payload (as : List (Arc α)) : List α := as.flatMap Arc.payload

theorem path_append {f g h : List α} {as bs : List (Arc α)}
    (ha : Path f g as) (hb : Path g h bs) : Path f h (as ++ bs) := by
  induction ha with
  | nil => simpa using hb
  | cons a rest ih => exact Path.cons a (ih hb)

theorem erase_closed {f g h : List α} {as loop bs : List (Arc α)}
    (ha : Path f g as) (_hl : Path g g loop) (hb : Path g h bs) :
    Path f h (as ++ bs) := path_append ha hb

theorem payload_append (as bs : List (Arc α)) :
    payload (as ++ bs) = payload as ++ payload bs := by
  simp [payload]

private theorem suffix_extend {f w v : List α} (h : f.IsSuffix w) :
    (f ++ v).IsSuffix (w ++ v) := by
  obtain ⟨before, hb⟩ := h
  refine ⟨before, ?_⟩
  rw [← hb, List.append_assoc]

theorem path_suffix {f g : List α} {as : List (Arc α)} (hp : Path f g as) :
    g.IsSuffix (f ++ payload as) := by
  induction hp with
  | nil f => simp [payload]
  | @cons a g as rest ih =>
    have h := ih.trans (suffix_extend (v := payload as) a.returns)
    simpa [payload, List.append_assoc] using h

theorem path_contains {f g : List α} {as : List (Arc α)} (hp : Path f g as) :
    ∀ a ∈ as, a.word.IsInfix (f ++ payload as) := by
  induction hp with
  | nil f => simp
  | @cons a g as rest ih =>
    intro b hb
    rcases List.mem_cons.mp hb with hba | hb
    · subst b
      simpa [Arc.word, payload, List.append_assoc] using
        (List.infix_append_left : (a.entry ++ a.payload).IsInfix
          ((a.entry ++ a.payload) ++ payload as))
    · have h := (ih b hb).trans
        (suffix_extend (v := payload as) a.returns).isInfix
      simpa [payload, List.append_assoc] using h

/-- The actual shortened word contains every promised permutation provided
its witness is in a retained arc. Optional means not needed by this coverage
certificate, not that the erased text contains no clean permutation windows. -/
theorem erase_closed_covers {f g h : List α} {as loop bs : List (Arc α)}
    (ha : Path f g as) (hl : Path g g loop) (hb : Path g h bs)
    (alphabet : List α)
    (hc : ∀ p : List α, p.Perm alphabet →
      ∃ a ∈ as ++ bs, p.IsInfix a.word) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix (f ++ payload (as ++ bs)) := by
  intro p hp
  obtain ⟨a, hm, hi⟩ := hc p hp
  exact hi.trans (path_contains (erase_closed ha hl hb) a hm)

theorem erase_closed_length (f : List α) (as loop bs : List (Arc α)) :
    (f ++ payload (as ++ bs)).length + (payload loop).length =
      (f ++ payload (as ++ loop ++ bs)).length := by
  simp only [payload_append, List.length_append]
  omega

/-- Replacement is sound because the concrete endpoint frames match. -/
theorem replace_path {f g h j : List α} {as old replacement bs : List (Arc α)}
    (ha : Path f g as) (_ho : Path g h old)
    (hn : Path g h replacement) (hb : Path h j bs) :
    Path f j (as ++ replacement ++ bs) :=
  path_append (path_append ha hn) hb

theorem replacement_saving (f : List α) (as old replacement bs : List (Arc α))
    (d : ℕ) (hd : (payload replacement).length + d = (payload old).length) :
    (f ++ payload (as ++ replacement ++ bs)).length + d =
      (f ++ payload (as ++ old ++ bs)).length := by
  simp only [payload_append, List.length_append]
  omega

section Budget

/-- Use r=n-3 so every subtraction below is integer arithmetic, not truncated
natural subtraction. This is the Egan expression, not a minimum claim. -/
def egan (r : ℕ) : ℤ :=
  ((r : ℤ)+3)^2 * ((r+1).factorial : ℤ) + (r.factorial : ℤ) + r

def priced (r : ℕ) (R Q cut : ℤ) : ℤ :=
  ((r : ℤ)+3)^2 * ((r+1).factorial : ℤ) + r + R + Q - cut

theorem exact_savings (r : ℕ) (R Q cut : ℤ) :
    egan r - priced r R Q cut = (r.factorial : ℤ) - R - Q + cut := by
  unfold egan priced
  ring

theorem beats_egan_iff (r : ℕ) (R Q cut : ℤ) :
    priced r R Q cut < egan r ↔ R + Q - cut < (r.factorial : ℤ) := by
  unfold priced egan
  omega

theorem saves_at_least_iff (r : ℕ) (R Q cut saving : ℤ) :
    priced r R Q cut + saving ≤ egan r ↔
      R + Q - cut + saving ≤ (r.factorial : ℤ) := by
  unfold priced egan
  omega

/-- In the inherited 144-backward-parent family, the catalog recurrence and
two-repeat packet cost give 5R=2r!. This removes R from the attachment target.
It does not supply the required cheap connectors. -/
theorem two_fifths_budget (r : ℕ) (R Q cut : ℤ)
    (hr : 5*R = 2*(r.factorial : ℤ)) :
    priced r R Q cut < egan r ↔ 5*(Q-cut) < 3*(r.factorial : ℤ) := by
  rw [beats_egan_iff]
  omega

/-- Reducing the CLOSED connector bill by d is not automatically a d-symbol
gain in the OPEN word: the removable cut may change too. -/
theorem open_gain (r : ℕ) (R Q cut Q' cut' d : ℤ) (hq : Q' + d = Q) :
    priced r R Q cut - priced r R Q' cut' = d + cut' - cut := by
  unfold priced
  omega

theorem nine_budget : egan 6 - priced 6 288 427 7 = 12 := by
  rw [exact_savings]
  norm_num [Nat.factorial]

theorem ten_budget : egan 7 - priced 7 2016 3368 10 = -334 := by
  rw [exact_savings]
  norm_num [Nat.factorial]

end Budget

#print axioms erase_closed_covers
#print axioms erase_closed_length
#print axioms replace_path
#print axioms replacement_saving
#print axioms exact_savings
#print axioms beats_egan_iff
#print axioms two_fifths_budget
#print axioms open_gain
end Coeff2.Charlieplex.AttachmentReduction
