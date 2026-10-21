import Coeff2.CharliePascalTransfer

/-!
# Exact degeneration sets

There are two distinct constructions here. Fixed candidate traces are removed
by occupation hits; actual successful literal continuations are restricted by
choosing their first symbol. Neither construction identifies no-repeat with
full coverage, or treats a moving endpoint as a fixed candidate universe.
-/

namespace Coeff2.Charlieplex

section Footprints
variable {Address Choice : Type*} [DecidableEq Address] [DecidableEq Choice]

/-- Candidates whose footprint touches an occupied address. -/
def footprintHits (candidates : Finset Choice) (footprint : Choice → Finset Address)
    (occupied : Finset Address) : Finset Choice :=
  candidates.filter fun choice => (footprint choice ∩ occupied).Nonempty

omit [DecidableEq Choice] in
theorem mem_footprintHits (candidates : Finset Choice)
    (footprint : Choice → Finset Address) (occupied : Finset Address) (choice : Choice) :
    choice ∈ footprintHits candidates footprint occupied ↔
      choice ∈ candidates ∧ ∃ address ∈ footprint choice, address ∈ occupied := by
  simp [footprintHits, Finset.Nonempty, Finset.mem_inter]

/-- Two obstruction sources combine by set union, not addition of counts. -/
theorem footprintHits_union (candidates : Finset Choice)
    (footprint : Choice → Finset Address) (old added : Finset Address) :
    footprintHits candidates footprint (old ∪ added) =
      footprintHits candidates footprint old ∪ footprintHits candidates footprint added := by
  ext choice
  simp only [mem_footprintHits, Finset.mem_union]
  aesop

omit [DecidableEq Choice] in
theorem footprintHits_mono (candidates : Finset Choice)
    (footprint : Choice → Finset Address) {old larger : Finset Address}
    (h : old ⊆ larger) :
    footprintHits candidates footprint old ⊆ footprintHits candidates footprint larger := by
  intro choice hc
  obtain ⟨hc, address, ha, hu⟩ := (mem_footprintHits ..).mp hc
  exact (mem_footprintHits ..).mpr ⟨hc, address, ha, h hu⟩

/-- The exact correction is the overlap of the killed-candidate sets. -/
theorem footprintHits_card_union (candidates : Finset Choice)
    (footprint : Choice → Finset Address) (old added : Finset Address) :
    (footprintHits candidates footprint (old ∪ added)).card +
        (footprintHits candidates footprint old ∩ footprintHits candidates footprint added).card =
      (footprintHits candidates footprint old).card +
        (footprintHits candidates footprint added).card := by
  rw [footprintHits_union]
  exact Finset.card_union_add_card_inter _ _

/-- An intrinsic repeated write is rejected even when the old cache is empty. -/
theorem occupationWriteDefect_zero_iff (occupied : Finset Address) (writes : List Address) :
    occupationWriteDefect occupied writes = 0 ↔
      writes.Nodup ∧ Disjoint writes.toFinset occupied := by
  induction writes generalizing occupied with
  | nil => simp [occupationWriteDefect]
  | cons address rest ih =>
      by_cases hmem : address ∈ occupied
      · simp [occupationWriteDefect, hmem, Finset.disjoint_insert_left]
      · simp [occupationWriteDefect, hmem, ih, Finset.disjoint_insert_left,
          Finset.disjoint_insert_right, and_left_comm, and_comm]

/-- Candidate identities are retained; internal duplicate writes are not hidden
by replacing a trace with its footprint. -/
def occupationSurvivors (candidates : Finset Choice) (writes : Choice → List Address)
    (occupied : Finset Address) : Finset Choice :=
  (candidates.filter fun choice => (writes choice).Nodup) \
    footprintHits candidates (fun choice => (writes choice).toFinset) occupied

theorem mem_occupationSurvivors (candidates : Finset Choice)
    (writes : Choice → List Address) (occupied : Finset Address) (choice : Choice) :
    choice ∈ occupationSurvivors candidates writes occupied ↔
      choice ∈ candidates ∧ occupationWriteDefect occupied (writes choice) = 0 := by
  rw [occupationWriteDefect_zero_iff]
  simp only [occupationSurvivors, footprintHits, Finset.mem_sdiff, Finset.mem_filter,
    Finset.nonempty_iff_ne_empty, Finset.disjoint_iff_inter_eq_empty]
  tauto

/-- Exact incremental deletion, for any finite candidate family and write mask. -/
theorem occupationSurvivors_union (candidates : Finset Choice)
    (writes : Choice → List Address) (old added : Finset Address) :
    occupationSurvivors candidates writes (old ∪ added) =
      occupationSurvivors candidates writes old \
        footprintHits candidates (fun choice => (writes choice).toFinset) added := by
  unfold occupationSurvivors
  rw [footprintHits_union]
  ext choice
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem occupationSurvivors_anti (candidates : Finset Choice)
    (writes : Choice → List Address) {old larger : Finset Address} (h : old ⊆ larger) :
    occupationSurvivors candidates writes larger ⊆ occupationSurvivors candidates writes old := by
  intro choice hc
  simp only [occupationSurvivors, Finset.mem_sdiff] at hc ⊢
  exact ⟨hc.1, fun hhit => hc.2 (footprintHits_mono candidates _ h hhit)⟩

/-- These are newly killed candidates, not the number of addresses written. -/
def newlyBlockedCandidates (candidates : Finset Choice) (writes : Choice → List Address)
    (old added : Finset Address) : Finset Choice :=
  occupationSurvivors candidates writes old ∩
    footprintHits candidates (fun choice => (writes choice).toFinset) added

theorem occupationSurvivors_card_balance (candidates : Finset Choice)
    (writes : Choice → List Address) (old added : Finset Address) :
    (occupationSurvivors candidates writes (old ∪ added)).card +
        (newlyBlockedCandidates candidates writes old added).card =
      (occupationSurvivors candidates writes old).card := by
  rw [occupationSurvivors_union, newlyBlockedCandidates]
  exact Finset.card_sdiff_add_card_inter _ _

/-- Fixed-family diminishing marginal loss: candidates already killed cannot
be killed again. This is not a theorem about changing endpoints or horizons. -/
theorem newlyBlockedCandidates_anti (candidates : Finset Choice)
    (writes : Choice → List Address) {old larger : Finset Address} (h : old ⊆ larger)
    (added : Finset Address) :
    newlyBlockedCandidates candidates writes larger added ⊆
      newlyBlockedCandidates candidates writes old added := by
  intro choice hc
  exact Finset.mem_inter.mpr
    ⟨occupationSurvivors_anti candidates writes h (Finset.mem_inter.mp hc).1,
      (Finset.mem_inter.mp hc).2⟩

theorem newlyBlockedCandidates_card_anti (candidates : Finset Choice)
    (writes : Choice → List Address) {old larger : Finset Address} (h : old ⊆ larger)
    (added : Finset Address) :
    (newlyBlockedCandidates candidates writes larger added).card ≤
      (newlyBlockedCandidates candidates writes old added).card :=
  Finset.card_le_card (newlyBlockedCandidates_anti candidates writes h added)

/-- Sequential traces compose with the entire updated occupation, exactly. -/
theorem occupationWriteDefect_append (occupied : Finset Address)
    (before after : List Address) :
    occupationWriteDefect occupied (before ++ after) =
      occupationWriteDefect occupied before +
        occupationWriteDefect (occupied ∪ before.toFinset) after := by
  induction before generalizing occupied with
  | nil => simp [occupationWriteDefect]
  | cons address rest ih =>
      simp [occupationWriteDefect, ih, Finset.insert_union, Finset.union_insert,
        Nat.add_assoc]

/-! ## Allowing a repeat budget, rather than banning every repeat -/

/-- Internal repeats are paid once independently of the old cache. Each
distinct old-cache hit contributes one more, even for internally repeated traces. -/
theorem occupationWriteDefect_split (occupied : Finset Address) (writes : List Address) :
    occupationWriteDefect occupied writes = occupationWriteDefect ∅ writes +
      (writes.toFinset ∩ occupied).card := by
  have hzero := occupationWriteDefect_add_final_card (∅ : Finset Address) writes
  simp only [Finset.empty_union, Finset.card_empty, Nat.add_zero] at hzero
  have hoccupied := occupationWriteDefect_add_final_card occupied writes
  have hcard := Finset.card_union_add_card_inter occupied writes.toFinset
  rw [Finset.inter_comm occupied writes.toFinset] at hcard
  omega

/-- Exact cost increment; an address already occupied is never charged again
merely because it also occurs in the newly supplied occupation mask. -/
theorem occupationWriteDefect_union (old added : Finset Address) (writes : List Address) :
    occupationWriteDefect (old ∪ added) writes = occupationWriteDefect old writes +
      (writes.toFinset ∩ (added \ old)).card := by
  rw [occupationWriteDefect_split (old ∪ added), occupationWriteDefect_split old]
  have hcard := Finset.card_sdiff_add_card_inter (writes.toFinset ∩ (old ∪ added)) old
  have hdiff : (writes.toFinset ∩ (old ∪ added)) \ old =
      writes.toFinset ∩ (added \ old) := by
    ext address
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  have hinter : (writes.toFinset ∩ (old ∪ added)) ∩ old = writes.toFinset ∩ old := by
    ext address
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hdiff, hinter] at hcard
  omega

/-- This budget counts repeated permutation writes, not characters or waste
windows. It is a component of feasibility, not a replacement for coverage. -/
def occupationBudgetSurvivors (candidates : Finset Choice) (writes : Choice → List Address)
    (occupied : Finset Address) (repeatBudget : ℕ) : Finset Choice :=
  candidates.filter fun choice => occupationWriteDefect occupied (writes choice) ≤ repeatBudget

theorem occupationBudgetSurvivors_zero (candidates : Finset Choice)
    (writes : Choice → List Address) (occupied : Finset Address) :
    occupationBudgetSurvivors candidates writes occupied 0 =
      occupationSurvivors candidates writes occupied := by
  ext choice
  simp [occupationBudgetSurvivors, mem_occupationSurvivors]

omit [DecidableEq Choice] in
/-- An exact set update also exists when repeated writes are permitted: filter
old survivors by their old cost plus the distinct newly occupied hits. -/
theorem occupationBudgetSurvivors_union (candidates : Finset Choice)
    (writes : Choice → List Address) (old added : Finset Address) (repeatBudget : ℕ) :
    occupationBudgetSurvivors candidates writes (old ∪ added) repeatBudget =
      (occupationBudgetSurvivors candidates writes old repeatBudget).filter
        (fun choice => occupationWriteDefect old (writes choice) +
          ((writes choice).toFinset ∩ (added \ old)).card ≤ repeatBudget) := by
  ext choice
  simp only [occupationBudgetSurvivors, Finset.mem_filter, occupationWriteDefect_union]
  constructor
  · rintro ⟨hc, hcost⟩
    exact ⟨⟨hc, by omega⟩, hcost⟩
  · rintro ⟨⟨hc, _⟩, hcost⟩
    exact ⟨hc, hcost⟩

end Footprints

/-! ## Bridge to every literal window, including windows crossing the seam -/

def literalFutureWrites (n : ℕ) (state : LiteralSearchState) : List ℕ → List (List ℕ)
  | [] => []
  | symbol :: rest =>
      (if literalPermTest n (state.boundary ++ [symbol])
        then [state.boundary ++ [symbol]] else []) ++
      literalFutureWrites n (literalStateStep n state symbol) rest

theorem literalPermutationWindows_append_future (n : ℕ) (hn : 1 ≤ n)
    (text suffix : List ℕ) :
    literalPermutationWindows n (text ++ suffix) =
      literalPermutationWindows n text ++ literalFutureWrites n (literalStateOf n text) suffix := by
  induction suffix generalizing text with
  | nil => simp [literalFutureWrites]
  | cons symbol rest ih =>
      rw [show text ++ symbol :: rest = (text ++ [symbol]) ++ rest by simp]
      rw [ih, literalPermutationWindows_append_singleton n hn]
      rw [literalFutureWrites, literalStateStep_correct n hn]
      simp only [literalStateOf, nextLiteralWindow, List.append_assoc]

theorem literal_append_nodup_iff_writeDefect (n : ℕ) (hn : 1 ≤ n)
    (text suffix : List ℕ) :
    (literalPermutationWindows n (text ++ suffix)).Nodup ↔
      (literalPermutationWindows n text).Nodup ∧
        occupationWriteDefect (literalStateOf n text).occupied
          (literalFutureWrites n (literalStateOf n text) suffix) = 0 := by
  rw [literalPermutationWindows_append_future n hn, List.nodup_append,
    occupationWriteDefect_zero_iff]
  simp only [literalStateOf, Finset.disjoint_left, List.mem_toFinset]
  aesop

/-- Exact accounting for literal repeats, even if the prefix already contains
repeats. This does not charge non-permutation windows as repeated writes. -/
theorem literalRepeatDefect_append (n : ℕ) (hn : 1 ≤ n) (text suffix : List ℕ) :
    literalRepeatDefect n (text ++ suffix) = literalRepeatDefect n text +
      occupationWriteDefect (literalStateOf n text).occupied
        (literalFutureWrites n (literalStateOf n text) suffix) := by
  have h := occupationWriteDefect_append (∅ : Finset (List ℕ))
    (literalPermutationWindows n text) (literalFutureWrites n (literalStateOf n text) suffix)
  have hempty (xs : List (List ℕ)) : occupationWriteDefect ∅ xs =
      xs.length - xs.toFinset.card := by simp [occupationWriteDefect_eq_footprint]
  rw [hempty, hempty, Finset.empty_union] at h
  simpa only [literalRepeatDefect, literalPermutationWindows_append_future n hn,
    literalStateOf] using h

/-- The survivor sets really describe every alphabet-valid literal suffix of
this character length, not merely the corpus or an abstract graph model. -/
theorem literalNoRepeatSuffixes_eq_survivors (n horizon : ℕ) (hn : 1 ≤ n)
    (text : List ℕ) (htext : (literalPermutationWindows n text).Nodup) :
    literalNoRepeatSuffixes n horizon text =
      occupationSurvivors (literalSuffixes n horizon)
        (literalFutureWrites n (literalStateOf n text)) (literalStateOf n text).occupied := by
  ext suffix
  simp only [literalNoRepeatSuffixes, Finset.mem_filter, mem_occupationSurvivors,
    literal_append_nodup_iff_writeDefect n hn, htext, true_and]

/-! ## Full completion sets: embed the child in the parent's coordinates -/

def literalChosenCompletions (n budget horizon : ℕ) (state : LiteralSearchState)
    (symbol : ℕ) : Finset (List ℕ) :=
  (literalSuccessfulSuffixes n budget horizon (literalStateStep n state symbol)).image
    (List.cons symbol)

/-- Choosing a symbol selects exactly one slice of the parent's successful
strings. The prepended symbol is essential when comparing sets. -/
theorem literalChosenCompletions_eq_filter (n budget horizon : ℕ)
    (state : LiteralSearchState) (symbol : ℕ) (hsymbol : symbol ∈ Finset.Icc 1 n) :
    literalChosenCompletions n budget horizon state symbol =
      (literalSuccessfulSuffixes n budget (horizon + 1) state).filter
        (fun suffix => suffix.head? = some symbol) := by
  ext suffix
  cases suffix with
  | nil => simp [literalChosenCompletions, literalSuccessfulSuffixes, literalSuffixes]
  | cons first rest =>
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hsymbol
      by_cases heq : first = symbol
      · subst first
        simp [literalChosenCompletions, literalSuccessfulSuffixes, literalSuffixes,
          literalStateRun, List.cons.injEq, hlo, hhi, and_assoc, and_left_comm, and_comm]
      · simp [literalChosenCompletions, literalSuccessfulSuffixes, literalSuffixes,
          List.cons.injEq, heq, Ne.symm heq]

def literalDiscardedCompletions (n budget horizon : ℕ) (state : LiteralSearchState)
    (symbol : ℕ) : Finset (List ℕ) :=
  literalSuccessfulSuffixes n budget (horizon + 1) state \
    literalChosenCompletions n budget horizon state symbol

/-- The old Bellman inequality sharpens to an exact set-loss balance. Full
coverage and the literal character budget are already in the acceptance gate. -/
theorem literalBellmanCount_exact_loss (n budget horizon : ℕ)
    (state : LiteralSearchState) (symbol : ℕ) (hsymbol : symbol ∈ Finset.Icc 1 n) :
    (literalDiscardedCompletions n budget horizon state symbol).card +
      literalBellmanCount n budget horizon (literalStateStep n state symbol) =
        literalBellmanCount n budget (horizon + 1) state := by
  have hsub : literalChosenCompletions n budget horizon state symbol ⊆
      literalSuccessfulSuffixes n budget (horizon + 1) state := by
    rw [literalChosenCompletions_eq_filter n budget horizon state symbol hsymbol]
    exact Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  simpa only [literalDiscardedCompletions, literalChosenCompletions,
    Finset.card_image_of_injective _ (List.cons_injective (a := symbol)),
    literalBellmanCount_eq_card] using hcard

end Coeff2.Charlieplex
