/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.CharlieCayleyFourier
import Mathlib.Tactic

/-!
# Exact occupation for Cayley words

Endpoint motion alone is a Cayley walk, but no-repeat legality is stateful.
This file gives the exact quotient that remains valid: translate the initial
endpoint to the identity while retaining every running product.  A word is
legal precisely when that rooted list has no duplicate.

This is not a fixed-memory approximation.  The complete prefix-product list
is the occupation ledger.
-/

namespace Coeff2

namespace Charlieplex

section OccupationCayley

variable {G : Type*} [Group G]

/-- All states visited by a right Cayley word, including the initial state. -/
def cayleyOccupationStates (start : G) (word : List G) : List G :=
  word.scanl (· * ·) start

/-- The final state after reading a Cayley word. -/
def cayleyOccupationEndpoint (start : G) (word : List G) : G :=
  word.foldl (· * ·) start

@[simp]
theorem cayleyOccupationStates_nil (start : G) :
    cayleyOccupationStates start [] = [start] := by
  simp [cayleyOccupationStates]

@[simp]
theorem cayleyOccupationEndpoint_nil (start : G) :
    cayleyOccupationEndpoint start [] = start := by
  simp [cayleyOccupationEndpoint]

/-- Left translation transports the entire occupation ledger. -/
theorem cayleyOccupationStates_mul_left (gauge start : G)
    (word : List G) :
    cayleyOccupationStates (gauge * start) word =
      (cayleyOccupationStates start word).map (fun state => gauge * state) := by
  induction word generalizing start with
  | nil => simp
  | cons generator rest ih =>
      simp only [cayleyOccupationStates, List.scanl_cons, List.map_cons,
        List.cons.injEq, true_and]
      simpa only [cayleyOccupationStates, mul_assoc] using
        ih (start * generator)

/-- The endpoint is transported by the same left translation. -/
theorem cayleyOccupationEndpoint_mul_left (gauge start : G)
    (word : List G) :
    cayleyOccupationEndpoint (gauge * start) word =
      gauge * cayleyOccupationEndpoint start word := by
  induction word generalizing start with
  | nil => simp
  | cons generator rest ih =>
      change cayleyOccupationEndpoint ((gauge * start) * generator) rest =
        gauge * cayleyOccupationEndpoint (start * generator) rest
      simpa only [mul_assoc] using ih (start * generator)

/-- Every occupation ledger is a left translate of the ledger rooted at the
identity. -/
theorem cayleyOccupationStates_eq_rooted (start : G) (word : List G) :
    cayleyOccupationStates start word =
      (cayleyOccupationStates 1 word).map (fun state => start * state) := by
  simpa using cayleyOccupationStates_mul_left start 1 word

/-- The corresponding endpoint normalization. -/
theorem cayleyOccupationEndpoint_eq_rooted (start : G) (word : List G) :
    cayleyOccupationEndpoint start word =
      start * cayleyOccupationEndpoint 1 word := by
  simpa using cayleyOccupationEndpoint_mul_left start 1 word

/-- Exact no-repeat legality of a Cayley generator word. -/
def CayleyOccupationLegal (start : G) (word : List G) : Prop :=
  (cayleyOccupationStates start word).Nodup

/-- Occupation legality is independent of the chosen starting permutation. -/
theorem cayleyOccupationLegal_iff_rooted (start : G) (word : List G) :
    CayleyOccupationLegal start word ↔ CayleyOccupationLegal 1 word := by
  rw [CayleyOccupationLegal, CayleyOccupationLegal,
    cayleyOccupationStates_eq_rooted]
  apply List.nodup_map_iff
  intro left right heq
  exact mul_left_cancel heq

/-- At the root, the exact occupation ledger is the list of running group
products. -/
theorem cayleyOccupationLegal_one_iff_partialProds (word : List G) :
    CayleyOccupationLegal 1 word ↔ word.partialProds.Nodup := by
  rfl

/-- Appending one generator adds exactly the new endpoint to the ledger. -/
theorem cayleyOccupationStates_append_singleton (start : G)
    (word : List G) (generator : G) :
    cayleyOccupationStates start (word ++ [generator]) =
      cayleyOccupationStates start word ++
        [cayleyOccupationEndpoint start word * generator] := by
  simp [cayleyOccupationStates, cayleyOccupationEndpoint,
    List.scanl_append]

/-- A right Cayley endpoint is the start multiplied by the product of its
generator word. -/
theorem cayleyOccupationEndpoint_eq_mul_prod (start : G) (word : List G) :
    cayleyOccupationEndpoint start word = start * word.prod := by
  induction word generalizing start with
  | nil => simp
  | cons generator rest ih =>
      change cayleyOccupationEndpoint (start * generator) rest =
        start * (generator :: rest).prod
      rw [ih]
      simp only [List.prod_cons, mul_assoc]

/-- Returning across a suffix is exactly the assertion that the suffix,
followed by the proposed generator, is an identity word. -/
theorem cayleyCollision_across_suffix_iff (start : G)
    (initial suffix : List G) (generator : G) :
    cayleyOccupationEndpoint start (initial ++ suffix) * generator =
        cayleyOccupationEndpoint start initial ↔
      suffix.prod * generator = 1 := by
  rw [cayleyOccupationEndpoint_eq_mul_prod,
    cayleyOccupationEndpoint_eq_mul_prod, List.prod_append]
  constructor
  · intro hcollision
    have hnormalized :
        (start * initial.prod) * (suffix.prod * generator) =
          (start * initial.prod) * 1 := by
      simpa only [mul_assoc, mul_one] using hcollision
    exact mul_left_cancel hnormalized
  · intro hreturn
    simp only [mul_assoc, hreturn, mul_one]

/-- Exact collision criterion in word language: the proposed action is
illegal precisely when it closes some suffix of the existing word to the
identity.  This includes the empty suffix, which detects an identity action. -/
theorem next_mem_occupation_iff_exists_suffix_return
    (start : G) (word : List G) (generator : G) :
    cayleyOccupationEndpoint start word * generator ∈
        cayleyOccupationStates start word ↔
      ∃ i ≤ word.length, (word.drop i).prod * generator = 1 := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hstate⟩
    have hi' : i ≤ word.length := by
      simpa [cayleyOccupationStates] using hi
    refine ⟨i, hi', ?_⟩
    apply (cayleyCollision_across_suffix_iff start
      (word.take i) (word.drop i) generator).mp
    rw [List.take_append_drop]
    simpa [cayleyOccupationStates, cayleyOccupationEndpoint] using hstate.symm
  · rintro ⟨i, hi, hreturn⟩
    have hilength : i < (cayleyOccupationStates start word).length := by
      simpa [cayleyOccupationStates] using hi
    refine ⟨i, hilength, ?_⟩
    have hcollision :=
      (cayleyCollision_across_suffix_iff start
        (word.take i) (word.drop i) generator).mpr hreturn
    rw [List.take_append_drop] at hcollision
    simpa [cayleyOccupationStates, cayleyOccupationEndpoint] using
      hcollision.symm

/-- Exact one-step cache law: assuming the old path is legal, an appended
generator is legal exactly when its endpoint is absent from the accumulated
ledger. -/
theorem cayleyOccupationLegal_append_iff
    {start : G} {word : List G} (generator : G)
    (hlegal : CayleyOccupationLegal start word) :
    CayleyOccupationLegal start (word ++ [generator]) ↔
      cayleyOccupationEndpoint start word * generator ∉
        cayleyOccupationStates start word := by
  change (cayleyOccupationStates start word).Nodup at hlegal
  rw [CayleyOccupationLegal, cayleyOccupationStates_append_singleton]
  simp only [List.nodup_append, hlegal, List.nodup_singleton,
    List.mem_singleton, true_and]
  constructor
  · intro hall hmem
    exact hall _ hmem _ rfl rfl
  · intro hnotmem left hleft right hright heq
    apply hnotmem
    simpa [heq, hright] using hleft

/-- Inductive closed-factor grammar for legal Cayley words.  Appending one
action is legal exactly when the old word was legal and no suffix, followed
by the new action, multiplies to the identity. -/
theorem cayleyOccupationLegal_append_iff_no_suffix_return
    (start : G) (word : List G) (generator : G) :
    CayleyOccupationLegal start (word ++ [generator]) ↔
      CayleyOccupationLegal start word ∧
        ∀ i ≤ word.length, (word.drop i).prod * generator ≠ 1 := by
  constructor
  · intro happend
    have hstates :
        (cayleyOccupationStates start word ++
          [cayleyOccupationEndpoint start word * generator]).Nodup := by
      simpa [CayleyOccupationLegal,
        cayleyOccupationStates_append_singleton] using happend
    have hword : CayleyOccupationLegal start word := by
      exact (List.nodup_append.mp hstates).1
    refine ⟨hword, ?_⟩
    have hfresh :=
      (cayleyOccupationLegal_append_iff generator hword).mp happend
    intro i hi hreturn
    apply hfresh
    exact (next_mem_occupation_iff_exists_suffix_return
      start word generator).mpr ⟨i, hi, hreturn⟩
  · rintro ⟨hword, hnoReturn⟩
    apply (cayleyOccupationLegal_append_iff generator hword).mpr
    intro hcollision
    obtain ⟨i, hi, hreturn⟩ :=
      (next_mem_occupation_iff_exists_suffix_return
        start word generator).mp hcollision
    exact hnoReturn i hi hreturn

/-- A word is identity-factor-free when every nonempty contiguous interval
has nonidentity product.  The interval starts at `startIndex` and ends just
before `endIndex`. -/
def IdentityFactorFree (word : List G) : Prop :=
  ∀ endIndex ≤ word.length, ∀ startIndex < endIndex,
    ((word.take endIndex).drop startIndex).prod ≠ 1

/-- Identity-factor freedom obeys the same suffix recurrence as occupation
legality. -/
theorem identityFactorFree_append_iff (word : List G) (generator : G) :
    IdentityFactorFree (word ++ [generator]) ↔
      IdentityFactorFree word ∧
        ∀ i ≤ word.length, (word.drop i).prod * generator ≠ 1 := by
  constructor
  · intro hfree
    constructor
    · intro endIndex hend startIndex hstart
      have hfull := hfree endIndex (by simp; omega) startIndex hstart
      simpa [List.take_append_of_le_length hend] using hfull
    · intro startIndex hstart
      have hfull := hfree (word.length + 1) (by simp) startIndex (by omega)
      have htake :
          (word ++ [generator]).take (word.length + 1) =
            word ++ [generator] := by
        simp
      have hdrop :
          (word ++ [generator]).drop startIndex =
            word.drop startIndex ++ [generator] := by
        exact List.drop_append_of_le_length hstart
      simpa [htake, hdrop, List.prod_append] using hfull
  · rintro ⟨hword, hterminal⟩
    intro endIndex hend startIndex hstart
    by_cases holdEnd : endIndex ≤ word.length
    · have hold := hword endIndex holdEnd startIndex hstart
      simpa [List.take_append_of_le_length holdEnd] using hold
    · have hendEq : endIndex = word.length + 1 := by
        simp only [List.length_append, List.length_singleton] at hend
        omega
      subst endIndex
      have hstartLe : startIndex ≤ word.length := by omega
      have hterminal' := hterminal startIndex hstartLe
      have htake :
          (word ++ [generator]).take (word.length + 1) =
            word ++ [generator] := by
        simp
      have hdrop :
          (word ++ [generator]).drop startIndex =
            word.drop startIndex ++ [generator] := by
        exact List.drop_append_of_le_length hstartLe
      simpa [htake, hdrop, List.prod_append] using hterminal'

/-- Exact global grammar: a right Cayley word visits no endpoint twice if
and only if it contains no nonempty contiguous identity factor. -/
theorem cayleyOccupationLegal_iff_identityFactorFree
    (start : G) (word : List G) :
    CayleyOccupationLegal start word ↔ IdentityFactorFree word := by
  induction word using List.reverseRecOn with
  | nil =>
      simp [CayleyOccupationLegal, IdentityFactorFree,
        cayleyOccupationStates]
  | append_singleton word generator ih =>
      rw [cayleyOccupationLegal_append_iff_no_suffix_return,
        identityFactorFree_append_iff, ih]

variable [DecidableEq G]

/-- The exact Bellman action set after a generator word. -/
def legalCayleyActions (generators : Finset G) (start : G)
    (word : List G) : Finset G :=
  generators.filter fun generator =>
    cayleyOccupationEndpoint start word * generator ∉
      cayleyOccupationStates start word

theorem mem_legalCayleyActions_iff (generators : Finset G)
    (start : G) (word : List G) (generator : G) :
    generator ∈ legalCayleyActions generators start word ↔
      generator ∈ generators ∧
        cayleyOccupationEndpoint start word * generator ∉
          cayleyOccupationStates start word := by
  simp [legalCayleyActions]

/-- When the existing word is legal, filtering by the occupation ledger is
equivalent to filtering by legality of the extended word. -/
theorem mem_legalCayleyActions_iff_legal_append
    (generators : Finset G) (start : G) (word : List G)
    (generator : G) (hlegal : CayleyOccupationLegal start word) :
    generator ∈ legalCayleyActions generators start word ↔
      generator ∈ generators ∧
        CayleyOccupationLegal start (word ++ [generator]) := by
  rw [mem_legalCayleyActions_iff,
    cayleyOccupationLegal_append_iff generator hlegal]

/-- The exact number of choices can only fall when an additional occupied
address is supplied to a fixed endpoint and generator family. -/
theorem legalActions_anti_occupation (generators : Finset G)
    (endpoint : G) {oldOccupation newOccupation : Finset G}
    (hsubset : oldOccupation ⊆ newOccupation) :
    (generators.filter fun generator =>
        endpoint * generator ∉ newOccupation).card ≤
      (generators.filter fun generator =>
        endpoint * generator ∉ oldOccupation).card := by
  apply Finset.card_le_card
  intro generator hgenerator
  simp only [Finset.mem_filter] at hgenerator ⊢
  exact ⟨hgenerator.1, fun hmem => hgenerator.2 (hsubset hmem)⟩

/-! ## Moving-coordinate occupation quotient -/

/-- Translate every occupied address into coordinates rooted at the current
endpoint. -/
def relativeOccupation (endpoint : G) (occupied : Finset G) : Finset G :=
  occupied.image fun oldAddress => endpoint⁻¹ * oldAddress

/-- Exact relative-cache update after taking generator `g`. -/
def advanceRelativeOccupation (g : G) (relative : Finset G) : Finset G :=
  insert 1 (relative.image fun address => g⁻¹ * address)

/-- The exact moving-coordinate cache generated by a Cayley word. -/
def relativeWordOccupation (start : G) (word : List G) : Finset G :=
  relativeOccupation (cayleyOccupationEndpoint start word)
    (cayleyOccupationStates start word).toFinset

/-- A proposed endpoint is fresh exactly when its generator address is absent
from the relative occupation cache. -/
theorem next_fresh_iff_not_mem_relativeOccupation (endpoint g : G)
    (occupied : Finset G) :
    endpoint * g ∉ occupied ↔ g ∉ relativeOccupation endpoint occupied := by
  have hmem :
      g ∈ relativeOccupation endpoint occupied ↔ endpoint * g ∈ occupied := by
    constructor
    · intro hrelative
      simp only [relativeOccupation, Finset.mem_image] at hrelative
      obtain ⟨oldAddress, hold, hcoordinate⟩ := hrelative
      have : endpoint * g = oldAddress := by
        calc
          endpoint * g = endpoint * (endpoint⁻¹ * oldAddress) := by
            rw [hcoordinate]
          _ = oldAddress := by simp
      simpa [this] using hold
    · intro hnext
      simp only [relativeOccupation, Finset.mem_image]
      refine ⟨endpoint * g, hnext, ?_⟩
      simp
  exact not_congr hmem.symm

/-- The relative cache contains exactly the actions that would close a
suffix of the word to an identity factor.  Thus occupation is not an
additional mysterious variable: it is the ledger of inverse suffix products. -/
theorem mem_relativeWordOccupation_iff_exists_suffix_return
    (start : G) (word : List G) (generator : G) :
    generator ∈ relativeWordOccupation start word ↔
      ∃ i ≤ word.length, (word.drop i).prod * generator = 1 := by
  have hnot := next_fresh_iff_not_mem_relativeOccupation
    (cayleyOccupationEndpoint start word) generator
    (cayleyOccupationStates start word).toFinset
  have hmem :
      cayleyOccupationEndpoint start word * generator ∈
          (cayleyOccupationStates start word).toFinset ↔
        generator ∈ relativeWordOccupation start word := by
    simpa [relativeWordOccupation] using not_congr hnot
  rw [← hmem]
  simpa using next_mem_occupation_iff_exists_suffix_return
    start word generator

/-- Actions rejected by the exact relative cache. -/
def blockedCayleyActions (generators : Finset G) (start : G)
    (word : List G) : Finset G :=
  generators.filter fun generator =>
    generator ∈ relativeWordOccupation start word

/-- Absolute and moving-coordinate legality tests give the same action set. -/
theorem legalCayleyActions_eq_filter_not_relative
    (generators : Finset G) (start : G) (word : List G) :
    legalCayleyActions generators start word =
      generators.filter fun generator =>
        generator ∉ relativeWordOccupation start word := by
  ext generator
  simp only [Finset.mem_filter, mem_legalCayleyActions_iff]
  constructor
  · rintro ⟨hgenerator, hfresh⟩
    exact ⟨hgenerator,
      (next_fresh_iff_not_mem_relativeOccupation
        (cayleyOccupationEndpoint start word) generator
        (cayleyOccupationStates start word).toFinset).mp
        (by simpa using hfresh)⟩
  · rintro ⟨hgenerator, hfresh⟩
    refine ⟨hgenerator, ?_⟩
    simpa using
      (next_fresh_iff_not_mem_relativeOccupation
        (cayleyOccupationEndpoint start word) generator
        (cayleyOccupationStates start word).toFinset).mpr hfresh

/-- Legal and blocked choices partition the entire generator frame. -/
theorem card_legal_add_card_blocked (generators : Finset G)
    (start : G) (word : List G) :
    (legalCayleyActions generators start word).card +
        (blockedCayleyActions generators start word).card =
      generators.card := by
  rw [legalCayleyActions_eq_filter_not_relative]
  simpa [blockedCayleyActions, add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := generators)
      (fun generator => generator ∈ relativeWordOccupation start word))

/-! ## Exact finite Bellman frontier -/

/-- Append every currently legal action to every word in a finite frontier.
The dependent pair retains the parent word, so this operation is the exact
one-step transition rather than a union-bound approximation. -/
def extendLegalCayleyFrontier (generators : Finset G) (start : G)
    (frontier : Finset (List G)) : Finset (List G) :=
  (frontier.sigma fun word => legalCayleyActions generators start word).image
    fun choice => choice.1 ++ [choice.2]

theorem mem_extendLegalCayleyFrontier_iff (generators : Finset G) (start : G)
    (frontier : Finset (List G)) (word : List G) :
    word ∈ extendLegalCayleyFrontier generators start frontier ↔
      ∃ parent ∈ frontier, ∃ generator ∈
        legalCayleyActions generators start parent,
        parent ++ [generator] = word := by
  simp only [extendLegalCayleyFrontier, Finset.mem_image, Finset.mem_sigma]
  constructor
  · rintro ⟨⟨parent, generator⟩, ⟨hparent, hgenerator⟩, heq⟩
    exact ⟨parent, hparent, generator, hgenerator, heq⟩
  · rintro ⟨parent, hparent, generator, hgenerator, heq⟩
    exact ⟨⟨parent, generator⟩, ⟨hparent, hgenerator⟩, heq⟩

omit [Group G] [DecidableEq G] in
/-- Appending one final generator is injective on parent/action pairs. -/
lemma appendSingletonSigma_injective :
    Function.Injective
      (fun choice : Sigma fun _word : List G => G =>
        choice.1 ++ [choice.2]) := by
  rintro ⟨leftWord, leftGenerator⟩ ⟨rightWord, rightGenerator⟩ heq
  have hlength : leftWord.length = rightWord.length := by
    have := congrArg List.length heq
    simp only [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨hword, hgenerator⟩ := List.append_inj heq hlength
  change leftWord = rightWord at hword
  change [leftGenerator] = [rightGenerator] at hgenerator
  subst rightWord
  have : leftGenerator = rightGenerator := by simpa using hgenerator
  subst rightGenerator
  rfl

/-- Exact cardinality of one Bellman expansion: the next frontier is the sum
of the legal degrees of its parents. -/
theorem card_extendLegalCayleyFrontier (generators : Finset G) (start : G)
    (frontier : Finset (List G)) :
    (extendLegalCayleyFrontier generators start frontier).card =
      ∑ word ∈ frontier, (legalCayleyActions generators start word).card := by
  rw [extendLegalCayleyFrontier,
    (Finset.card_image_iff.mpr appendSingletonSigma_injective.injOn),
    Finset.card_sigma]

/-- The exact finite legal-word frontier, built from the empty word by the
stateful occupation transition. -/
def legalCayleyWordFrontier (generators : Finset G) (start : G) :
    ℕ → Finset (List G)
  | 0 => {[]}
  | horizon + 1 =>
      extendLegalCayleyFrontier generators start
        (legalCayleyWordFrontier generators start horizon)

@[simp]
theorem legalCayleyWordFrontier_zero (generators : Finset G) (start : G) :
    legalCayleyWordFrontier generators start 0 = {[]} := rfl

@[simp]
theorem legalCayleyWordFrontier_succ (generators : Finset G) (start : G)
    (horizon : ℕ) :
    legalCayleyWordFrontier generators start (horizon + 1) =
      extendLegalCayleyFrontier generators start
        (legalCayleyWordFrontier generators start horizon) := rfl

/-- Concrete Bellman recurrence for exact Cayley occupation.  This is the
identity computed by the OpenCL edge ledger at every completed horizon. -/
theorem card_legalCayleyWordFrontier_succ (generators : Finset G) (start : G)
    (horizon : ℕ) :
    (legalCayleyWordFrontier generators start (horizon + 1)).card =
      ∑ word ∈ legalCayleyWordFrontier generators start horizon,
        (legalCayleyActions generators start word).card := by
  rw [legalCayleyWordFrontier_succ, card_extendLegalCayleyFrontier]

/-- Every recursively generated frontier word has the advertised length. -/
theorem length_eq_of_mem_legalCayleyWordFrontier
    (generators : Finset G) (start : G) {horizon : ℕ} {word : List G}
    (hword : word ∈ legalCayleyWordFrontier generators start horizon) :
    word.length = horizon := by
  induction horizon generalizing word with
  | zero => simpa using hword
  | succ horizon ih =>
      simp only [legalCayleyWordFrontier_succ, extendLegalCayleyFrontier,
        Finset.mem_image, Finset.mem_sigma] at hword
      obtain ⟨⟨parent, generator⟩, ⟨hparent, _haction⟩, rfl⟩ := hword
      simp [ih hparent]

/-- Every recursively generated frontier word is genuinely occupation-legal.
Together with the recurrence, this connects the finite census to the global
identity-factor-free grammar. -/
theorem legal_of_mem_legalCayleyWordFrontier
    (generators : Finset G) (start : G) {horizon : ℕ} {word : List G}
    (hword : word ∈ legalCayleyWordFrontier generators start horizon) :
    CayleyOccupationLegal start word := by
  induction horizon generalizing word with
  | zero =>
      have : word = [] := by simpa using hword
      subst word
      simp [CayleyOccupationLegal, cayleyOccupationStates]
  | succ horizon ih =>
      simp only [legalCayleyWordFrontier_succ, extendLegalCayleyFrontier,
        Finset.mem_image, Finset.mem_sigma] at hword
      obtain ⟨⟨parent, generator⟩, ⟨hparent, haction⟩, rfl⟩ := hword
      exact (mem_legalCayleyActions_iff_legal_append generators start parent
        generator (ih hparent)).mp haction |>.2

/-- The recursive frontier is complete as well as sound: it contains exactly
the legal generator words of the specified length. -/
theorem mem_legalCayleyWordFrontier_iff
    (generators : Finset G) (start : G) (horizon : ℕ) (word : List G) :
    word ∈ legalCayleyWordFrontier generators start horizon ↔
      word.length = horizon ∧
        (∀ generator ∈ word, generator ∈ generators) ∧
          CayleyOccupationLegal start word := by
  induction horizon generalizing word with
  | zero =>
      constructor
      · intro hword
        have hnil : word = [] := by simpa using hword
        subst word
        simp [CayleyOccupationLegal, cayleyOccupationStates]
      · rintro ⟨hlength, _hgenerators, _hlegal⟩
        have hnil : word = [] := by simpa using hlength
        subst word
        simp
  | succ horizon ih =>
      constructor
      · intro hword
        rw [legalCayleyWordFrontier_succ,
          mem_extendLegalCayleyFrontier_iff] at hword
        obtain ⟨parent, hparent, generator, haction, rfl⟩ := hword
        obtain ⟨hparentLength, hparentGenerators, hparentLegal⟩ :=
          (ih parent).mp hparent
        obtain ⟨hgenerator, happendLegal⟩ :=
          (mem_legalCayleyActions_iff_legal_append generators start parent
            generator hparentLegal).mp haction
        refine ⟨by simp [hparentLength], ?_, happendLegal⟩
        intro element helement
        simp only [List.mem_append, List.mem_singleton] at helement
        rcases helement with helement | rfl
        · exact hparentGenerators element helement
        · exact hgenerator
      · rintro ⟨hlength, hgenerators, hlegal⟩
        induction word using List.reverseRecOn with
        | nil => simp at hlength
        | append_singleton parent generator =>
            rw [legalCayleyWordFrontier_succ,
              mem_extendLegalCayleyFrontier_iff]
            have hparentLength : parent.length = horizon := by
              simp only [List.length_append, List.length_singleton] at hlength
              omega
            have hparentGenerators :
                ∀ element ∈ parent, element ∈ generators := by
              intro element helement
              exact hgenerators element (by simp [helement])
            have hparentLegal : CayleyOccupationLegal start parent :=
              (cayleyOccupationLegal_append_iff_no_suffix_return
                start parent generator).mp hlegal |>.1
            have hparent :
                parent ∈ legalCayleyWordFrontier generators start horizon :=
              (ih parent).mpr
                ⟨hparentLength, hparentGenerators, hparentLegal⟩
            refine ⟨parent, hparent, generator, ?_, rfl⟩
            apply (mem_legalCayleyActions_iff_legal_append generators start
              parent generator hparentLegal).mpr
            exact ⟨hgenerators generator (by simp), hlegal⟩

/-- A legal word of length `t` has exactly `t+1` occupied relative
addresses, including the identity coordinate for its current endpoint. -/
theorem card_relativeWordOccupation_of_legal
    {start : G} {word : List G} (hlegal : CayleyOccupationLegal start word) :
    (relativeWordOccupation start word).card = word.length + 1 := by
  have htranslate :
      ((cayleyOccupationStates start word).toFinset.image
        (fun oldAddress =>
          (cayleyOccupationEndpoint start word)⁻¹ * oldAddress)).card =
        (cayleyOccupationStates start word).toFinset.card := by
    rw [Finset.card_image_iff]
    intro left hleft right hright heq
    exact mul_left_cancel heq
  rw [relativeWordOccupation, relativeOccupation, htranslate]
  change (cayleyOccupationStates start word).Nodup at hlegal
  rw [List.toFinset_card_of_nodup hlegal]
  simp [cayleyOccupationStates]

/-- The number of blocked actions is at most the number of occupied
addresses. -/
theorem card_blockedCayleyActions_le_relative
    (generators : Finset G) (start : G) (word : List G) :
    (blockedCayleyActions generators start word).card ≤
      (relativeWordOccupation start word).card := by
  apply Finset.card_le_card
  intro generator hgenerator
  simp only [blockedCayleyActions, Finset.mem_filter] at hgenerator
  exact hgenerator.2

/-- General early-frontier bound: after a legal word of length `t`, at
least `|generators|-(t+1)` actions remain.  The bound is independent of the
ambient group size and makes the generator-frame normalization explicit. -/
theorem card_generators_sub_length_le_legal
    (generators : Finset G) (start : G) (word : List G)
    (hlegal : CayleyOccupationLegal start word) :
    generators.card - (word.length + 1) ≤
      (legalCayleyActions generators start word).card := by
  have hblocked :
      (blockedCayleyActions generators start word).card ≤ word.length + 1 := by
    rw [← card_relativeWordOccupation_of_legal hlegal]
    exact card_blockedCayleyActions_le_relative generators start word
  have hpartition := card_legal_add_card_blocked generators start word
  omega

/-- The moving-coordinate formula transports the entire accumulated ledger,
not merely the current decision frame. -/
theorem relativeOccupation_step (endpoint g : G) (occupied : Finset G) :
    relativeOccupation (endpoint * g) (insert (endpoint * g) occupied) =
      advanceRelativeOccupation g (relativeOccupation endpoint occupied) := by
  ext address
  constructor
  · intro haddress
    simp only [relativeOccupation, Finset.mem_image] at haddress
    obtain ⟨oldAddress, hold, hcoordinate⟩ := haddress
    rw [Finset.mem_insert] at hold
    simp only [advanceRelativeOccupation, Finset.mem_insert,
      Finset.mem_image]
    rcases hold with rfl | hold
    · left
      simpa using hcoordinate.symm
    · right
      refine ⟨endpoint⁻¹ * oldAddress, ?_, ?_⟩
      · simp only [relativeOccupation, Finset.mem_image]
        exact ⟨oldAddress, hold, rfl⟩
      · simpa [mul_inv_rev, mul_assoc] using hcoordinate
  · intro haddress
    simp only [advanceRelativeOccupation, Finset.mem_insert,
      Finset.mem_image] at haddress
    simp only [relativeOccupation, Finset.mem_image]
    rcases haddress with hidentity | ⟨relativeAddress, hrelative, hstep⟩
    · refine ⟨endpoint * g,
        Finset.mem_insert_self (endpoint * g) occupied, ?_⟩
      simp [hidentity]
    · simp only [relativeOccupation, Finset.mem_image] at hrelative
      obtain ⟨oldAddress, hold, hcoordinate⟩ := hrelative
      refine ⟨oldAddress, Finset.mem_insert_of_mem hold, ?_⟩
      calc
        (endpoint * g)⁻¹ * oldAddress =
            g⁻¹ * (endpoint⁻¹ * oldAddress) := by
              simp [mul_inv_rev, mul_assoc]
        _ = g⁻¹ * relativeAddress := by rw [hcoordinate]
        _ = address := hstep

/-- Moving to relative coordinates preserves the number of occupied
addresses. -/
theorem card_relativeOccupation (endpoint : G) (occupied : Finset G) :
    (relativeOccupation endpoint occupied).card = occupied.card := by
  rw [relativeOccupation, Finset.card_image_iff]
  intro left hleft right hright heq
  exact mul_left_cancel heq

/-- Every legal relative-cache step writes exactly one new bit. -/
theorem card_advanceRelativeOccupation {g : G} {relative : Finset G}
    (hfresh : g ∉ relative) :
    (advanceRelativeOccupation g relative).card = relative.card + 1 := by
  have hone : 1 ∉ relative.image (fun address => g⁻¹ * address) := by
    intro hmem
    simp only [Finset.mem_image] at hmem
    obtain ⟨address, hrelative, hcoordinate⟩ := hmem
    apply hfresh
    have : address = g := by
      calc
        address = g * (g⁻¹ * address) := by simp
        _ = g := by rw [hcoordinate, mul_one]
    simpa [this] using hrelative
  rw [advanceRelativeOccupation, Finset.card_insert_of_notMem hone]
  congr 1
  rw [Finset.card_image_iff]
  intro left hleft right hright heq
  exact mul_left_cancel heq

/-! ## Exact two-step occupation -/

/-- Generators whose inverse is also available in the same frame. -/
def inverseSupportedGenerators (generators : Finset G) : Finset G :=
  generators.filter fun generator => generator⁻¹ ∈ generators

/-- Ordered generator pairs that return to the occupied root in two steps. -/
def twoStepReturnPairs (generators : Finset G) : Finset (G × G) :=
  (generators ×ˢ generators).filter fun pair => pair.1 * pair.2 = 1

/-- A two-step root return is uniquely determined by its first generator;
the second generator must be its inverse. -/
def twoStepReturnPairEquiv (generators : Finset G) :
    ↥(twoStepReturnPairs generators) ≃
      ↥(inverseSupportedGenerators generators) where
  toFun pair := by
    refine ⟨pair.1.1, ?_⟩
    have hpair := pair.2
    simp only [twoStepReturnPairs, Finset.mem_filter,
      Finset.mem_product] at hpair
    have hinverse : pair.1.2 = pair.1.1⁻¹ := by
      calc
        pair.1.2 = pair.1.1⁻¹ * (pair.1.1 * pair.1.2) := by
          simp
        _ = pair.1.1⁻¹ := by rw [hpair.2, mul_one]
    simp only [inverseSupportedGenerators, Finset.mem_filter]
    exact ⟨hpair.1.1, hinverse ▸ hpair.1.2⟩
  invFun generator := by
    refine ⟨(generator.1, generator.1⁻¹), ?_⟩
    have hgenerator := generator.2
    simp only [inverseSupportedGenerators, Finset.mem_filter] at hgenerator
    simp [twoStepReturnPairs, hgenerator]
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hpair := pair.2
      simp only [twoStepReturnPairs, Finset.mem_filter,
        Finset.mem_product] at hpair
      calc
        pair.1.1⁻¹ = pair.1.1⁻¹ * (pair.1.1 * pair.1.2) := by
          rw [hpair.2, mul_one]
        _ = pair.1.2 := by simp
  right_inv generator := by
    rfl

/-- Exact group-level identity behind the two-step killed mass. -/
theorem card_twoStepReturnPairs (generators : Finset G) :
    (twoStepReturnPairs generators).card =
      (inverseSupportedGenerators generators).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (twoStepReturnPairEquiv generators)

/-- Immediate inverse returns can occupy at most one second action per first
action. -/
theorem card_twoStepReturnPairs_le (generators : Finset G) :
    (twoStepReturnPairs generators).card ≤ generators.card := by
  rw [card_twoStepReturnPairs]
  exact Finset.card_filter_le _ _

end OccupationCayley

section DeletedCharacter

variable {G : Type*} [Group G] [Fintype G]

/-- A finite-group character taking the value `-1` has zero total sum.  The
proof pairs/reindexes states by right multiplication. -/
theorem character_sum_eq_zero_of_value_neg_one (character : G →* ℤ)
    (oddElement : G) (hodd : character oddElement = -1) :
    ∑ state : G, character state = 0 := by
  let total : ℤ := ∑ state : G, character state
  have hreindex :
      (∑ state : G, character (state * oddElement)) = total := by
    exact Equiv.sum_comp (Equiv.mulRight oddElement) character
  have hneg : total = -total := by
    calc
      total = ∑ state : G, character (state * oddElement) := hreindex.symm
      _ = ∑ state : G, character state * character oddElement := by
        simp_rw [map_mul]
      _ = -total := by simp [total, hodd]
  omega

variable [DecidableEq G]

/-- Deleting the identity from a zero-sum character leaves signed numerator
`-1`.  Thus the uniform measure on the remaining states has character mean
`-1 / (|G|-1)`. -/
theorem character_sum_erase_identity (character : G →* ℤ)
    (hsum : (∑ state : G, character state) = 0) :
    ∑ state ∈ (Finset.univ.erase (1 : G)), character state = -1 := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset G)
    character (Finset.mem_univ (1 : G))
  simp only [map_one] at hsplit
  rw [hsum] at hsplit
  omega

variable {Address : Type*} [Fintype Address] [DecidableEq Address]
  [Nontrivial Address]

/-- Permutation sign is balanced whenever the address type has at least two
elements. -/
theorem permutationSignCharacter_sum_eq_zero :
    ∑ permutation : Equiv.Perm Address,
      permutationSignCharacter permutation = 0 := by
  obtain ⟨oddPermutation, hoddPermutation⟩ :=
    Equiv.Perm.sign_surjective Address (-1)
  apply character_sum_eq_zero_of_value_neg_one
    permutationSignCharacter oddPermutation
  simpa [permutationSignCharacter] using
    congrArg (fun unit : ℤˣ => (unit : ℤ)) hoddPermutation

/-- Removing the even identity permutation creates signed numerator `-1`.
This is the exact source of the parity bias seen in the root-killed walk. -/
theorem permutationSignCharacter_sum_erase_identity :
    ∑ permutation ∈
        (Finset.univ.erase (1 : Equiv.Perm Address)),
      permutationSignCharacter permutation = -1 :=
  character_sum_erase_identity permutationSignCharacter
    permutationSignCharacter_sum_eq_zero

end DeletedCharacter

end Charlieplex

end Coeff2
