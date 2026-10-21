import Coeff2.Statements
import Coeff2.ParityCycles
import Coeff2.CharlieOccupationCayley
import Coeff2.CharlieCacheMachine

/-!
# Literal superpermutation bridge

The address ledger in this module is computed from actual contiguous windows
of a finite symbol list.  No user-supplied realization predicates or coverage
axioms occur.  Proper overlap walks are connected to this literal ledger.
-/

namespace Coeff2
namespace Charlieplex

/-- Executable test of the project's literal permutation-word definition. -/
def literalPermTest (n : ℕ) (word : List ℕ) : Bool :=
  decide word.Nodup && decide (word.toFinset = Finset.Icc 1 n)

@[simp] theorem literalPermTest_eq_true (n : ℕ) (word : List ℕ) :
    literalPermTest n word = true ↔ IsPermWord n word := by
  simp [literalPermTest, IsPermWord]

/-- Every permutation window, in text order and retaining multiplicity.
The final empty suffix handles order zero correctly as well. -/
def literalPermutationWindows (n : ℕ) (word : List ℕ) : List (List ℕ) :=
  (word.tails.map (fun suffix => suffix.take n)).filter (literalPermTest n)

@[simp] theorem literalPermutationWindows_cons (n a : ℕ) (word : List ℕ) :
    literalPermutationWindows n (a :: word) =
      if literalPermTest n ((a :: word).take n) then
        (a :: word).take n :: literalPermutationWindows n word
      else literalPermutationWindows n word := by
  simp [literalPermutationWindows, List.filter_cons]

/-- The scanner accepts exactly the literal permutation factors of the text. -/
theorem mem_literalPermutationWindows_iff (n : ℕ) (text window : List ℕ) :
    window ∈ literalPermutationWindows n text ↔
      IsPermWord n window ∧ window <:+: text := by
  simp only [literalPermutationWindows, List.mem_filter, List.mem_map,
    literalPermTest_eq_true]
  constructor
  · rintro ⟨⟨suffix, hsuffix, rfl⟩, hperm⟩
    exact ⟨hperm, (List.take_prefix n suffix).isInfix.trans
      ((List.mem_tails suffix text).mp hsuffix).isInfix⟩
  · rintro ⟨hperm, before, after, htext⟩
    refine ⟨⟨window ++ after, ?_, ?_⟩, hperm⟩
    · apply (List.mem_tails _ _).mpr
      exact ⟨before, by simpa [List.append_assoc] using htext⟩
    · exact List.take_left' hperm.length

/-- Too-short text contributes no permutation window. -/
theorem literalPermutationWindows_eq_nil_of_short (n : ℕ) (text : List ℕ)
    (hshort : text.length < n) : literalPermutationWindows n text = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro window hwindow
  obtain ⟨hperm, hinfix⟩ := (mem_literalPermutationWindows_iff n text window).mp hwindow
  have := hinfix.length_le
  rw [hperm.length] at this
  omega

/-- Dropping positions with no permutation windows does not alter the ledger. -/
theorem literalPermutationWindows_drop (n : ℕ) (text : List ℕ) (count : ℕ)
    (hcount : count ≤ text.length)
    (hblocked : ∀ position < count,
      ¬ IsPermWord n ((text.drop position).take n)) :
    literalPermutationWindows n text =
      literalPermutationWindows n (text.drop count) := by
  induction count generalizing text with
  | zero => simp
  | succ count ih =>
      cases text with
      | nil => simp at hcount
      | cons a rest =>
          have hfirst : literalPermTest n ((a :: rest).take n) = false := by
            apply Bool.eq_false_iff.mpr
            intro htrue
            exact hblocked 0 (by omega) ((literalPermTest_eq_true _ _).mp htrue)
          rw [literalPermutationWindows_cons, hfirst]
          simp only [Bool.false_eq_true, if_false, List.drop_succ_cons]
          apply ih
          · simp only [List.length_cons] at hcount
            omega
          · intro position hposition
            simpa using hblocked (position + 1) (by omega)

/-- One first permutation followed by a literal gap with no other permutation
windows contributes exactly one ledger entry. -/
theorem literalPermutationWindows_first_gap (n : ℕ)
    (text : List ℕ) (gap : ℕ) (hgap : 0 < gap) (hbound : gap ≤ text.length)
    (hfirst : IsPermWord n (text.take n))
    (hinterior : ∀ position, 0 < position → position < gap →
      ¬ IsPermWord n ((text.drop position).take n)) :
    literalPermutationWindows n text =
      text.take n :: literalPermutationWindows n (text.drop gap) := by
  cases text with
  | nil => simp at hbound; omega
  | cons a rest =>
      have htest := (literalPermTest_eq_true _ _).mpr hfirst
      rw [literalPermutationWindows_cons, htest]
      simp only [if_true]
      have hskip := literalPermutationWindows_drop n rest (gap - 1)
        (by simp only [List.length_cons] at hbound; omega)
        (by
          intro position hposition
          simpa using hinterior (position + 1) (by omega) (by omega))
      rw [hskip]
      congr 2
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hgap)
      simp

/-- Appending later text cannot change a window already wholly present. -/
theorem literalWindow_append_of_fits (n : ℕ) (left right : List ℕ)
    (position : ℕ) (hfits : position + n ≤ left.length) :
    (((left ++ right).drop position).take n) =
      (left.drop position).take n := by
  rw [List.drop_append_of_le_length (by omega)]
  apply List.take_append_of_le_length
  simp only [List.length_drop]
  omega

/-- A single permutation word yields precisely its one full window. -/
theorem literalPermutationWindows_perm (n : ℕ) (hn : 1 ≤ n)
    (word : List ℕ) (hword : IsPermWord n word) :
    literalPermutationWindows n word = [word] := by
  have htake : word.take n = word := List.take_of_length_le (by rw [hword.length])
  have hdrop : word.drop n = [] := List.drop_eq_nil_of_le (by rw [hword.length])
  have hscan := literalPermutationWindows_first_gap n word n (by omega)
    (by rw [hword.length]) (by rwa [htake])
    (by
      intro position hpositive hlt hperm
      have hlen := hperm.length
      simp only [List.length_take, List.length_drop, hword.length] at hlen
      omega)
  rw [hscan, htake, hdrop,
    literalPermutationWindows_eq_nil_of_short n [] (by simpa)]

/-- The two usual literal spellings of one minimal-overlap edge agree. -/
theorem literalOverlap_eq_prefix_target (n : ℕ) (hn : 1 ≤ n)
    (source target : List ℕ) (hsource : IsPermWord n source) :
    overlapWord n source target = source.take (wt n source target) ++ target := by
  have hover := (wt_spec (v := target) hn (le_of_eq hsource.length)).2.2
  unfold overlapWord
  calc
    source ++ target.drop (n - wt n source target) =
        (source.take (wt n source target) ++ source.drop (wt n source target)) ++
          target.drop (n - wt n source target) := by rw [List.take_append_drop]
    _ = source.take (wt n source target) ++ target := by
      rw [hover, List.append_assoc, List.take_append_drop]

/-- No unrecorded permutation windows occur in the spelling of a proper
overlap walk.  This is equality of lists, not merely equality of sets:
order and repeated occurrences are preserved. -/
theorem literalPermutationWindows_wordOf (n : ℕ) (hn : 1 ≤ n)
    (vertices : List (List ℕ)) (hne : vertices ≠ [])
    (hperms : ∀ vertex ∈ vertices, IsPermWord n vertex)
    (hproper : vertices.IsChain (ProperStep n)) :
    literalPermutationWindows n (wordOf n vertices) = vertices := by
  induction vertices with
  | nil => exact False.elim (hne rfl)
  | cons source rest ih =>
      have hsource := hperms source List.mem_cons_self
      cases rest with
      | nil =>
          exact literalPermutationWindows_perm n hn source hsource
      | cons target rest =>
          have htailPerms : ∀ vertex ∈ target :: rest, IsPermWord n vertex :=
            fun vertex hvertex => hperms vertex (List.mem_cons_of_mem source hvertex)
          have htailProper := (List.isChain_cons_cons.mp hproper).2
          have hedge := (List.isChain_cons_cons.mp hproper).1
          have hd := wt_spec (v := target) hn (le_of_eq hsource.length)
          obtain ⟨after, hafter⟩ := word_prefix_wordOf hn rest target
            (htailPerms target List.mem_cons_self)
            (fun vertex hvertex => htailPerms vertex
              (List.mem_cons_of_mem target hvertex))
          have hspell : wordOf n (source :: target :: rest) =
              overlapWord n source target ++ after := by
            rw [literalOverlap_eq_prefix_target n hn source target hsource,
              List.append_assoc, hafter]
            rfl
          have hoverLength : (overlapWord n source target).length =
              wt n source target + n := by
            rw [literalOverlap_eq_prefix_target n hn source target hsource]
            simp only [List.length_append, List.length_take, hsource.length,
              (htailPerms target List.mem_cons_self).length, Nat.min_eq_left hd.2.1]
          have hfirst : (wordOf n (source :: target :: rest)).take n = source := by
            obtain ⟨tail, htail⟩ := word_prefix_wordOf hn (target :: rest)
              source hsource htailPerms
            rw [← htail]
            exact List.take_left' hsource.length
          have hdrop : (wordOf n (source :: target :: rest)).drop
              (wt n source target) = wordOf n (target :: rest) := by
            change (source.take (wt n source target) ++
              wordOf n (target :: rest)).drop (wt n source target) = _
            have hlength : (source.take (wt n source target)).length =
                wt n source target := by simp [hsource.length, Nat.min_eq_left hd.2.1]
            simpa only [hlength] using
              (List.drop_left (l₁ := source.take (wt n source target))
                (l₂ := wordOf n (target :: rest)))
          have hscan := literalPermutationWindows_first_gap n
            (wordOf n (source :: target :: rest)) (wt n source target)
            (by omega)
            (by rw [hspell, List.length_append, hoverLength]; omega)
            (by rwa [hfirst])
            (by
              intro position hpositive hbefore hperm
              apply hedge
              refine ⟨position, by omega, hbefore, ?_⟩
              rw [hspell, literalWindow_append_of_fits n _ _ position
                (by rw [hoverLength]; omega)] at hperm
              exact hperm)
          rw [hscan, hfirst, hdrop, ih (by simp) htailPerms htailProper]

/-- The complete literal occupancy set, computed rather than supplied. -/
def literalOccupation (n : ℕ) (text : List ℕ) : Finset (List ℕ) :=
  (literalPermutationWindows n text).toFinset

/-- Literal coverage is exactly the original superpermutation predicate.
No no-repeat hypothesis is needed. -/
theorem literalOccupation_covers_iff (n : ℕ) (text : List ℕ) :
    (∀ permutation, IsPermWord n permutation →
      permutation ∈ literalOccupation n text) ↔ IsSuperperm n text := by
  simp only [literalOccupation, List.mem_toFinset, mem_literalPermutationWindows_iff]
  constructor
  · intro h permutation hperm
    exact (h permutation hperm).2
  · intro h permutation hperm
    exact ⟨hperm, h permutation hperm⟩

/-- A proper walk's combinatorial ledger equals its actual string ledger. -/
theorem properWalk_literal_occupation {n : ℕ} (hn : 1 ≤ n) (walk : Walk n) :
    literalOccupation n (wordOf n walk.verts) = walk.verts.toFinset := by
  rw [literalOccupation,
    literalPermutationWindows_wordOf n hn walk.verts walk.ne walk.isPerm walk.chain]

/-- A proper walk spells a superpermutation exactly when its vertex ledger
covers.  The converse follows from the no-hidden-windows theorem. -/
theorem properWalk_literal_superperm_iff {n : ℕ} (hn : 1 ≤ n) (walk : Walk n) :
    IsSuperperm n (wordOf n walk.verts) ↔ walk.Covering := by
  rw [← literalOccupation_covers_iff, properWalk_literal_occupation hn walk]
  simp [Walk.Covering]

/-- No-repeat can be imposed or omitted explicitly; it is not part of the
definition of a superpermutation. -/
theorem properWalk_literal_nodup_iff {n : ℕ} (hn : 1 ≤ n) (walk : Walk n) :
    (literalPermutationWindows n (wordOf n walk.verts)).Nodup ↔ walk.verts.Nodup := by
  rw [literalPermutationWindows_wordOf n hn walk.verts walk.ne walk.isPerm walk.chain]

/-! ## Executable spelling, with no oracle for the overlap cost -/

/-- Enumerate every positive literal overlap offset. -/
def literalOverlapCandidates (n : ℕ) (source target : List ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun gap => source.drop gap = target.take (n - gap)

/-- Compute the least positive overlap offset by a finite minimum.
The zero default is used only outside the valid positive-order domain. -/
def literalOverlapCost (n : ℕ) (source target : List ℕ) : ℕ :=
  if h : (literalOverlapCandidates n source target).Nonempty then
    (literalOverlapCandidates n source target).min' h
  else 0

/-- The executable finite minimum is the exact weight of the existing
overlap graph, not an estimated cost. -/
theorem literalOverlapCost_eq_wt (n : ℕ) (hn : 1 ≤ n)
    (source target : List ℕ) (hsource : source.length ≤ n) :
    literalOverlapCost n source target = wt n source target := by
  have hnonempty : (literalOverlapCandidates n source target).Nonempty := by
    refine ⟨n, ?_⟩
    simp [literalOverlapCandidates, hn, List.drop_eq_nil_of_le hsource]
  rw [literalOverlapCost, dif_pos hnonempty]
  apply le_antisymm
  · apply Finset.min'_le
    have hspec := wt_spec (v := target) hn hsource
    simp only [literalOverlapCandidates, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hspec.1, hspec.2.1⟩, hspec.2.2⟩
  · have hmem := Finset.min'_mem (literalOverlapCandidates n source target) hnonempty
    simp only [literalOverlapCandidates, Finset.mem_filter, Finset.mem_Icc] at hmem
    exact wt_le hmem.1.1 hmem.1.2 hmem.2

/-- Spell a concrete vertex list using only finite list/number operations. -/
def literalSpelling (n : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | [vertex] => vertex
  | source :: target :: rest =>
      source.take (literalOverlapCost n source target) ++
        literalSpelling n (target :: rest)

/-- Executable spelling agrees with the foundational overlap-word builder. -/
theorem literalSpelling_eq_wordOf (n : ℕ) (hn : 1 ≤ n)
    (vertices : List (List ℕ))
    (hperms : ∀ vertex ∈ vertices, IsPermWord n vertex) :
    literalSpelling n vertices = wordOf n vertices := by
  induction vertices with
  | nil => rfl
  | cons source rest ih =>
      cases rest with
      | nil => rfl
      | cons target rest =>
          change source.take (literalOverlapCost n source target) ++
            literalSpelling n (target :: rest) =
              source.take (wt n source target) ++ wordOf n (target :: rest)
          rw [literalOverlapCost_eq_wt n hn source target
            (le_of_eq (hperms source List.mem_cons_self).length),
            ih (fun vertex hvertex => hperms vertex
              (List.mem_cons_of_mem source hvertex))]

/-- The complete literal path-to-string contract.  Costs, occurrences,
coverage, and no-repeat are all about the very same computed string. -/
theorem literalSpelling_correct {n : ℕ} (hn : 1 ≤ n) (walk : Walk n) :
    (literalSpelling n walk.verts).length = walk.len ∧
    literalPermutationWindows n (literalSpelling n walk.verts) = walk.verts ∧
    (IsSuperperm n (literalSpelling n walk.verts) ↔ walk.Covering) ∧
    ((literalPermutationWindows n (literalSpelling n walk.verts)).Nodup ↔
      walk.verts.Nodup) := by
  rw [literalSpelling_eq_wordOf n hn walk.verts walk.isPerm]
  exact ⟨wordOf_length hn walk.verts walk.ne walk.isPerm,
    literalPermutationWindows_wordOf n hn walk.verts walk.ne walk.isPerm walk.chain,
    properWalk_literal_superperm_iff hn walk,
    properWalk_literal_nodup_iff hn walk⟩

/-! ## Literal reading of a Cayley state -/

/-- Read a position permutation as the actual alphabet word `1,...,n`. -/
def positionalWord {n : ℕ} (state : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn fun position => (state position).val + 1

@[simp] theorem positionalWord_length {n : ℕ} (state : Equiv.Perm (Fin n)) :
    (positionalWord state).length = n := by simp [positionalWord]

theorem positionalWord_isPerm {n : ℕ} (state : Equiv.Perm (Fin n)) :
    IsPermWord n (positionalWord state) := by
  constructor
  · apply List.nodup_ofFn.mpr
    intro left right heq
    change (state left).val + 1 = (state right).val + 1 at heq
    apply state.injective
    apply Fin.ext
    omega
  · ext symbol
    simp only [positionalWord, List.mem_toFinset, List.mem_ofFn, Finset.mem_Icc]
    constructor
    · rintro ⟨position, rfl⟩
      have := (state position).isLt
      omega
    · rintro ⟨hpositive, hbound⟩
      let value : Fin n := ⟨symbol - 1, by omega⟩
      refine ⟨state.symm value, ?_⟩
      simp only [Equiv.apply_symm_apply]
      dsimp [value]
      omega

/-- There is no state identification hidden by the literal word decoder. -/
theorem positionalWord_injective {n : ℕ} :
    Function.Injective (positionalWord (n := n)) := by
  intro left right heq
  have hfn := List.ofFn_injective heq
  apply Equiv.ext
  intro position
  apply Fin.ext
  have := congrFun hfn position
  omega

/-- Every project permutation word decodes from its actual positional
permutation.  Together with injectivity this supplies the full word/state
correspondence, not merely a cardinality equality. -/
theorem positionalWord_wordPermutation {n : ℕ} (word : List ℕ)
    (hword : IsPermWord n word) :
    positionalWord (ParityCycles.wordPermutation word hword) = word := by
  apply List.ext_getElem (by rw [positionalWord_length, hword.length])
  intro position hleft hright
  simp only [positionalWord, List.getElem_ofFn]
  change word[position] - 1 + 1 = word[position]
  have hmem : word[position] ∈ Finset.Icc 1 n := by
    rw [← hword.toFinset_eq]
    exact List.mem_toFinset.mpr (List.getElem_mem hright)
  simp only [Finset.mem_Icc] at hmem
  omega

/-- Decode every Cayley endpoint as a literal permutation word. -/
def cayleyLiteralVertices {n : ℕ} (start : Equiv.Perm (Fin n))
    (actions : List (Equiv.Perm (Fin n))) : List (List ℕ) :=
  (cayleyOccupationStates start actions).map positionalWord

theorem cayleyLiteralVertices_ne_nil {n : ℕ} (start : Equiv.Perm (Fin n))
    (actions : List (Equiv.Perm (Fin n))) :
    cayleyLiteralVertices start actions ≠ [] := by
  intro heq
  have hlength := congrArg List.length heq
  simp [cayleyLiteralVertices, cayleyOccupationStates] at hlength

theorem cayleyLiteralVertices_isPerm {n : ℕ} (start : Equiv.Perm (Fin n))
    (actions : List (Equiv.Perm (Fin n))) :
    ∀ vertex ∈ cayleyLiteralVertices start actions, IsPermWord n vertex := by
  intro vertex hvertex
  obtain ⟨state, _hstate, rfl⟩ := List.mem_map.mp hvertex
  exact positionalWord_isPerm state

/-- Literal no-repeat and Cayley no-repeat are exactly the same condition
on the decoded endpoint list. -/
theorem cayleyLiteralVertices_nodup_iff {n : ℕ} (start : Equiv.Perm (Fin n))
    (actions : List (Equiv.Perm (Fin n))) :
    (cayleyLiteralVertices start actions).Nodup ↔
      CayleyOccupationLegal start actions := by
  exact List.nodup_map_iff positionalWord_injective

/-- Literal permutation coverage and group-state coverage are equivalent. -/
theorem cayleyLiteralVertices_cover_iff {n : ℕ} (start : Equiv.Perm (Fin n))
    (actions : List (Equiv.Perm (Fin n))) :
    (∀ vertex, IsPermWord n vertex → vertex ∈ cayleyLiteralVertices start actions) ↔
      ∀ state, state ∈ cayleyOccupationStates start actions := by
  constructor
  · intro hcover state
    obtain ⟨other, hother, heq⟩ :=
      List.mem_map.mp (hcover (positionalWord state) (positionalWord_isPerm state))
    rwa [positionalWord_injective heq] at hother
  · intro hcover vertex hvertex
    exact List.mem_map.mpr ⟨ParityCycles.wordPermutation vertex hvertex,
      hcover _, positionalWord_wordPermutation vertex hvertex⟩

/-- A Cayley trace becomes a proper overlap walk only after checking the
actual literal transitions.  No placeholder notion of realization is used. -/
def literalCayleyWalk {n : ℕ} (start : Equiv.Perm (Fin n))
    (actions : List (Equiv.Perm (Fin n)))
    (hproper : (cayleyLiteralVertices start actions).IsChain (ProperStep n)) : Walk n where
  verts := cayleyLiteralVertices start actions
  ne := cayleyLiteralVertices_ne_nil start actions
  isPerm := cayleyLiteralVertices_isPerm start actions
  chain := hproper

/-- The concrete Cayley-to-text integration contract.  Every actual window
is accounted for, the exact cost is the sum of overlap weights, coverage
means `IsSuperperm`, and no-repeat means the original occupation condition. -/
theorem cayleyLiteralSpelling_correct {n : ℕ} (hn : 1 ≤ n)
    (start : Equiv.Perm (Fin n)) (actions : List (Equiv.Perm (Fin n)))
    (hproper : (cayleyLiteralVertices start actions).IsChain (ProperStep n)) :
    let vertices := cayleyLiteralVertices start actions
    let text := literalSpelling n vertices
    text.length = n + (vertices.zipWith (wt n) vertices.tail).sum ∧
    literalPermutationWindows n text = vertices ∧
    (IsSuperperm n text ↔ ∀ state, state ∈ cayleyOccupationStates start actions) ∧
    ((literalPermutationWindows n text).Nodup ↔ CayleyOccupationLegal start actions) := by
  dsimp only
  have hcontract := literalSpelling_correct hn (literalCayleyWalk start actions hproper)
  refine ⟨hcontract.1, hcontract.2.1, ?_, ?_⟩
  · exact hcontract.2.2.1.trans (cayleyLiteralVertices_cover_iff start actions)
  · exact hcontract.2.2.2.trans (cayleyLiteralVertices_nodup_iff start actions)

end Charlieplex
end Coeff2
