import Coeff2.CharlieLiteralState
import Coeff2.CharlieFrobeniusLedger
import Mathlib.Tactic

/-!
# Phase-anchored literal packets and finite Frobenius reservoirs

Packets are actual appended symbol strings. Their footprints include every
permutation window crossing their incoming suffix. No occupation predicate
is inferred from cost, parity, or the number of matrix cells.
-/

namespace Coeff2.Charlieplex.LiteralReservoir

/-- All new permutation occurrences, including seam windows. -/
def emitted (n : ℕ) (boundary : List ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | symbol :: rest =>
    let window := boundary ++ [symbol]
    (if literalPermTest n window then [window] else []) ++
      emitted n (lastSymbols (n - 1) window) rest

def endBoundary (n : ℕ) (boundary : List ℕ) : List ℕ → List ℕ
  | [] => boundary
  | symbol :: rest =>
    endBoundary n (lastSymbols (n - 1) (boundary ++ [symbol])) rest

theorem run_boundary (n : ℕ) (state : LiteralSearchState) (word : List ℕ) :
    (literalStateRun n state word).boundary = endBoundary n state.boundary word := by
  induction word generalizing state with
  | nil => rfl
  | cons symbol rest ih =>
    simpa [literalStateRun, literalStateStep, endBoundary] using
      ih (literalStateStep n state symbol)

theorem run_length (n : ℕ) (state : LiteralSearchState) (word : List ℕ) :
    (literalStateRun n state word).length = state.length + word.length := by
  induction word generalizing state with
  | nil => simp [literalStateRun]
  | cons symbol rest ih =>
    simp [literalStateRun, ih, literalStateStep, Nat.add_comm, Nat.add_left_comm]

theorem run_alphabet (n : ℕ) (state : LiteralSearchState) (word : List ℕ) :
    (literalStateRun n state word).alphabetOK =
      (state.alphabetOK && literalAlphabetTest n word) := by
  induction word generalizing state with
  | nil => simp [literalStateRun, literalAlphabetTest]
  | cons symbol rest ih =>
    simp [literalStateRun, ih, literalStateStep, literalAlphabetTest, Bool.and_assoc]

theorem run_occupation (n : ℕ) (state : LiteralSearchState) (word : List ℕ) :
    (literalStateRun n state word).occupied =
      state.occupied ∪ (emitted n state.boundary word).toFinset := by
  induction word generalizing state with
  | nil => simp [literalStateRun, emitted]
  | cons symbol rest ih =>
    rw [literalStateRun, ih]
    by_cases hh : literalPermTest n (state.boundary ++ [symbol]) = true
    · simp [literalStateStep, emitted, hh, Finset.insert_union]
    · simp [literalStateStep, emitted, hh]

/-- Complete no-repeat criterion for a literal packet, with incoming
occupation and all internal/seam occurrences accounted for separately. -/
theorem run_noRepeat_iff (n : ℕ) (state : LiteralSearchState) (word : List ℕ) :
    (literalStateRun n state word).noRepeat = true ↔
      state.noRepeat = true ∧ (emitted n state.boundary word).Nodup ∧
      Disjoint (emitted n state.boundary word).toFinset state.occupied := by
  induction word generalizing state with
  | nil => simp [literalStateRun, emitted]
  | cons symbol rest ih =>
    rw [literalStateRun, ih]
    by_cases hh : literalPermTest n (state.boundary ++ [symbol]) = true
    · simp [literalStateStep, emitted, hh, List.nodup_cons,
        Finset.disjoint_insert_left, Finset.disjoint_insert_right,
        and_assoc, and_left_comm, and_comm]
    · simp [literalStateStep, emitted, hh]

theorem endBoundary_append (n : ℕ) (boundary left right : List ℕ) :
    endBoundary n boundary (left ++ right) =
      endBoundary n (endBoundary n boundary left) right := by
  induction left generalizing boundary with
  | nil => rfl
  | cons symbol rest ih => simp [endBoundary, ih]

theorem emitted_append (n : ℕ) (boundary left right : List ℕ) :
    emitted n boundary (left ++ right) =
      emitted n boundary left ++ emitted n (endBoundary n boundary left) right := by
  induction left generalizing boundary with
  | nil => rfl
  | cons symbol rest ih => simp [emitted, endBoundary, ih, List.append_assoc]

/-- A two-terminal literal transfer. Its phase anchor is the exact incoming
suffix; coarser phase labels may be used only with a separately proved lift. -/
structure Transfer (n : ℕ) where
  incoming : List ℕ
  outgoing : List ℕ
  text : List ℕ
  alphabet : literalAlphabetTest n text = true
  boundary_correct : endBoundary n incoming text = outgoing
  noInternalRepeat : (emitted n incoming text).Nodup

def Transfer.footprint {n : ℕ} (piece : Transfer n) : List (List ℕ) :=
  emitted n piece.incoming piece.text

/-- Partial, directed composition: boundary matching and disjoint footprints
are explicit. Neither a cost equality nor parity alone replaces these tests. -/
def Transfer.compose {n : ℕ} (left right : Transfer n)
    (hmatch : left.outgoing = right.incoming)
    (hfree : Disjoint left.footprint.toFinset right.footprint.toFinset) : Transfer n where
  incoming := left.incoming
  outgoing := right.outgoing
  text := left.text ++ right.text
  alphabet := by
    have hA := left.alphabet
    have hB := right.alphabet
    simpa only [literalAlphabetTest, List.all_append, Bool.and_eq_true] using And.intro hA hB
  boundary_correct := by
    rw [endBoundary_append, left.boundary_correct, hmatch, right.boundary_correct]
  noInternalRepeat := by
    rw [emitted_append, left.boundary_correct, hmatch]
    apply List.nodup_append'.mpr
    refine ⟨left.noInternalRepeat, right.noInternalRepeat, ?_⟩
    intro p hp hq
    exact Finset.disjoint_left.mp hfree (List.mem_toFinset.mpr hp) (List.mem_toFinset.mpr hq)

theorem Transfer.compose_cost {n : ℕ} (left right : Transfer n)
    (hmatch : left.outgoing = right.incoming)
    (hfree : Disjoint left.footprint.toFinset right.footprint.toFinset) :
    (left.compose right hmatch hfree).text.length = left.text.length + right.text.length := by
  simp [Transfer.compose]

theorem Transfer.compose_footprint {n : ℕ} (left right : Transfer n)
    (hmatch : left.outgoing = right.incoming)
    (hfree : Disjoint left.footprint.toFinset right.footprint.toFinset) :
    (left.compose right hmatch hfree).footprint = left.footprint ++ right.footprint := by
  simp [Transfer.footprint, Transfer.compose, emitted_append, left.boundary_correct, hmatch]

/-- Cached boundary and footprint checks suffice to apply a transfer to the
full literal state. This includes hidden/seam windows and the incoming cache. -/
theorem Transfer.apply_sound {n : ℕ} (piece : Transfer n) (state : LiteralSearchState)
    (hmatch : state.boundary = piece.incoming)
    (halpha : state.alphabetOK = true) (hno : state.noRepeat = true)
    (hfree : Disjoint piece.footprint.toFinset state.occupied) :
    (literalStateRun n state piece.text).boundary = piece.outgoing ∧
    (literalStateRun n state piece.text).alphabetOK = true ∧
    (literalStateRun n state piece.text).noRepeat = true ∧
    (literalStateRun n state piece.text).occupied = state.occupied ∪ piece.footprint.toFinset := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run_boundary, hmatch, piece.boundary_correct]
  · rw [run_alphabet, halpha, piece.alphabet]
    rfl
  · rw [run_noRepeat_iff, hmatch]
    exact ⟨hno, piece.noInternalRepeat, hfree⟩
  · rw [run_occupation, hmatch]
    rfl

/-- Exact two-terminal cover identity for an actual literal prefix. Coverage
does not need a return loop, divisibility condition, or no-repeat assumption.
The separate soundness theorem enforces single-use occupation. -/
theorem Transfer.completion_iff (n : ℕ) (hn : 1 ≤ n) (text : List ℕ)
    (piece : Transfer n) (hmatch : (literalStateOf n text).boundary = piece.incoming) :
    IsSuperperm n (text ++ piece.text) ↔
      ∀ p, IsPermWord n p →
        p ∈ (literalStateOf n text).occupied ∪ piece.footprint.toFinset := by
  have hocc := run_occupation n (literalStateOf n text) piece.text
  rw [literalStateRun_correct n hn, hmatch] at hocc
  rw [← literalOccupation_covers_iff n (text ++ piece.text)]
  change (∀ p, IsPermWord n p →
    p ∈ (literalStateOf n (text ++ piece.text)).occupied) ↔ _
  rw [hocc]
  rfl

/-- Two-terminal exact-cover gluing, including alphabet and single-use
occupation, concludes the original literal definition of superpermutation. -/
theorem Transfer.complete (n : ℕ) (hn : 1 ≤ n) (text : List ℕ)
    (piece : Transfer n) (hmatch : (literalStateOf n text).boundary = piece.incoming)
    (halpha : (literalStateOf n text).alphabetOK = true)
    (hstart : (literalStateOf n text).noRepeat = true)
    (hfree : Disjoint piece.footprint.toFinset (literalStateOf n text).occupied)
    (hcover : ∀ p, IsPermWord n p →
      p ∈ (literalStateOf n text).occupied ∪ piece.footprint.toFinset) :
    IsSuperperm n (text ++ piece.text) ∧
    literalAlphabetTest n (text ++ piece.text) = true ∧
    (literalPermutationWindows n (text ++ piece.text)).Nodup := by
  have hl := piece.apply_sound (literalStateOf n text) hmatch halpha hstart hfree
  rw [literalStateRun_correct n hn] at hl
  exact ⟨(piece.completion_iff n hn text hmatch).mpr hcover, hl.2.1,
    (literalNoRepeatTest_eq_true n _).mp hl.2.2.1⟩

/-- Concrete packet certificate. Full n-1-symbol suffix equality is stronger
than a parity bit or a projected phase label. -/
structure Packet (n : ℕ) (boundary : List ℕ) where
  text : List ℕ
  alphabet : literalAlphabetTest n text = true
  returns : endBoundary n boundary text = boundary
  noInternalRepeat : (emitted n boundary text).Nodup

def packetWindows {n : ℕ} {boundary : List ℕ} (packet : Packet n boundary) :
    List (List ℕ) := emitted n boundary packet.text

def spellPackets {n : ℕ} {boundary : List ℕ} (packets : List (Packet n boundary)) :
    List ℕ := packets.flatMap Packet.text

def packetFootprints {n : ℕ} {boundary : List ℕ}
    (packets : List (Packet n boundary)) : List (List ℕ) :=
  packets.flatMap packetWindows

theorem packets_return {n : ℕ} {boundary : List ℕ}
    (packets : List (Packet n boundary)) :
    endBoundary n boundary (spellPackets packets) = boundary := by
  induction packets with
  | nil => rfl
  | cons packet rest ih =>
    simpa [spellPackets, endBoundary_append, packet.returns] using ih

theorem packets_emitted {n : ℕ} {boundary : List ℕ}
    (packets : List (Packet n boundary)) :
    emitted n boundary (spellPackets packets) = packetFootprints packets := by
  induction packets with
  | nil => rfl
  | cons packet rest ih =>
    simp only [spellPackets, packetFootprints] at ih
    simp [spellPackets, packetFootprints, emitted_append, packet.returns, ih, packetWindows]

theorem packets_alphabet {n : ℕ} {boundary : List ℕ}
    (packets : List (Packet n boundary)) :
    literalAlphabetTest n (spellPackets packets) = true := by
  induction packets with
  | nil => simp [spellPackets, literalAlphabetTest]
  | cons packet rest ih =>
    have hp := packet.alphabet
    simp only [literalAlphabetTest] at hp
    simp only [spellPackets, List.flatMap_cons, literalAlphabetTest, List.all_append] at *
    rw [hp, ih]
    rfl

/-- Literal gluing through a common suffix with exact, seam-aware occupation.
The footprint tests are finite tests on actual packet strings. -/
theorem packets_legal {n : ℕ} {boundary : List ℕ}
    (state : LiteralSearchState) (packets : List (Packet n boundary))
    (hboundary : state.boundary = boundary)
    (halpha : state.alphabetOK = true) (hstart : state.noRepeat = true)
    (hocc : (packetFootprints packets).Nodup)
    (hfree : Disjoint (packetFootprints packets).toFinset state.occupied) :
    (literalStateRun n state (spellPackets packets)).boundary = boundary ∧
    (literalStateRun n state (spellPackets packets)).alphabetOK = true ∧
    (literalStateRun n state (spellPackets packets)).noRepeat = true ∧
    (literalStateRun n state (spellPackets packets)).occupied =
      state.occupied ∪ (packetFootprints packets).toFinset := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run_boundary, hboundary, packets_return]
  · rw [run_alphabet, halpha, packets_alphabet]
    rfl
  · rw [run_noRepeat_iff, hboundary, packets_emitted]
    exact ⟨hstart, hocc, hfree⟩
  · rw [run_occupation, hboundary, packets_emitted]

/-- Any selected sub-reservoir stays occupation-safe. Availability cannot be
reused: sublists select copies already present in this finite reservoir. -/
theorem sublist_packets_legal {n : ℕ} {boundary : List ℕ}
    (state : LiteralSearchState) (whole selected : List (Packet n boundary))
    (hsub : selected.Sublist whole)
    (hboundary : state.boundary = boundary)
    (halpha : state.alphabetOK = true) (hstart : state.noRepeat = true)
    (hocc : (packetFootprints whole).Nodup)
    (hfree : Disjoint (packetFootprints whole).toFinset state.occupied) :
    (literalStateRun n state (spellPackets selected)).boundary = boundary ∧
    (literalStateRun n state (spellPackets selected)).alphabetOK = true ∧
    (literalStateRun n state (spellPackets selected)).noRepeat = true ∧
    (literalStateRun n state (spellPackets selected)).occupied =
      state.occupied ∪ (packetFootprints selected).toFinset := by
  have hf : (packetFootprints selected).Sublist (packetFootprints whole) :=
    hsub.flatMap packetWindows
  apply packets_legal state selected hboundary halpha hstart (hocc.sublist hf)
  apply hfree.mono_left
  intro p hp
  exact List.mem_toFinset.mpr (hf.subset (List.mem_toFinset.mp hp))

theorem spellPackets_length_uniform {n : ℕ} {boundary : List ℕ}
    (packets : List (Packet n boundary)) (cost : ℕ)
    (hlen : ∀ p ∈ packets, p.text.length = cost) :
    (spellPackets packets).length = packets.length * cost := by
  induction packets with
  | nil => simp [spellPackets]
  | cons packet rest ih =>
    have hp := hlen packet List.mem_cons_self
    have hr := ih (fun p h => hlen p (List.mem_cons_of_mem packet h))
    simp only [spellPackets, List.flatMap_cons, List.length_append,
      List.length_cons] at *
    rw [hp, hr]
    ring

/-- Exact finite-resource bridge, also valid below the conductor. -/
theorem bounded_realizes_literal_extension {n : ℕ} {boundary : List ℕ}
    (state : LiteralSearchState) (as bs : List (Packet n boundary)) (a b t : ℕ)
    (hcost : FrobeniusLedger.BoundedRepresentable a b as.length bs.length t)
    (hlenA : ∀ p ∈ as, p.text.length = a)
    (hlenB : ∀ p ∈ bs, p.text.length = b)
    (hboundary : state.boundary = boundary)
    (halpha : state.alphabetOK = true) (hstart : state.noRepeat = true)
    (hocc : (packetFootprints (as ++ bs)).Nodup)
    (hfree : Disjoint (packetFootprints (as ++ bs)).toFinset state.occupied) :
    ∃ word : List ℕ, word.length = t ∧
      (literalStateRun n state word).boundary = boundary ∧
      (literalStateRun n state word).alphabetOK = true ∧
      (literalStateRun n state word).noRepeat = true := by
  obtain ⟨x, y, hxA, hyB, hcost⟩ := hcost
  let selected := as.take x ++ bs.take y
  have hsub : selected.Sublist (as ++ bs) :=
    (List.take_sublist x as).append (List.take_sublist y bs)
  have hlegal := sublist_packets_legal state (as ++ bs) selected hsub
    hboundary halpha hstart hocc hfree
  have hlenX := spellPackets_length_uniform (as.take x) a
    (fun p hp => hlenA p (List.mem_of_mem_take hp))
  have hlenY := spellPackets_length_uniform (bs.take y) b
    (fun p hp => hlenB p (List.mem_of_mem_take hp))
  refine ⟨spellPackets selected, ?_, hlegal.1, hlegal.2.1, hlegal.2.2.1⟩
  have hsp : spellPackets selected =
      spellPackets (as.take x) ++ spellPackets (bs.take y) := by
    simp [spellPackets, selected]
  rw [hsp, List.length_append, hlenX, hlenY,
    List.length_take, List.length_take, Nat.min_eq_left hxA, Nat.min_eq_left hyB]
  nlinarith

/-- The finite, occupation-aware Frobenius bridge. Sufficient supplies are
b-1 concrete a-packets and floor(t/b) concrete b-packets. The chosen packets
are actually scanned from the incoming literal state; no reusable loops or
unconditional semigroup of legal extensions is assumed. -/
theorem conductor_realizes_literal_extension {n : ℕ} {boundary : List ℕ}
    (state : LiteralSearchState) (as bs : List (Packet n boundary)) (a b t : ℕ)
    (hcop : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b)
    (ht : FrobeniusLedger.conductor a b ≤ t)
    (hA : b - 1 ≤ as.length) (hB : t / b ≤ bs.length)
    (hlenA : ∀ p ∈ as, p.text.length = a)
    (hlenB : ∀ p ∈ bs, p.text.length = b)
    (hboundary : state.boundary = boundary)
    (halpha : state.alphabetOK = true) (hstart : state.noRepeat = true)
    (hocc : (packetFootprints (as ++ bs)).Nodup)
    (hfree : Disjoint (packetFootprints (as ++ bs)).toFinset state.occupied) :
    ∃ word : List ℕ, word.length = t ∧
      (literalStateRun n state word).boundary = boundary ∧
      (literalStateRun n state word).alphabetOK = true ∧
      (literalStateRun n state word).noRepeat = true := by
  apply bounded_realizes_literal_extension state as bs a b t ?_
    hlenA hlenB hboundary halpha hstart hocc hfree
  obtain ⟨x, y, hx, hy, hcost⟩ :=
    FrobeniusLedger.conductor_bounded_witness hcop ha hb ht
  exact ⟨x, y, by omega, by omega, hcost⟩

/-- The full first-principles completion bridge. Coverage is a finite
address-ledger obligation, not an assumed IsSuperperm conclusion. -/
theorem packets_complete (n : ℕ) (hn : 1 ≤ n) (text : List ℕ)
    (packets : List (Packet n (literalStateOf n text).boundary))
    (halpha : (literalStateOf n text).alphabetOK = true)
    (hstart : (literalStateOf n text).noRepeat = true)
    (hocc : (packetFootprints packets).Nodup)
    (hfree : Disjoint (packetFootprints packets).toFinset (literalStateOf n text).occupied)
    (hcover : ∀ p, IsPermWord n p →
      p ∈ (literalStateOf n text).occupied ∪ (packetFootprints packets).toFinset) :
    IsSuperperm n (text ++ spellPackets packets) ∧
    literalAlphabetTest n (text ++ spellPackets packets) = true ∧
    (literalPermutationWindows n (text ++ spellPackets packets)).Nodup := by
  have hl := packets_legal (literalStateOf n text) packets rfl halpha hstart hocc hfree
  rw [literalStateRun_correct n hn] at hl
  refine ⟨?_, hl.2.1, ?_⟩
  · apply (literalOccupation_covers_iff n (text ++ spellPackets packets)).mp
    intro p hp
    change p ∈ (literalStateOf n (text ++ spellPackets packets)).occupied
    rw [hl.2.2.2]
    exact hcover p hp
  · exact (literalNoRepeatTest_eq_true n _).mp hl.2.2.1

/-- The pigeonhole capacity of any actual phase region. Nested regions are
tested separately; the theorem never adds a parent to its children. -/
theorem phase_region_capacity {Address : Type*} [DecidableEq Address]
    (writes occupied region : Finset Address) (hfree : Disjoint writes occupied) :
    (writes ∩ region).card ≤ (region \ occupied).card := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hw, hr⟩ := Finset.mem_inter.mp hp
  exact Finset.mem_sdiff.mpr ⟨hr, fun ho => Finset.disjoint_left.mp hfree hw ho⟩

/-- A packet with a nonempty footprint cannot be used twice at the same
phase anchor under single-use occupation. This forbids unbounded pumping
of productive packets, even though their numerical costs add freely. -/
theorem productive_packet_cannot_repeat {n : ℕ} {boundary : List ℕ}
    (state : LiteralSearchState) (packet : Packet n boundary)
    (hboundary : state.boundary = boundary) (hproductive : packetWindows packet ≠ []) :
    (literalStateRun n state (spellPackets [packet,packet])).noRepeat ≠ true := by
  intro h
  rw [run_noRepeat_iff, hboundary, packets_emitted] at h
  have hnd : (packetWindows packet ++ packetWindows packet).Nodup := by
    simpa [packetFootprints] using h.2.1
  have hd := hnd.disjoint
  cases hw : packetWindows packet with
  | nil => exact hproductive hw
  | cons w ws =>
    have hm : w ∈ packetWindows packet := by simp [hw]
    exact hd hm hm

end Coeff2.Charlieplex.LiteralReservoir
