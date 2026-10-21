import Coeff2.CharlieClockBellman

/-!
# Forward and backward clock specialization

This connects the exact three-type optimizer to the previous forward-only
closed formula. Prices are explicit parameters until specialized to order N.
The remaining literal-generator/occupation bridge is NOT assumed here.
-/
namespace Coeff2.Charlieplex.ClockBellman

open scoped BigOperators
open ClockMacro ClockBudget

def backward (m base wrap : ℕ) : Macro m :=
  ⟨1, fun j => if j = -1 then wrap else base⟩

def clock (m g base wrap : ℕ) : Model m :=
  ⟨forward m g true, forward m g false, backward m base wrap⟩

/-- The prices of the existing native three-type prototype. Specializing this
definition is not itself a proof of its literal packet-extraction bridge. -/
def target (N : ℕ) : Model (N-3) :=
  clock (N-3) (N^2-1) (N^2-2*N-2) (4*N^2-6*N-6)

theorem backward_wrap_phase {m : ℕ} [NeZero m] (j : ZMod m) :
    j = -1 ↔ j.val = m-1 := by
  cases m with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ m =>
    constructor
    · intro h; simp [h, ZMod.val_neg_one]
    · intro h
      have he : j.val = (-1 : ZMod (m+1)).val := by simpa [ZMod.val_neg_one] using h
      have hc := congrArg (fun v : ℕ => (v : ZMod (m+1))) he
      simpa only [ZMod.natCast_zmod_val] using hc

theorem schedule_shift {m f o b : ℕ} (g base wrap : ℕ) {xs : List Kind}
    (h : Schedule f o b xs) :
    (compile (xs.map (clock m g base wrap).move)).shift =
      (b : ZMod m) - (f : ZMod m) - (o : ZMod m) := by
  induction h with
  | nil => simp [compile, identity]
  | packet h ih =>
    simp only [List.map_cons, compile, Macro.then]
    rw [ih]
    dsimp [Model.move, clock, forward]
    push_cast; ring
  | connector h ih =>
    simp only [List.map_cons, compile, Macro.then]
    rw [ih]
    dsimp [Model.move, clock, forward]
    push_cast; ring
  | backward h ih =>
    simp only [List.map_cons, compile, Macro.then]
    rw [ih]
    dsimp [Model.move, clock, backward]
    push_cast; ring

theorem schedule_end_phase {m f o b : ℕ} (g base wrap spent : ℕ) {xs : List Kind}
    (h : Schedule f o b xs) (j : ZMod m) :
    (run (xs.map (clock m g base wrap).move) (j, spent)).1 =
      j + (b : ZMod m) - (f : ZMod m) - (o : ZMod m) := by
  rw [← compile_correct]
  change j + (compile _).shift = _
  rw [schedule_shift g base wrap h]
  ring

/-- Working back from terminal phase h, the remaining counts determine the
current phase. This does not determine occupation or literal attachment. -/
def phaseFromEnd {m : ℕ} (h : ZMod m) (f o b : ℕ) : ZMod m :=
  h - (b : ZMod m) + (f : ZMod m) + (o : ZMod m)

theorem phaseFromEnd_packet {m : ℕ} (h : ZMod m) (f o b : ℕ) :
    phaseFromEnd h (f+1) o b - 1 = phaseFromEnd h f o b := by
  simp only [phaseFromEnd, Nat.cast_add, Nat.cast_one]
  ring

theorem phaseFromEnd_connector {m : ℕ} (h : ZMod m) (f o b : ℕ) :
    phaseFromEnd h f (o+1) b - 1 = phaseFromEnd h f o b := by
  simp only [phaseFromEnd, Nat.cast_add, Nat.cast_one]
  ring

theorem phaseFromEnd_backward {m : ℕ} (h : ZMod m) (f o b : ℕ) :
    phaseFromEnd h f o (b+1) + 1 = phaseFromEnd h f o b := by
  simp only [phaseFromEnd, Nat.cast_add, Nat.cast_one]
  ring

theorem phaseFromEnd_recovers {m : ℕ} (j : ZMod m) (f o b : ℕ) :
    phaseFromEnd (j + (b : ZMod m) - (f : ZMod m) - (o : ZMod m)) f o b = j := by
  unfold phaseFromEnd
  ring

theorem schedule_fixed_end {m f o b : ℕ} (g base wrap spent : ℕ) {xs : List Kind}
    (hs : Schedule f o b xs) (h : ZMod m) :
    (run (xs.map (clock m g base wrap).move) (phaseFromEnd h f o b, spent)).1 = h := by
  rw [schedule_end_phase g base wrap spent hs]
  unfold phaseFromEnd
  ring

private theorem count_ofFn_sum {L : ℕ} (s : Fin L → Kind) (k : Kind) :
    (List.ofFn s).count k = ∑ i : Fin L, if s i = k then 1 else 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    rw [List.count_cons, ih]
    by_cases he : s 0 = k
    · subst k; simp [Nat.add_comm]
    · simp [he]

theorem count_ofFn_slots {L : ℕ} (s : Fin L → Kind) (k : Kind) :
    (List.ofFn s).count k = (Finset.univ.filter (fun i => s i = k)).card := by
  rw [count_ofFn_sum]
  simp

def packetSlots (xs : List Kind) : Finset (Fin xs.length) :=
  Finset.univ.filter (fun i => xs.get i = .packet)

theorem packetSlots_card (xs : List Kind) :
    (packetSlots xs).card = xs.count .packet := by
  have h := count_ofFn_slots xs.get .packet
  simpa [packetSlots] using h.symm

/-- Every zero-B type word is represented by the earlier finite-slot model. -/
theorem zero_backward_map {m : ℕ} (g base wrap : ℕ) (xs : List Kind)
    (hb : xs.count .backward = 0) :
    xs.map (clock m g base wrap).move = forwardPlan m xs.length g (packetSlots xs) := by
  conv_lhs => rw [← List.ofFn_get xs]
  rw [List.map_ofFn]
  unfold forwardPlan
  apply congrArg List.ofFn
  funext i
  have hi : xs.get i ∈ xs := List.get_mem xs i
  have hn : Kind.backward ∉ xs := List.count_eq_zero.mp hb
  have hm : (i ∈ packetSlots xs) ↔ xs.get i = Kind.packet := by
    simp only [packetSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [hm, Function.comp_apply]
  cases he : xs.get i with
  | packet => rfl
  | connector => rfl
  | backward => exact False.elim (hn (he ▸ hi))

def slotWord {L : ℕ} (P : Finset (Fin L)) : List Kind :=
  List.ofFn (fun i => if i ∈ P then .packet else .connector)

theorem slotWord_schedule {L : ℕ} (P : Finset (Fin L)) :
    Schedule P.card (L-P.card) 0 (slotWord P) := by
  have hf : (slotWord P).count .packet = P.card := by
    rw [slotWord, count_ofFn_slots]
    congr 1
    ext i
    simp
  have hb : (slotWord P).count .backward = 0 := by
    rw [slotWord, count_ofFn_sum]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> simp_all
  have hs := schedule_counts (slotWord P)
  have hl := hs.length
  have ho : (slotWord P).count .connector = L-P.card := by
    rw [hf, hb] at hl
    have hlen : (slotWord P).length = L := by simp [slotWord]
    rw [hlen] at hl
    omega
  simpa [hf, hb, ho] using hs

theorem slotWord_map {m L : ℕ} (g base wrap : ℕ) (P : Finset (Fin L)) :
    (slotWord P).map (clock m g base wrap).move = forwardPlan m L g P := by
  rw [slotWord, List.map_ofFn]
  unfold forwardPlan
  apply congrArg List.ofFn
  funext i
  by_cases hi : i ∈ P <;> simp [hi, Model.move, clock]

/-- The previous closed bound is exactly the b=0 boundary of Bellman's value. -/
theorem optimum_zero_backward {m : ℕ} [NeZero m] (g base wrap f o : ℕ) (j : ZMod m) :
    optimum (clock m g base wrap) f o 0 j =
      lowerBound (f+o) f (wrapCount m (f+o) j.val) g := by
  apply Nat.le_antisymm
  · obtain ⟨P, hp, hc⟩ := exists_optimal_forward_order m (f+o) g f j (by omega)
    have hs := slotWord_schedule P
    rw [hp, show f+o-f = o by omega] at hs
    have hl := optimum_le_every_word (clock m g base wrap) hs j
    unfold wordCost at hl
    rw [slotWord_map, hc, wrapSlots_card] at hl
    exact hl
  · obtain ⟨xs, hs, hc⟩ := optimum_attained (clock m g base wrap) f o 0 j
    have hlen : xs.length = f+o := by simpa using hs.length
    have hf : (packetSlots xs).card = f := by rw [packetSlots_card, hs.counts.1]
    have hm := zero_backward_map (m := m) g base wrap xs hs.counts.2.2
    have hl := closed_lowerBound xs.length g (packetSlots xs) j
    rw [← hm] at hl
    change lowerBound xs.length (packetSlots xs).card _ g ≤ wordCost _ xs j at hl
    simpa [hlen, hf, hc] using hl

end Coeff2.Charlieplex.ClockBellman
