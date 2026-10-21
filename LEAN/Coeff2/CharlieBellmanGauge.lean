import Coeff2.CharlieBellmanExactQuotient
import Coeff2.CharlieLiteralGaugeRigidity
import Coeff2.CharlieLiteralRelabelProblem

/-! A genuine gauge of the literal Bellman problem: a single alphabet
permutation acts on the boundary, ALL occupied windows, and the continuation.
No boundary-only phase quotient or unproved independent clock gauge occurs.
-/
namespace Coeff2.Charlieplex.BellmanGauge
open LiteralReservoir BellmanExactQuotient

def AlphabetGauge (n : ℕ) (e : ℕ ≃ ℕ) : Prop :=
  ∀ a, (1 ≤ e a ∧ e a ≤ n) ↔ (1 ≤ a ∧ a ≤ n)

theorem inverse_gauge {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e) :
    AlphabetGauge n e.symm := by
  intro a
  simpa using (he (e.symm a)).symm

def wordEquiv (e : ℕ ≃ ℕ) : List ℕ ≃ List ℕ where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv w := by simp [List.map_map, Function.comp_def]
  right_inv w := by simp [List.map_map, Function.comp_def]

theorem gauge_interval {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e) :
    (Finset.Icc 1 n).image e = Finset.Icc 1 n := by
  ext a
  constructor
  · rintro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr ((he b).mpr (Finset.mem_Icc.mp hb))
  · intro ha
    refine Finset.mem_image.mpr ⟨e.symm a, ?_, by simp⟩
    exact Finset.mem_Icc.mpr ((inverse_gauge he a).mpr (Finset.mem_Icc.mp ha))

theorem perm_map_forward {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    {w : List ℕ} (hw : IsPermWord n w) : IsPermWord n (w.map e) := by
  refine ⟨hw.1.map e.injective, ?_⟩
  have hmap : (w.map e).toFinset = w.toFinset.image e := by
    ext a
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [hmap, hw.2, gauge_interval he]

theorem perm_map_iff {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e) (w : List ℕ) :
    IsPermWord n (w.map e) ↔ IsPermWord n w := by
  constructor
  · intro hw
    simpa [List.map_map, Function.comp_def] using perm_map_forward (inverse_gauge he) hw
  · exact perm_map_forward he

theorem permTest_map {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e) (w : List ℕ) :
    literalPermTest n (w.map e) = literalPermTest n w := by
  rw [Bool.eq_iff_iff, literalPermTest_eq_true, literalPermTest_eq_true, perm_map_iff he]

theorem alphabet_map {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e) (w : List ℕ) :
    literalAlphabetTest n (w.map e) = literalAlphabetTest n w := by
  rw [Bool.eq_iff_iff]
  simp only [literalAlphabetTest, List.all_eq_true, List.mem_map, decide_eq_true_eq]
  constructor
  · intro h a ha
    exact (he a).mp (h (e a) ⟨a, ha, rfl⟩)
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact (he b).mpr (h b hb)

def transport (e : ℕ ≃ ℕ) (s : LiteralSearchState) : LiteralSearchState where
  boundary := s.boundary.map e
  occupied := s.occupied.image (List.map e)
  length := s.length
  alphabetOK := s.alphabetOK
  noRepeat := s.noRepeat

theorem transport_inverse (e : ℕ ≃ ℕ) (s : LiteralSearchState) :
    transport e.symm (transport e s) = s := by
  apply LiteralSearchState.ext <;>
    simp [transport, List.map_map, Finset.image_image, Function.comp_def]

theorem mem_transport (e : ℕ ≃ ℕ) (s : LiteralSearchState) (w : List ℕ) :
    w.map e ∈ (transport e s).occupied ↔ w ∈ s.occupied := by
  change wordEquiv e w ∈ s.occupied.image (wordEquiv e) ↔ _
  constructor
  · intro hw
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hw
    have hvw := (wordEquiv e).injective heq
    simpa only [hvw] using hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

/-- Literal single-character transitions commute with the gauge, including
both occupation and repeat tracking. The action label must also be mapped. -/
theorem step_equivariant {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    (s : LiteralSearchState) (a : ℕ) :
    literalStateStep n (transport e s) (e a) = transport e (literalStateStep n s a) := by
  have hp := permTest_map he (s.boundary ++ [a])
  have hm := mem_transport e s (s.boundary ++ [a])
  simp only [List.map_append, List.map_singleton] at hp hm
  have hd : decide (1 ≤ e a ∧ e a ≤ n) = decide (1 ≤ a ∧ a ≤ n) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using he a)
  have hn : decide (s.boundary.map e ++ [e a] ∉ (transport e s).occupied) =
      decide (s.boundary ++ [a] ∉ s.occupied) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using not_congr hm)
  apply LiteralSearchState.ext
  · simp [literalStateStep, transport, lastSymbols, List.map_append]
  · change (if literalPermTest n (s.boundary.map e ++ [e a]) then
        insert (s.boundary.map e ++ [e a]) (s.occupied.image (List.map e))
      else s.occupied.image (List.map e)) = _
    rw [hp]
    split <;> simp [transport, literalStateStep, List.map_append, Finset.image_insert, *]
  · rfl
  · change (s.alphabetOK && decide (1 ≤ e a ∧ e a ≤ n)) = _
    rw [hd]
    rfl
  · change (s.noRepeat && (!literalPermTest n (s.boundary.map e ++ [e a]) ||
        decide (s.boundary.map e ++ [e a] ∉ (transport e s).occupied))) = _
    rw [hp, hn]
    rfl

theorem run_equivariant {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    (s : LiteralSearchState) (w : List ℕ) :
    literalStateRun n (transport e s) (w.map e) = transport e (literalStateRun n s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons, literalStateRun, step_equivariant he, ih]

theorem covered_transport {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    (s : LiteralSearchState) : covered n (transport e s) ↔ covered n s := by
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨ha, fun p hp => ?_⟩
    exact (mem_transport e s p).mp (hc (p.map e) (perm_map_forward he hp))
  · rintro ⟨ha, hc⟩
    refine ⟨ha, fun p hp => ?_⟩
    have hold := hc (p.map e.symm) (perm_map_forward (inverse_gauge he) hp)
    have hnew := (mem_transport e s (p.map e.symm)).mpr hold
    simpa [List.map_map, Function.comp_def] using hnew

/-- Exact Bellman feasibility in BOTH directions; witnesses map back using
the inverse gauge, at the same character length. -/
theorem bellman_gauge_iff {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    (h : ℕ) (s : LiteralSearchState) : canFinish n h (transport e s) ↔ canFinish n h s := by
  have forward : ∀ (f : ℕ ≃ ℕ), AlphabetGauge n f → ∀ t,
      canFinish n h t → canFinish n h (transport f t) := by
    intro f hf t ht
    obtain ⟨w, hw, hal, hc⟩ := (feasible_word n h t).mp ht
    apply (feasible_word n h (transport f t)).mpr
    refine ⟨w.map f, by simpa using hw, ?_, ?_⟩
    · rw [alphabet_map hf, hal]
    · rw [run_equivariant hf, covered_transport hf]
      exact hc
  constructor
  · intro ht
    simpa only [transport_inverse] using forward e.symm (inverse_gauge he) (transport e s) ht
  · exact forward e he s

theorem optimal_gauge_iff {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    (k : ℕ) (s : LiteralSearchState) : optimalAt n k (transport e s) ↔ optimalAt n k s := by
  simp only [optimalAt, bellman_gauge_iff he]

/-- Combine the exact gauge with coverage dominance. Both the boundary
and the WHOLE occupation cache must be transported before comparing. -/
theorem gauge_dominance {n : ℕ} {e : ℕ ≃ ℕ} (he : AlphabetGauge n e)
    (h : ℕ) (s t : LiteralSearchState)
    (hb : (transport e s).boundary = t.boundary)
    (ha : s.alphabetOK = t.alphabetOK)
    (hu : (transport e s).occupied ⊆ t.occupied) :
    canFinish n h s → canFinish n h t := by
  intro hs
  exact cache_dominance n h (transport e s) t hb ha hu ((bellman_gauge_iff he h s).mpr hs)

/-- Equality of two transported full states is a certified cache key.
The gauges may differ; each continuation is recovered in its own alphabet. -/
theorem gauge_key_sound {n : ℕ} {e f : ℕ ≃ ℕ}
    (he : AlphabetGauge n e) (hf : AlphabetGauge n f)
    (h : ℕ) (s t : LiteralSearchState) (key : transport e s = transport f t) :
    canFinish n h s ↔ canFinish n h t := by
  rw [← bellman_gauge_iff he h s, key, bellman_gauge_iff hf h t]

/-- Literal two-terminal repair decisions are also gauge invariant. This
is the exact local problem underlying the native canonical dictionary;
neither head, tail nor residual occupation may be omitted from the key. -/
theorem repair_budget_gauge (e : ℕ ≃ ℕ) (head tail : List ℕ)
    (required : List (List ℕ)) (budget : ℕ) :
    (∃ w : List ℕ, w.length ≤ budget ∧
      LiteralRelabelProblem.feasible (head.map e) (tail.map e)
        (required.map (List.map e)) w) ↔
    (∃ w : List ℕ, w.length ≤ budget ∧
      LiteralRelabelProblem.feasible head tail required w) := by
  constructor
  · rintro ⟨w, hw, hc⟩
    refine ⟨w.map e.symm, by simpa using hw, ?_⟩
    apply (LiteralRelabelProblem.feasible_relabel e head tail (w.map e.symm) required).mp
    simpa [List.map_map, Function.comp_def] using hc
  · rintro ⟨w, hw, hc⟩
    exact ⟨w.map e, by simpa using hw,
      (LiteralRelabelProblem.feasible_relabel e head tail w required).mpr hc⟩

/-- The native candidate language stitches literal targets. Every edge
overlap and every stitched witness commutes with the SAME alphabet map. -/
def repairOverlap (left right : List ℕ) : ℕ :=
  Nat.findGreatest (fun k => left.drop (left.length-k) = right.take k)
    (min left.length right.length)

def repairJoin (left right : List ℕ) : List ℕ :=
  left ++ right.drop (repairOverlap left right)

/-- Same maximal-overlap definition as CharlieSzekeresExchange. Kept here
without its optional Archive import so this bridge builds independently. -/
theorem repairOverlap_gauge (e : ℕ ≃ ℕ) (left right : List ℕ) :
    repairOverlap (left.map e) (right.map e) = repairOverlap left right := by
  have hpred : (fun k => (left.map e).drop (left.length-k) =
      (right.map e).take k) = (fun k => left.drop (left.length-k) = right.take k) := by
    funext k
    apply propext
    rw [← List.map_drop, ← List.map_take]
    exact e.injective.list_map.eq_iff
  simp only [repairOverlap, List.length_map]
  apply Nat.le_antisymm
  · exact Nat.findGreatest_mono_left (fun k hk => Eq.mp (congrFun hpred k) hk) _
  · exact Nat.findGreatest_mono_left (fun k hk => Eq.mpr (congrFun hpred k) hk) _

theorem repairJoin_gauge (e : ℕ ≃ ℕ) (left right : List ℕ) :
    (repairJoin left right).map e = repairJoin (left.map e) (right.map e) := by
  simp [repairJoin, repairOverlap_gauge, List.map_drop]

def assemble (head : List ℕ) : List (List ℕ) → List ℕ
  | [] => head
  | piece :: rest => assemble (repairJoin head piece) rest

theorem assemble_gauge (e : ℕ ≃ ℕ) (head : List ℕ) (pieces : List (List ℕ)) :
    assemble (head.map e) (pieces.map (List.map e)) = (assemble head pieces).map e := by
  induction pieces generalizing head with
  | nil => rfl
  | cons piece rest ih =>
    simp only [List.map_cons, assemble, ← repairJoin_gauge e, ih]

theorem assemble_cost_gauge (e : ℕ ≃ ℕ) (head : List ℕ) (pieces : List (List ℕ)) :
    (assemble (head.map e) (pieces.map (List.map e))).length = (assemble head pieces).length := by
  rw [assemble_gauge]
  simp

#print axioms inverse_gauge
#print axioms gauge_interval
#print axioms perm_map_iff
#print axioms alphabet_map
#print axioms transport_inverse
#print axioms step_equivariant
#print axioms run_equivariant
#print axioms covered_transport
#print axioms bellman_gauge_iff
#print axioms optimal_gauge_iff
#print axioms gauge_dominance
#print axioms gauge_key_sound
#print axioms repair_budget_gauge
#print axioms repairOverlap_gauge
#print axioms repairJoin_gauge
#print axioms assemble_gauge
#print axioms assemble_cost_gauge
end Coeff2.Charlieplex.BellmanGauge
