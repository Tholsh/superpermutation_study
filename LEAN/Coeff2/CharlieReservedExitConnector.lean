import Coeff2.CharlieTopologyFlowDual
import Coeff2.CharlieLiteralAttachmentCut

/-!
Exact last-exit connector for arbitrary finite, directed, labelled multigraphs.
The graph may be the COMPLETE literal-symbol automaton, with dirty windows and
repeated permutation hits. Nothing in this theorem assumes atomic courses.

At each nonterminal vertex, reserve one copy of its rooted-tree exit until
the other outgoing copies have been used. A balanced remainder cannot strand
any edges. Together with endpoint balance this proves that a stopped greedy
traversal has consumed the whole prescribed ledger. It does NOT choose a cheap
ledger or prove that optimization over all possible trees is tractable.

The BEST/matrix-tree enumeration formula in the accompanying native diagnostic
is externally sourced and empirically checked, not formalized by this module.
-/
namespace Coeff2.Charlieplex.ReservedExitConnector

open scoped BigOperators
variable {V E : Type*} [Fintype E] [DecidableEq V]

def outgoing (src : E → V) (x : E → ℕ) (v : V) : ℕ :=
  ∑ e, if src e = v then x e else 0

def incoming (dst : E → V) (x : E → ℕ) (v : V) : ℕ :=
  ∑ e, if dst e = v then x e else 0

theorem edge_le_outgoing (src : E → V) (x : E → ℕ) (e : E) :
    x e ≤ outgoing src x (src e) := by
  classical
  have hh := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset E)) =>
      Nat.zero_le (if src i = src e then x i else 0)) (Finset.mem_univ e)
  simpa [outgoing] using hh

theorem edge_le_incoming (dst : E → V) (x : E → ℕ) (e : E) :
    x e ≤ incoming dst x (dst e) := edge_le_outgoing dst x e

/-- All residual edges disappear at a stopped terminal, provided the actual
remaining rooted exit is reserved at every active nonterminal vertex. -/
theorem balanced_reserved_no_stranding
    (src dst : E → V) (x : E → ℕ) (terminal : V)
    (parent : V → V) (depth : V → ℕ)
    (descending : ∀ v, v ≠ terminal → depth (parent v) < depth v)
    (reserved : ∀ v, v ≠ terminal → 0 < outgoing src x v →
      ∃ e, src e = v ∧ dst e = parent v ∧ 0 < x e)
    (balanced : ∀ v, outgoing src x v = incoming dst x v)
    (halted : outgoing src x terminal = 0) : ∀ e, x e = 0 := by
  have noOut : ∀ k v, depth v = k → outgoing src x v = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      by_cases ht : v = terminal
      · simpa only [ht] using halted
      · by_contra hn
        have hp : 0 < outgoing src x v := Nat.pos_of_ne_zero hn
        obtain ⟨e, _, he, hx⟩ := reserved v ht hp
        have hi : 0 < incoming dst x (parent v) := by
          have hh := edge_le_incoming dst x e
          rw [he] at hh
          omega
        have hz := ih (depth (parent v)) (by rw [← hv]; exact descending v ht)
          (parent v) rfl
        have hb := balanced (parent v)
        omega
  intro e
  have hz := noOut (depth (src e)) (src e) rfl
  have hh := edge_le_outgoing src x e
  omega

/-- This is the OPEN-trail endpoint condition; a circuit is also permitted.
If the current vertex is stuck, balance forces it to be the terminal. The
reserved exit theorem then rules out a premature stop with an unseen edge. -/
theorem stopped_ledger_empty
    (src dst : E → V) (x : E → ℕ) (current terminal : V)
    (parent : V → V) (depth : V → ℕ)
    (descending : ∀ v, v ≠ terminal → depth (parent v) < depth v)
    (reserved : ∀ v, v ≠ terminal → 0 < outgoing src x v →
      ∃ e, src e = v ∧ dst e = parent v ∧ 0 < x e)
    (balance : ∀ v,
      (outgoing src x v : ℤ) - incoming dst x v =
        (if v = current then 1 else 0) - (if v = terminal then 1 else 0))
    (halted : outgoing src x current = 0) :
    current = terminal ∧ ∀ e, x e = 0 := by
  have ht : current = terminal := by
    by_contra hn
    have hb := balance current
    simp [halted, hn] at hb
    omega
  refine ⟨ht, ?_⟩
  apply balanced_reserved_no_stranding src dst x terminal parent depth descending reserved
  · intro v
    have hb := balance v
    rw [ht] at hb
    omega
  · simpa only [ht] using halted

/-- Any prescribed transition multiset has one exact occupation set. Ordering
still matters for whether it is a walk, but not for the union of its emissions.
This is the algebraic replacement of the chronological occupation mask. -/
def emitted {P : Type*} [DecidableEq P] [DecidableEq E] (hits : E → Finset P)
    (route : List E) : Finset P := route.toFinset.biUnion hits

theorem emitted_of_permutation {P : Type*} [DecidableEq P] [DecidableEq E]
    (hits : E → Finset P) {route reassembled : List E}
    (same : route.Perm reassembled) : emitted hits route = emitted hits reassembled := by
  unfold emitted
  have hh : route.toFinset = reassembled.toFinset := by
    ext e
    simp only [List.mem_toFinset]
    exact same.mem_iff
  rw [hh]

section TreeFloor
variable [DecidableEq E] {I : Type*} [Fintype I] [DecidableEq I]

/-- One omitted required edge from each labelled required circuit bounds how
many required edges a connecting tree can use. In the literal permutation
graph these circuits are R orbits; the acyclic tree supplies the omission.
The tree cardinality and circuit omissions remain explicit inputs here. -/
theorem dirty_tree_floor (required tree : Finset E) (circuit : E → I)
    (dirtyVertices : ℕ)
    (omission : ∀ i, ∃ e ∈ required, e ∉ tree ∧ circuit e = i)
    (treeSize : tree.card + 1 = required.card + dirtyVertices) :
    Fintype.card I + dirtyVertices ≤ (tree \ required).card + 1 := by
  classical
  have full : (required \ tree).image circuit = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    obtain ⟨e, hr, ht, he⟩ := omission i
    exact Finset.mem_image.mpr ⟨e, Finset.mem_sdiff.mpr ⟨hr, ht⟩, he⟩
  have missing : Fintype.card I ≤ (required \ tree).card := by
    have hh := Finset.card_image_le (s := required \ tree) (f := circuit)
    simpa [full] using hh
  have hr := Finset.card_sdiff_add_card_inter required tree
  have ht := Finset.card_sdiff_add_card_inter tree required
  rw [Finset.inter_comm tree required] at ht
  omega

/-- The floor is on actual edge traversals, not the number of decisions in a
heuristic. Multiple copies can only increase this bound. Optional vertices
are NOT free: they consume the same finite excess budget as extra routing. -/
theorem tree_ledger_floor (required tree : Finset E) (circuit : E → I)
    (dirtyVertices : ℕ) (x : E → ℕ)
    (omission : ∀ i, ∃ e ∈ required, e ∉ tree ∧ circuit e = i)
    (treeSize : tree.card + 1 = required.card + dirtyVertices)
    (used : ∀ e ∈ required ∪ tree, 1 ≤ x e) :
    required.card + Fintype.card I + dirtyVertices ≤ (∑ e, x e) + 1 := by
  classical
  have hf := dirty_tree_floor required tree circuit dirtyVertices omission treeSize
  have part : (required ∪ tree).card ≤ ∑ e ∈ required ∪ tree, x e := by
    calc
      _ = ∑ _e ∈ required ∪ tree, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum used
  have whole : (∑ e ∈ required ∪ tree, x e) ≤ ∑ e, x e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro e _ _
    exact Nat.zero_le _
  have hu := Finset.card_sdiff_add_card tree required
  rw [Finset.union_comm tree required] at hu
  omega

/-- An exact, nonnegative excess decomposition, not just a lower bound.
The two differences are well-defined Nat surpluses because the tree floor
and the actual traversal lower bounds have both been proved above.

For a normalized literal word add its initial n-1 symbols. Its length then
equals n!+(n-1)!+n-2 plus dirty vertices, tree defect, and residual copies.
The literal R-orbit extraction supplies the explicit cardinality premises;
this declaration does not assert that choosing those surpluses is easy. -/
theorem exact_tree_excess (required tree : Finset E) (circuit : E → I)
    (dirtyVertices : ℕ) (x : E → ℕ)
    (omission : ∀ i, ∃ e ∈ required, e ∉ tree ∧ circuit e = i)
    (treeSize : tree.card + 1 = required.card + dirtyVertices)
    (used : ∀ e ∈ required ∪ tree, 1 ≤ x e) :
    (∑ e, x e) + 1 = required.card + Fintype.card I + dirtyVertices +
      ((tree \ required).card + 1 - (Fintype.card I + dirtyVertices)) +
      ((∑ e, x e) - (required ∪ tree).card) := by
  classical
  have hf := dirty_tree_floor required tree circuit dirtyVertices omission treeSize
  have part : (required ∪ tree).card ≤ ∑ e ∈ required ∪ tree, x e := by
    calc
      _ = ∑ _e ∈ required ∪ tree, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum used
  have whole : (∑ e ∈ required ∪ tree, x e) ≤ ∑ e, x e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro e _ _
    exact Nat.zero_le _
  have hu := Finset.card_sdiff_add_card tree required
  rw [Finset.union_comm tree required] at hu
  omega
end TreeFloor

end Coeff2.Charlieplex.ReservedExitConnector

#print axioms Coeff2.Charlieplex.ReservedExitConnector.balanced_reserved_no_stranding
#print axioms Coeff2.Charlieplex.ReservedExitConnector.stopped_ledger_empty
#print axioms Coeff2.Charlieplex.ReservedExitConnector.emitted_of_permutation
#print axioms Coeff2.Charlieplex.ReservedExitConnector.dirty_tree_floor
#print axioms Coeff2.Charlieplex.ReservedExitConnector.tree_ledger_floor
#print axioms Coeff2.Charlieplex.ReservedExitConnector.exact_tree_excess
