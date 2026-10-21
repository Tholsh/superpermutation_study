import Coeff2.CharlieRestrictedCircleAssembly
import SuperpermutationUpperBound.Assembly.RowMacroFamily
import SuperpermutationUpperBound.Foundation.SupportedWords

/-! Pantone's literal row constructor with a restricted endpoint vocabulary.
The row and occurrence definitions and their proofs are upstream Apache-2.0.
This closes the construction step, not just an arithmetic implication. -/
namespace Coeff2.Charlieplex.RestrictedCircleAssembly
open SuperpermutationUpperBound
open ConnectorFamily

variable {I C α : Type} [Fintype I] [Fintype C] [DecidableEq α] {h ell : Nat}

theorem exists_restricted_word (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (hell : ell ≤ h)
    (hr : ∀ i, rows i ≠ [] ∧ ∃ v, EdgePath MacroEdge.source MacroEdge.target v (rows i) v)
    (hcover : ∀ i, ∃ c, ∃ edge ∈ rows i, ∃ j, j < h ∧ edge.source = rot (circle c) j)
    (A : Finset α) (hnd : ∀ c, (circle c).Nodup)
    (hA : ∀ c, ∀ a ∈ circle c, a ∈ A)
    (R : List α → Prop)
    (hrp : ∀ c j, R ((rot (circle c) j).take ell))
    (hrt : ∀ c j, R ((rot (circle c) j).drop (h - ell)))
    (P : α → Prop)
    (hrows : ∀ i edge, edge ∈ rows i → ∀ a ∈ edge.word, P a)
    (hcircles : ∀ c, ∀ a ∈ circle c, P a) :
    ∃ t J : Nat, ∃ w : List α,
      t ≤ Fintype.card C ∧ J ≤ min t (admissibleCount A ell R) ∧
      w.length = (∑ i, ((rows i).map MacroEdge.cost).sum) + h * Fintype.card C +
        (h - 1) * t - ell * (t - J) ∧
      (∀ i edge, edge ∈ rows i → edge.word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  let cycles := (Finset.univ.toList : List (I ⊕ C)).map (cycle rows circle hlen hh)
  have hc : ClosedCycles (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target) cycles := by
    intro es hes
    obtain ⟨tag, _, rfl⟩ := List.mem_map.mp hes
    exact cycles_closed rows circle hlen hh hr tag
  have hi : cycles.flatten.Perm Finset.univ.toList := by
    simpa only [cycles, List.flatMap_def] using cycles_inventory rows circle hlen hh
  have hcut : ∀ c j, j < h → (payload rows circle hlen hh (cut rows circle hlen hh c j)).cost = 1 ∧
      (payload rows circle hlen hh (cut rows circle hlen hh c j)).source = rot (circle c) j ∧
      (payload rows circle hlen hh (cut rows circle hlen hh c j)).target = rot (circle c) (j + 1) := by
    intro c j hj
    simp [cut_eq _ _ _ _ _ _ hj]
  have hconn : ∀ c j, j < h → EdgeConnected
      (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target)
      (cut rows circle hlen hh c 0) (cut rows circle hlen hh c j) := by
    intro c j hj
    rw [cut_eq _ _ _ _ _ _ hh, cut_eq _ _ _ _ _ _ hj]
    exact circle_connected rows circle hlen hh c 0 j hh hj
  have hcov : ∀ e, ∃ c, EdgeConnected (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target) e (cut rows circle hlen hh c 0) := by
    intro e
    simpa only [cut_eq _ _ _ _ _ _ hh] using cover_connected rows circle hlen hh hr hcover e
  obtain ⟨modules, J, w, _, hmod, hJ, hw, hkeep, hs⟩ :=
    balanced_restricted_circle_words (payload rows circle hlen hh) cycles circle
      (cut rows circle hlen hh) Required P A R hh hell hc hi hlen hnd hA hrp hrt
      hcut hconn hcov (fun e he c j _ => required_ne_cut rows circle hlen hh e he c j)
      (payload_support rows circle hlen hh P hrows hcircles)
  refine ⟨modules.length, J, w, hmod, hJ, ?_, ?_, hs⟩
  · rw [payload_cost_list_sum] at hw
    exact hw
  · intro i edge he
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp he
    have hhkeep := hkeep (rowLabel rows circle hlen hh i ⟨j,hj⟩) (by simp [Required, rowLabel])
    simpa only [rowLabel_payload, hje] using hhkeep

theorem exists_restricted_word_of_circle_rows {K ell : Nat}
    (rows : I → List (Row Nat)) (circles : List (List Nat))
    (hK : 4 ≤ K) (hell : ell ≤ K - 3)
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K)
    (hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible)
    (hclosed : ∀ i, ClosedTrail (rows i))
    (hc : CircleTransport.CircleFamilyValid (K - 3) circles)
    (hcover : CircleTransport.CoversDesignated circles (fun i => CircleTransport.HeadVertex (rows i)))
    (A : Finset Nat) (hA : ∀ c ∈ circles, ∀ a ∈ c, a ∈ A)
    (R : List Nat → Prop)
    (hrp : ∀ c ∈ circles, ∀ j, R ((rot c j).take ell))
    (hrt : ∀ c ∈ circles, ∀ j, R ((rot c j).drop (K - 3 - ell)))
    (hcs : ∀ c ∈ circles, ∀ a ∈ c, a < K)
    (hs : ∀ i r, r ∈ rows i → ∀ a ∈ r.word, a < K)
    (hperms : ∀ p : List Nat, p.Perm (List.range K) → ∃ i, ∃ r ∈ rows i, r.Assigned p) :
    ∃ t J : Nat, ∃ w : Word K, IsSuperpermutation w ∧
      t ≤ circles.length ∧ J ≤ min t (admissibleCount A ell R) ∧
      w.length = (K + 1) *
        (((Finset.univ.toList : List I).flatMap rows).map Row.visible).sum +
        ((Finset.univ.toList : List I).flatMap rows).length + (K - 3) * circles.length +
        (K - 4) * t - ell * (t - J) := by
  classical
  let edges := RowMacroFamily.edges rows hlen
  let circle : Fin circles.length → List Nat := fun c => circles[c.val]
  have hclen : ∀ c, (circle c).length = K - 3 := fun c => (hc _ (List.getElem_mem c.isLt)).1
  obtain ⟨t, J, w, ht, hJ, hw, hrows, hsupport⟩ := exists_restricted_word
    edges circle hclen (by omega) hell (RowMacroFamily.edges_closed rows hlen hK hclosed hv)
    (RowMacroFamily.edges_cover rows hlen circles hc hcover) A
    (fun c => (hc _ (List.getElem_mem c.isLt)).2)
    (fun c => hA _ (List.getElem_mem c.isLt)) R
    (fun c => hrp _ (List.getElem_mem c.isLt)) (fun c => hrt _ (List.getElem_mem c.isLt))
    (fun a => a < K) (RowMacroFamily.edges_support rows hlen _ hs)
    (fun c => hcs _ (List.getElem_mem c.isLt))
  have hcost : (∑ i, ((edges i).map MacroEdge.cost).sum) =
      (K + 1) * (((Finset.univ.toList : List I).flatMap rows).map Row.visible).sum +
        ((Finset.univ.toList : List I).flatMap rows).length := by
    simp_rw [show ∀ i, ((edges i).map MacroEdge.cost).sum =
      (K + 1) * ((rows i).map Row.visible).sum + (rows i).length from
        RowMacroFamily.edges_cost rows hlen hK hv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, finite_family_cost_sum, finite_family_length_sum]
  have hperm : CoversPermutationsOf (List.range K) w := by
    intro p hp
    obtain ⟨i, r, hr, ha⟩ := hperms p hp
    obtain ⟨edge, he, hword⟩ := RowMacroFamily.edges_word_mem rows hlen i r hr
    exact (r.assigned_infix_word ha).trans (hword ▸ hrows i edge he)
  refine ⟨t, J, liftWord w hsupport, isSuperpermutation_liftWord_of_covers w hsupport hperm,
    by simpa using ht, hJ, ?_⟩
  rw [liftWord_length]
  rw [hcost, Fintype.card_fin] at hw
  simpa only [show K - 3 - 1 = K - 4 by omega] using hw

#print axioms exists_restricted_word
#print axioms exists_restricted_word_of_circle_rows
end Coeff2.Charlieplex.RestrictedCircleAssembly
