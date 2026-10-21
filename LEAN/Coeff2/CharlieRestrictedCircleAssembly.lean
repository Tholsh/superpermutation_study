import SuperpermutationUpperBound.Assembly.ConnectorFamily
import SuperpermutationUpperBound.BalancedCuts.CutWords
import Mathlib.Data.Fintype.CardEmbedding
import Coeff2.CharlieTransportVocabulary

/-!
# Literal restricted-endpoint assembly

This adapts Pantone's Apache-2.0 supported-state and circle assembly proofs.
Unlike the earlier generic saving lemma, it constructs the actual module
inventory from closed row occurrences before restricting its endpoints.
No claim about a new asymptotic coefficient or optimized record follows here.
-/
namespace Coeff2.Charlieplex.RestrictedCircleAssembly
open SuperpermutationUpperBound
open TransportVocabulary

variable {I E C α : Type} [Fintype I] [Fintype E] [Fintype C]
  [DecidableEq α] {h ell : Nat}

/- Keep this foundational type independent of SprintFamily's large finite
example certificates. It is literally the same ordered-list construction. -/
def Endpoint (A : Finset α) (ell : Nat) :=
  {v : List α // v.length = ell ∧ v.Nodup ∧ ∀ a ∈ v, a ∈ A}

def embeddingEndpoint (A : Finset α) (ell : Nat) (f : Fin ell ↪ A) : Endpoint A ell := by
  refine ⟨List.ofFn (fun i => (f i).val), List.length_ofFn, ?_, ?_⟩
  · apply List.nodup_ofFn_ofInjective
    intro i j hij
    exact f.injective (Subtype.ext hij)
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact (f i).property

omit [DecidableEq α] in
theorem embeddingEndpoint_bijective (A : Finset α) (ell : Nat) :
    Function.Bijective (embeddingEndpoint A ell) := by
  constructor
  · intro f g he
    have hv := List.ofFn_injective (congrArg Subtype.val he)
    apply DFunLike.ext
    intro i
    exact Subtype.ext (congrFun hv i)
  · rintro ⟨v,hv,hn,hs⟩
    subst ell
    let f : Fin v.length ↪ A :=
      ⟨fun i => ⟨v.get i, hs _ (List.get_mem v i)⟩,
        fun i j hij => hn.get_inj_iff.mp (congrArg Subtype.val hij)⟩
    exact ⟨f,Subtype.ext (List.ofFn_get v)⟩

noncomputable def endpointEquiv (A : Finset α) (ell : Nat) : Endpoint A ell ≃ (Fin ell ↪ A) :=
  (Equiv.ofBijective (embeddingEndpoint A ell) (embeddingEndpoint_bijective A ell)).symm

noncomputable instance (A : Finset α) (ell : Nat) : Fintype (Endpoint A ell) :=
  Fintype.ofEquiv (Fin ell ↪ A) (endpointEquiv A ell).symm

instance (A : Finset α) (ell : Nat) : DecidableEq (Endpoint A ell) :=
  inferInstanceAs (DecidableEq {v : List α // v.length = ell ∧ v.Nodup ∧ ∀ a ∈ v, a ∈ A})

omit [DecidableEq α] in
theorem endpoint_card (A : Finset α) (ell : Nat) :
    Fintype.card (Endpoint A ell) = A.card.descFactorial ell := by
  rw [Fintype.card_congr (endpointEquiv A ell)]
  simp only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]

omit [DecidableEq α] in
theorem take_short_of_take_eq {w u : List α} (he : w.take h = u) (hl : ell ≤ h) :
    w.take ell = u.take ell := by
  rw [← he,List.take_take,Nat.min_eq_left hl]

omit [DecidableEq α] in
theorem drop_short_of_drop_eq {w u : List α} (he : w.drop (w.length-h) = u)
    (hh : h ≤ w.length) (hl : ell ≤ h) :
    w.drop (w.length-ell) = u.drop (h-ell) := by
  rw [← he,List.drop_drop]
  congr 1
  omega

noncomputable def admissibleCount (A : Finset α) (ell : Nat)
    (R : List α → Prop) : Nat := by
  classical
  exact Fintype.card {v : Endpoint A ell // R v.val}

theorem balanced_restricted_cut_words [DecidableEq I]
    (words : I × Fin h → List α) (lengths : I → Nat)
    (A : Finset α) (R : List α → Prop)
    (hh : 0 < h) (hl : ∀ c, (words c).length = lengths c.1)
    (hell : ∀ i, ell ≤ lengths i)
    (hp : ∀ c, ((words c).take ell).Nodup ∧ ∀ a ∈ (words c).take ell, a ∈ A)
    (ht : ∀ c, ((words c).drop ((words c).length - ell)).Nodup ∧
      ∀ a ∈ (words c).drop ((words c).length - ell), a ∈ A)
    (hrp : ∀ c, R ((words c).take ell))
    (hrt : ∀ c, R ((words c).drop ((words c).length - ell)))
    (hbalance : ∀ i,
      ((List.finRange h).map (fun j => (words (i,j)).take ell)).Perm
        ((List.finRange h).map (fun j => (words (i,j)).drop ((words (i,j)).length - ell))))
    (P : α → Prop) (hsupport : ∀ c, ∀ a ∈ words c, P a) :
    ∃ selected : I → Fin h, ∃ J : Nat, ∃ w : List α,
      J ≤ min (Fintype.card I) (admissibleCount A ell R) ∧
      w.length = (∑ i, lengths i) - ell * (Fintype.card I - J) ∧
      (∀ i, (words (i, selected i)).IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  let V := {v : Endpoint A ell // R v.val}
  let source : I × Fin h → V := fun c => by
    refine ⟨⟨(words c).take ell, ⟨?_, hp c⟩⟩, hrp c⟩
    rw [List.length_take, hl]
    exact Nat.min_eq_left (hell c.1)
  let target : I × Fin h → V := fun c => by
    refine ⟨⟨(words c).drop ((words c).length - ell), ⟨?_, ht c⟩⟩, hrt c⟩
    rw [List.length_drop, Nat.sub_sub_self (by rw [hl]; exact hell c.1)]
  let vertexWord : V → List α := fun v => v.val.val
  have hinj : Function.Injective vertexWord := by
    intro v u he
    exact Subtype.ext (Subtype.ext he)
  have hb : ∀ i, ((List.finRange h).map (fun j => source (i,j))).Perm
      ((List.finRange h).map (fun j => target (i,j))) := by
    intro i
    apply (List.map_perm_map_iff hinj).mp
    simpa only [List.map_map, Function.comp_def, vertexWord, source, target] using hbalance i
  obtain ⟨selected, J, w, hJ, hw, hc, hs⟩ :=
    BalancedCuts.balanced_cut_words words lengths source target vertexWord hh hl hell
      (fun _ => rfl) (fun _ => rfl) hb P hsupport
  exact ⟨selected, J, w, hJ, hw, hc, hs⟩

/-- The module construction is exactly the literal one in Pantone's proof.
Only the finite type of admissible endpoint words is made smaller. -/
theorem balanced_restricted_circle_words (payload : E → MacroEdge α h)
    (cycles : List (List E)) (circle : C → List α) (cut : C → Nat → E)
    (required : E → Prop) (P : α → Prop) (A : Finset α)
    (R : List α → Prop)
    (hh : 0 < h) (hell : ell ≤ h)
    (hc : ClosedCycles (fun e => (payload e).source) (fun e => (payload e).target) cycles)
    (hi : cycles.flatten.Perm Finset.univ.toList)
    (hlen : ∀ c, (circle c).length = h)
    (hnd : ∀ c, (circle c).Nodup)
    (hA : ∀ c, ∀ a ∈ circle c, a ∈ A)
    (hrp : ∀ c j, R ((rot (circle c) j).take ell))
    (hrt : ∀ c j, R ((rot (circle c) j).drop (h - ell)))
    (hcut : ∀ c j, j < h → (payload (cut c j)).cost = 1 ∧
      (payload (cut c j)).source = rot (circle c) j ∧
      (payload (cut c j)).target = rot (circle c) (j + 1))
    (hconnected : ∀ c j, j < h → EdgeConnected
      (fun e => (payload e).source) (fun e => (payload e).target) (cut c 0) (cut c j))
    (hcover : ∀ e, ∃ c, EdgeConnected
      (fun e => (payload e).source) (fun e => (payload e).target) e (cut c 0))
    (hrequired : ∀ e, required e → ∀ c j, j < h → e ≠ cut c j)
    (hs : ∀ e, ∀ a ∈ (payload e).word, P a) :
    ∃ modules : List (List E), ∃ J : Nat, ∃ w : List α,
      modules.flatten.Perm Finset.univ.toList ∧
      modules.length ≤ Fintype.card C ∧
      J ≤ min modules.length (admissibleCount A ell R) ∧
      w.length = (Finset.univ.toList.map (fun e => (payload e).cost)).sum +
        (h - 1) * modules.length - ell * (modules.length - J) ∧
      (∀ e, required e → (payload e).word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  obtain ⟨modules, chosen, words, _hm, hmi, hmcount, hw, hbal, hmarker⟩ :=
    covered_circle_module_words payload cycles circle cut required P hh hc hi hlen
      hcut hconnected hcover hrequired hs
  let lengths : Fin modules.length → Nat :=
    fun i => (modules[i.val].map (fun e => (payload e).cost)).sum - 1 + h
  have hcost : ∀ i : Fin modules.length,
      1 ≤ (modules[i.val].map (fun e => (payload e).cost)).sum := by
    intro i
    exact cost_sum_pos_of_one _ (hmarker i) (hcut (chosen i) 0 hh).1
  have hwordlen : ∀ i j, j < h → (words i j).length = lengths i :=
    fun i j hj => (hw i j hj).1
  have hlong : ∀ i, h ≤ lengths i := by
    intro i
    simp only [lengths]
    omega
  have hprefix : ∀ c : Fin modules.length × Fin h,
      (words c.1 c.2.val).take ell = (rot (circle (chosen c.1)) (c.2.val + 1)).take ell :=
    fun c => take_short_of_take_eq (hw c.1 c.2.val c.2.isLt).2.1 hell
  have hsuffix : ∀ c : Fin modules.length × Fin h,
      (words c.1 c.2.val).drop ((words c.1 c.2.val).length - ell) =
        (rot (circle (chosen c.1)) c.2.val).drop (h - ell) := by
    intro c
    exact drop_short_of_drop_eq (hw c.1 c.2.val c.2.isLt).2.2.1
      (by rw [hwordlen _ _ c.2.isLt]; exact hlong c.1) hell
  have hp : ∀ c : Fin modules.length × Fin h,
      ((words c.1 c.2.val).take ell).Nodup ∧
        ∀ a ∈ (words c.1 c.2.val).take ell, a ∈ A := by
    intro c
    rw [hprefix]
    refine ⟨((rot_perm _ _).nodup_iff.mpr (hnd _)).take, ?_⟩
    intro a ha
    exact hA _ a ((rot_perm _ _).mem_iff.mp (List.mem_of_mem_take ha))
  have ht : ∀ c : Fin modules.length × Fin h,
      ((words c.1 c.2.val).drop ((words c.1 c.2.val).length - ell)).Nodup ∧
        ∀ a ∈ (words c.1 c.2.val).drop ((words c.1 c.2.val).length - ell), a ∈ A := by
    intro c
    rw [hsuffix]
    refine ⟨((rot_perm _ _).nodup_iff.mpr (hnd _)).drop, ?_⟩
    intro a ha
    exact hA _ a ((rot_perm _ _).mem_iff.mp (List.mem_of_mem_drop ha))
  have hb : ∀ i : Fin modules.length,
      ((List.finRange h).map (fun j => (words i j.val).take ell)).Perm
        ((List.finRange h).map (fun j => (words i j.val).drop ((words i j.val).length - ell))) := by
    intro i
    simpa only [← map_val_finRange h, List.map_map, Function.comp_def] using hbal i ell hell
  obtain ⟨selected, J, w, hJ, hwlen, hocc, hsupport⟩ := balanced_restricted_cut_words
    (fun c => words c.1 c.2.val) lengths A R hh (fun c => hwordlen _ _ c.2.isLt)
    (fun i => hell.trans (hlong i)) hp ht
    (fun c => by rw [hprefix]; exact hrp _ _)
    (fun c => by rw [hsuffix]; exact hrt _ _) hb P
    (fun c => (hw c.1 c.2.val c.2.isLt).2.2.2.2)
  have hsum := sum_cut_module_lengths modules (fun e => (payload e).cost) lengths h hh hcost
    (fun _ => rfl)
  have htotal := (hmi.map (fun e => (payload e).cost)).sum_eq
  refine ⟨modules, J, w, hmi, hmcount, by simpa using hJ, ?_, ?_, hsupport⟩
  · simpa only [Fintype.card_fin, hsum, htotal] using hwlen
  · intro e he
    obtain ⟨es, hes, hees⟩ := List.mem_flatten.mp (hmi.mem_iff.mpr (by simp : e ∈ Finset.univ.toList))
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hes
    let ix : Fin modules.length := ⟨i, hi⟩
    exact ((hw ix (selected ix).val (selected ix).isLt).2.2.2.1 e hees he).trans (hocc ix)

#print axioms balanced_restricted_cut_words
#print axioms balanced_restricted_circle_words
end Coeff2.Charlieplex.RestrictedCircleAssembly
