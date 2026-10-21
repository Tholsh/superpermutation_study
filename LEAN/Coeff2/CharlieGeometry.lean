/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.Charlieplex

/-!
# Geometry of Charlieplex ride coordinates

This file supplies the explicit geometric bridge omitted from the cardinality
argument in `Coeff2.Charlieplex`.

* Ride coordinates `(h,q)` are explicitly equivalent to directed channels on
  the cyclic phase set.
* An injection of pin sets induces an injection of directed channel spaces.
* Initial pin segments therefore give nested directed complete graphs
  `K₂ → K₄ → K₈` with 2, 12, and 56 channels.
* Channel reversal is a fixed-point-free involution and respects every pin
  embedding.

No assertion is made here that the observed corpus fragments already carry
these labels; that is a separate data-to-geometry bridge.
-/

namespace Coeff2

namespace Charlieplex

/-! ## Explicit inverse to the cyclic ride map -/

/-- Recover the orbit index and source phase from a nonzero cyclic
displacement. -/
def cyclicDifferenceToRide {m : ℕ} (hm : 2 ≤ m)
    (c : CyclicDifferenceCoord m) : RideCoord m := by
  letI : NeZero m := ⟨by omega⟩
  have hnonzero : c.2.1.val ≠ 0 := (ZMod.val_ne_zero c.2.1).mpr c.2.2
  exact
    (⟨c.2.1.val - 1, by have := c.2.1.val_lt; omega⟩,
      ⟨c.1.val, c.1.val_lt⟩)

theorem cyclicDifferenceToRide_leftInverse {m : ℕ} (hm : 2 ≤ m)
    (c : RideCoord m) :
    cyclicDifferenceToRide hm (rideToCyclicDifference hm c) = c := by
  rcases c with ⟨h, q⟩
  apply Prod.ext
  · apply Fin.ext
    change (((h.val + 1 : ℕ) : ZMod m).val - 1) = h.val
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega
  · apply Fin.ext
    simp [cyclicDifferenceToRide, rideToCyclicDifference,
      Nat.mod_eq_of_lt q.isLt]

theorem cyclicDifferenceToRide_rightInverse {m : ℕ} (hm : 2 ≤ m)
    (c : CyclicDifferenceCoord m) :
    rideToCyclicDifference hm (cyclicDifferenceToRide hm c) = c := by
  letI : NeZero m := ⟨by omega⟩
  rcases c with ⟨source, ⟨displacement, hdisplacement⟩⟩
  apply Sigma.ext
  · exact ZMod.natCast_zmod_val source
  · apply heq_of_eq
    apply Subtype.ext
    simp only [cyclicDifferenceToRide, rideToCyclicDifference]
    have hnonzero : displacement.val ≠ 0 :=
      (ZMod.val_ne_zero displacement).mpr hdisplacement
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnonzero)]
    exact ZMod.natCast_zmod_val displacement

/-- The geometric ride dictionary is an explicit equivalence, not merely an
equivalence chosen from equal cardinalities. -/
def rideEquivCyclicDifference {m : ℕ} (hm : 2 ≤ m) :
    RideCoord m ≃ CyclicDifferenceCoord m where
  toFun := rideToCyclicDifference hm
  invFun := cyclicDifferenceToRide hm
  left_inv := cyclicDifferenceToRide_leftInverse hm
  right_inv := cyclicDifferenceToRide_rightInverse hm

/-- Compose the explicit difference dictionary with `(source,d) ↦
(source,source+d)`. -/
def rideEquivCyclicChannel {m : ℕ} (hm : 2 ≤ m) :
    RideCoord m ≃ CyclicChannel m :=
  (rideEquivCyclicDifference hm).trans (cyclicDifferenceEquivChannel m)

@[simp]
theorem rideEquivCyclicChannel_apply {m : ℕ} (hm : 2 ≤ m)
    (c : RideCoord m) :
    rideEquivCyclicChannel hm c = rideToCyclicChannel hm c := rfl

theorem rideToCyclicChannel_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (rideToCyclicChannel hm) := by
  change Function.Injective (rideEquivCyclicChannel hm)
  exact (rideEquivCyclicChannel hm).injective

theorem rideToCyclicChannel_surjective {m : ℕ} (hm : 2 ≤ m) :
    Function.Surjective (rideToCyclicChannel hm) := by
  change Function.Surjective (rideEquivCyclicChannel hm)
  exact (rideEquivCyclicChannel hm).surjective

theorem existsUnique_ride_for_cyclicChannel {m : ℕ} (hm : 2 ≤ m)
    (channel : CyclicChannel m) :
    ∃! c : RideCoord m, rideToCyclicChannel hm c = channel := by
  rcases rideToCyclicChannel_surjective hm channel with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact rideToCyclicChannel_injective hm (hd.trans hc.symm)

/-! ## Directed-channel embeddings -/

/-- An injection of pins induces a map of directed channels. -/
def mapDirectedChannel {k m : ℕ} (f : Fin k ↪ Fin m)
    (c : DirectedChannel k) : DirectedChannel m :=
  ⟨f c.1, ⟨f c.2.1, fun h => c.2.2 (f.injective h)⟩⟩

theorem mapDirectedChannel_injective {k m : ℕ} (f : Fin k ↪ Fin m) :
    Function.Injective (mapDirectedChannel f) := by
  intro a b hab
  rcases a with ⟨asource, ⟨asink, ha⟩⟩
  rcases b with ⟨bsource, ⟨bsink, hb⟩⟩
  have hsource : asource = bsource := f.injective (congrArg Sigma.fst hab)
  have hsink : asink = bsink :=
    f.injective (congrArg (fun c : DirectedChannel m => c.2.1) hab)
  subst bsource
  subst bsink
  rfl

/-- Reversing a channel commutes with every injection of pin sets. -/
theorem reverseChannel_mapDirectedChannel {k m : ℕ} (f : Fin k ↪ Fin m)
    (c : DirectedChannel k) :
    reverseChannel (mapDirectedChannel f c) =
      mapDirectedChannel f (reverseChannel c) := by
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  rfl

/-- Channel reversal is an involution. -/
@[simp]
theorem reverseChannel_involutive {A : Type*} (c : Channel A) :
    reverseChannel (reverseChannel c) = c := by
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  rfl

/-- A directed non-loop channel is never fixed by orientation reversal. -/
theorem reverseChannel_ne_self {A : Type*} (c : Channel A) :
    reverseChannel c ≠ c := by
  intro h
  exact c.2.2 (congrArg Sigma.fst h)

/-- Embed an initial segment of `k` pins into `m` pins. -/
def initialPinEmbedding {k m : ℕ} (hkm : k ≤ m) : Fin k ↪ Fin m where
  toFun i := ⟨i.1, i.2.trans_le hkm⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun i : Fin m => i.val) hab

/-- The directed complete graph on the first `k` pins, embedded in `m` pins. -/
noncomputable def initialChannelGeometry (k m : ℕ) (hkm : k ≤ m) :
    Finset (DirectedChannel m) :=
  Finset.univ.image (mapDirectedChannel (initialPinEmbedding hkm))

theorem card_initialChannelGeometry (k m : ℕ) (hkm : k ≤ m) :
    (initialChannelGeometry k m hkm).card = k * (k - 1) := by
  classical
  rw [initialChannelGeometry,
    Finset.card_image_of_injective _
      (mapDirectedChannel_injective (initialPinEmbedding hkm)),
    Finset.card_univ, card_directedChannel]

/-- Initial-segment channel geometries are nested with their pin sets. -/
theorem initialChannelGeometry_mono {j k m : ℕ}
    (hjk : j ≤ k) (hkm : k ≤ m) :
    initialChannelGeometry j m (hjk.trans hkm) ⊆
      initialChannelGeometry k m hkm := by
  classical
  intro channel hchannel
  rw [initialChannelGeometry, Finset.mem_image] at hchannel ⊢
  rcases hchannel with ⟨small, _, rfl⟩
  refine ⟨mapDirectedChannel (initialPinEmbedding hjk) small,
    Finset.mem_univ _, ?_⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  rfl

/-- Every embedded directed geometry is closed under channel reversal. -/
theorem reverse_mem_initialChannelGeometry {k m : ℕ} (hkm : k ≤ m)
    {channel : DirectedChannel m}
    (hchannel : channel ∈ initialChannelGeometry k m hkm) :
    reverseChannel channel ∈ initialChannelGeometry k m hkm := by
  classical
  rw [initialChannelGeometry, Finset.mem_image] at hchannel ⊢
  rcases hchannel with ⟨small, _, rfl⟩
  refine ⟨reverseChannel small, Finset.mem_univ _, ?_⟩
  exact (reverseChannel_mapDirectedChannel (initialPinEmbedding hkm) small).symm

/-- The concrete nested geometry suggested by the 5905 multiplicities. -/
theorem charlie_two_four_eight_geometry :
    (initialChannelGeometry 2 8 (by omega)).card = 2 ∧
    (initialChannelGeometry 4 8 (by omega)).card = 12 ∧
    (initialChannelGeometry 8 8 (by omega)).card = 56 ∧
    initialChannelGeometry 2 8 (by omega) ⊆
      initialChannelGeometry 4 8 (by omega) ∧
    initialChannelGeometry 4 8 (by omega) ⊆
      initialChannelGeometry 8 8 (by omega) := by
  constructor
  · simpa using card_initialChannelGeometry 2 8 (by omega)
  constructor
  · simpa using card_initialChannelGeometry 4 8 (by omega)
  constructor
  · simpa using card_initialChannelGeometry 8 8 (by omega)
  constructor
  · exact initialChannelGeometry_mono (m := 8) (by omega) (by omega)
  · exact initialChannelGeometry_mono (m := 8) (by omega) (by omega)

end Charlieplex

end Coeff2
