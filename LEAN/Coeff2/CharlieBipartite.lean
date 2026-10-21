/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.CharlieGeometry
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The Charlieplex crown graph

This file inserts an incidence layer between Charlieplex coordinates and a
future Cayley-graph model.  We use two copies of the phase set: the left copy
records the phase before an event and the right copy records the phase after
it.  A left phase is adjacent to every right phase except its own copy.

Thus the graph is the crown graph `K_{m,m}` with the diagonal perfect matching
removed.  Its canonically left-to-right oriented edges are exactly the
`m * (m - 1)` directed Charlie channels.
-/

namespace Coeff2

namespace Charlieplex

/-- Two copies of the phase set.  `inl` is the start shore and `inr` is the
end shore. -/
abbrev CrownVertex (m : ℕ) := Sum (Fin m) (Fin m)

/-- Crown adjacency: opposite shores and different phase labels. -/
def CrownAdj {m : ℕ} : CrownVertex m → CrownVertex m → Prop
  | .inl source, .inr sink => sink ≠ source
  | .inr sink, .inl source => sink ≠ source
  | _, _ => False

theorem crownAdj_symm {m : ℕ} : Std.Symm (@CrownAdj m) where
  symm u v huv := by
    cases u <;> cases v <;> simpa [CrownAdj] using huv

theorem crownAdj_irrefl {m : ℕ} : Std.Irrefl (@CrownAdj m) where
  irrefl v := by
    cases v <;> simp [CrownAdj]

instance crownAdjDecidable {m : ℕ} : DecidableRel (@CrownAdj m) := by
  intro u v
  cases u <;> cases v <;> simp only [CrownAdj] <;> infer_instance

/-- The Charlieplex crown graph at radix `m`. -/
def crownGraph (m : ℕ) : SimpleGraph (CrownVertex m) where
  Adj := CrownAdj
  symm := crownAdj_symm
  loopless := crownAdj_irrefl

instance crownGraphAdjDecidable (m : ℕ) : DecidableRel (crownGraph m).Adj :=
  crownAdjDecidable

@[simp]
theorem crownGraph_adj_left_right {m : ℕ} (source sink : Fin m) :
    (crownGraph m).Adj (.inl source) (.inr sink) ↔ sink ≠ source := by
  rfl

@[simp]
theorem crownGraph_adj_right_left {m : ℕ} (source sink : Fin m) :
    (crownGraph m).Adj (.inr sink) (.inl source) ↔ sink ≠ source := by
  rfl

@[simp]
theorem crownGraph_not_adj_left_left {m : ℕ} (a b : Fin m) :
    ¬(crownGraph m).Adj (.inl a) (.inl b) := by
  simp [crownGraph, CrownAdj]

@[simp]
theorem crownGraph_not_adj_right_right {m : ℕ} (a b : Fin m) :
    ¬(crownGraph m).Adj (.inr a) (.inr b) := by
  simp [crownGraph, CrownAdj]

/-- The removed diagonal consists of the forbidden same-phase transitions. -/
@[simp]
theorem crownGraph_not_adj_diagonal {m : ℕ} (phase : Fin m) :
    ¬(crownGraph m).Adj (.inl phase) (.inr phase) := by
  simp

/-- The two shores of the crown graph. -/
def crownLeft (m : ℕ) : Set (CrownVertex m) := {v | ∃ phase, v = .inl phase}

def crownRight (m : ℕ) : Set (CrownVertex m) := {v | ∃ phase, v = .inr phase}

/-- The crown graph really is bipartite in its start and end shores. -/
theorem crownGraph_isBipartiteWith (m : ℕ) :
    (crownGraph m).IsBipartiteWith (crownLeft m) (crownRight m) := by
  constructor
  · rw [Set.disjoint_left]
    intro v hvLeft hvRight
    rcases hvLeft with ⟨source, rfl⟩
    rcases hvRight with ⟨sink, h⟩
    cases h
  · intro u v huv
    cases u with
    | inl source =>
        cases v with
        | inl sink => simp at huv
        | inr sink =>
            left
            exact ⟨⟨source, rfl⟩, ⟨sink, rfl⟩⟩
    | inr sink =>
        cases v with
        | inl source =>
            right
            exact ⟨⟨sink, rfl⟩, ⟨source, rfl⟩⟩
        | inr source => simp at huv

/-! ## Canonically oriented crown edges -/

/-- Every undirected crown edge has a unique orientation from the left shore
to the right shore. -/
abbrev CrownEdge (m : ℕ) :=
  Σ source : Fin m,
    {sink : Fin m // (crownGraph m).Adj (.inl source) (.inr sink)}

/-- A directed Charlie channel is the same object as a canonically oriented
edge of the crown graph. -/
def channelEquivCrownEdge (m : ℕ) : DirectedChannel m ≃ CrownEdge m where
  toFun channel := ⟨channel.1, ⟨channel.2.1, channel.2.2⟩⟩
  invFun edge := ⟨edge.1, ⟨edge.2.1, edge.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_crownEdge (m : ℕ) :
    Fintype.card (CrownEdge m) = m * (m - 1) := by
  rw [← Fintype.card_congr (channelEquivCrownEdge m)]
  exact card_directedChannel m

/-- A concrete channel supplies an edge of the bipartite graph. -/
theorem channel_is_crown_edge {m : ℕ} (channel : DirectedChannel m) :
    (crownGraph m).Adj (.inl channel.1) (.inr channel.2.1) :=
  channel.2.2

/-- Conversely, every left-to-right adjacency supplies one and only one
directed channel. -/
theorem existsUnique_channel_for_crown_edge {m : ℕ}
    (source sink : Fin m)
    (h : (crownGraph m).Adj (.inl source) (.inr sink)) :
    ∃! channel : DirectedChannel m,
      channel.1 = source ∧ channel.2.1 = sink := by
  refine ⟨⟨source, ⟨sink, h⟩⟩, ⟨rfl, rfl⟩, ?_⟩
  intro channel hc
  rcases channel with ⟨channelSource, ⟨channelSink, hne⟩⟩
  simp only at hc
  rcases hc with ⟨rfl, rfl⟩
  rfl

/-! ## Shore exchange and channel reversal -/

/-- Exchange start and end shores without changing the phase label. -/
def swapCrownShore {m : ℕ} : CrownVertex m → CrownVertex m
  | .inl phase => .inr phase
  | .inr phase => .inl phase

@[simp]
theorem swapCrownShore_involutive {m : ℕ} (v : CrownVertex m) :
    swapCrownShore (swapCrownShore v) = v := by
  cases v <;> rfl

/-- Shore exchange is a symmetry of the crown graph. -/
theorem swapCrownShore_adj_iff {m : ℕ} (u v : CrownVertex m) :
    (crownGraph m).Adj (swapCrownShore u) (swapCrownShore v) ↔
      (crownGraph m).Adj u v := by
  cases u <;> cases v <;> simp [swapCrownShore, ne_comm]

/-- Reversing a Charlie channel exchanges its two endpoints and their shores. -/
theorem reverseChannel_crown_endpoints {m : ℕ} (channel : DirectedChannel m) :
    (.inl (reverseChannel channel).1 : CrownVertex m) =
        swapCrownShore (.inr channel.2.1) ∧
      (.inr (reverseChannel channel).2.1 : CrownVertex m) =
        swapCrownShore (.inl channel.1) := by
  exact ⟨rfl, rfl⟩

/-! ## Concrete Charlieplex counts -/

/-- At radix eight the crown graph has sixteen vertices, seven legal neighbors
at every phase/shore, and fifty-six canonically oriented edges. -/
theorem crown_eight_geometry :
    Fintype.card (CrownVertex 8) = 16 ∧
    (∀ source : Fin 8,
      Fintype.card {sink : Fin 8 //
        (crownGraph 8).Adj (.inl source) (.inr sink)} = 7) ∧
    Fintype.card (CrownEdge 8) = 56 := by
  constructor
  · simp [CrownVertex]
  constructor
  · intro source
    simpa using card_sink_ne 8 source
  · simpa using card_crownEdge 8

end Charlieplex

end Coeff2
