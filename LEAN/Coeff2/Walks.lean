/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Words

/-!
# Walks in the proper overlap graph, `Λ(n)`, superpermutations, `S(n)` (paper §2)

Formalization choices:
* A walk `W = (π₁,…,π_m)` is a nonempty list of permutation words in which consecutive
  words are joined by proper edges.  Walk *times* are 0-based here (`vert 0 = π₁`);
  the paper is 1-based.
* `vert t` is total, with junk value `[]` past the end of the walk.
* `Λ(n)` and `S(n)` are `Nat.sInf`s of the corresponding sets of lengths.
-/

namespace Coeff2

open List

/-- Paper §2: a walk in the proper overlap graph: a (nonempty) sequence of vertices with
consecutive vertices joined by proper edges. -/
structure Walk (n : ℕ) : Type where
  /-- The vertices `π₁, …, π_m` visited by the walk, in order (0-based here). -/
  verts : List (List ℕ)
  ne : verts ≠ []
  isPerm : ∀ w ∈ verts, IsPermWord n w
  chain : verts.IsChain (ProperStep n)

variable {n : ℕ}

namespace Walk

/-- The number `m` of vertices of the walk (visits, counted with multiplicity). -/
def numVerts (W : Walk n) : ℕ := W.verts.length

/-- The vertex `π_{t+1}` of the walk at (0-based) time `t`; junk value `[]` for
`t ≥ numVerts`. -/
def vert (W : Walk n) (t : ℕ) : List ℕ := W.verts.getD t []

/-- Paper §2: `wt(W) = Σ_{i=1}^{m−1} wt(π_i, π_{i+1})`, the total weight of the walk. -/
noncomputable def wtW (W : Walk n) : ℕ :=
  (List.zipWith (wt n) W.verts W.verts.tail).sum

/-- Paper §2: `len(W) = n + wt(W)`. -/
noncomputable def len (W : Walk n) : ℕ := n + W.wtW

/-- Paper §2: a walk is covering if it visits every permutation at least once. -/
def Covering (W : Walk n) : Prop :=
  ∀ w, IsPermWord n w → w ∈ W.verts

/-- The prefix walk consisting of the first `t+1` vertices `π₁,…,π_{t+1}` of `W`
(everything up to and including time `t`; the whole walk if `t+1 ≥ numVerts`).
Used to define the stepwise increments `Δp, Δc, Δv` of paper §3–§4. -/
def pre (W : Walk n) (t : ℕ) : Walk n where
  verts := W.verts.take (t + 1)
  ne := by
    obtain ⟨a, l, h⟩ := List.exists_cons_of_ne_nil W.ne
    rw [h, List.take_succ_cons]
    exact List.cons_ne_nil _ _
  isPerm := fun w hw => W.isPerm w (List.take_subset _ _ hw)
  chain := W.chain.take _

end Walk

/-- Paper §2: `Λ(n)`, the minimum length of a covering walk in the proper overlap
graph. -/
noncomputable def Lam (n : ℕ) : ℕ :=
  sInf {m | ∃ W : Walk n, W.Covering ∧ W.len = m}

/-- Paper §1: a word over `[n]` is an `n`-superpermutation if it contains every
permutation of `[n]` as a factor (contiguous block). -/
def IsSuperperm (n : ℕ) (w : List ℕ) : Prop :=
  ∀ v, IsPermWord n v → v <:+: w

/-- Paper §1: `S(n)`, the minimum length of an `n`-superpermutation. -/
noncomputable def S (n : ℕ) : ℕ :=
  sInf {m | ∃ w : List ℕ, IsSuperperm n w ∧ w.length = m}

/-- Paper §1/§3: the HPV bound `HPV(n) = n! + (n−1)! + (n−2)! + n − 3`. -/
def HPV (n : ℕ) : ℕ :=
  n.factorial + (n - 1).factorial + (n - 2).factorial + n - 3

end Coeff2
