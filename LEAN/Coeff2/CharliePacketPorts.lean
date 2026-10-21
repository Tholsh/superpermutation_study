import Coeff2.CharliePacketAssembly

/-!
# All-order literal course execution and the reduced packet ports

Unlike an occupation count, these formulas retain the directed entry and exit
phases. `advance` executes complete courses separated by actual cost-two moves.
They are an endpoint bridge, not yet the full partial-course footprint proof.
-/
namespace Coeff2.Charlieplex.PacketPorts
open EganOccupationLift EganProcedure
variable {α : Type*}

def finish (p : List α) (extra : ℕ) : List α :=
  p.rotate (p.length - 1 + extra)

def nextCourse (p : List α) (extra : ℕ) : List α := two (finish p extra)

def advance (p : List α) (k : ℕ) : List α := (fun w => nextCourse w 0)^[k] p

theorem finish_ordinary (q : List α) (a : α) : finish (q ++ [a]) 0 = a :: q := by
  simp only [finish, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    Nat.add_zero, List.rotate_append_length_eq, List.singleton_append]

theorem finish_extra (p : List α) (hp : p ≠ []) : finish p 1 = p := by
  have hl : 0 < p.length := List.length_pos_iff.mpr hp
  have he : p.length - 1 + 1 = p.length := by omega
  rw [finish, he, List.rotate_length]

theorem next_ordinary (q : List α) (a : α) (hq : q ≠ []) :
    nextCourse (q ++ [a]) 0 = q.rotate 1 ++ [a] := by
  rw [nextCourse, finish_ordinary]
  cases q with
  | nil => contradiction
  | cons x t => simp [two, List.append_assoc]

theorem advance_ordinary (q : List α) (a : α) (hq : q ≠ []) (k : ℕ) :
    advance (q ++ [a]) k = q.rotate k ++ [a] := by
  induction k with
  | zero => simp [advance]
  | succ k ih =>
    simp only [advance, Function.iterate_succ_apply'] at *
    rw [ih, next_ordinary _ a (by simpa using hq), List.rotate_rotate]

theorem ordinary_end (q : List α) (a : α) (hq : q ≠ []) (k : ℕ) :
    finish (advance (q ++ [a]) k) 0 = a :: q.rotate k := by
  rw [advance_ordinary q a hq k, finish_ordinary]

theorem extra_bridge (x y : α) (t : List α) :
    nextCourse (x :: y :: t) 1 = t ++ [y,x] := by
  rw [nextCourse, finish_extra _ (by simp)]
  rfl

theorem insert_split (t : List α) (a : α) (k : ℕ) (hk : k ≤ t.length) :
    t.insertIdx k a = t.take k ++ a :: t.drop k := by
  induction t generalizing k with
  | nil =>
    have : k = 0 := by simpa using hk
    subst k
    rfl
  | cons x t ih =>
    cases k with
    | zero => rfl
    | succ k => simpa using congrArg (List.cons x) (ih k (by simpa using hk))

/-- The actual kth course points at exactly the kth insertion position. This
retains the order, not just the cardinality of the resulting fiber. -/
theorem pointed_course_entry (t : List α) (z a : α) (k : ℕ) (hk : k ≤ t.length) :
    (advance ((t ++ [z]) ++ [a]) k).IsRotated (z :: t.insertIdx k a) := by
  rw [advance_ordinary _ a (by simp),
    List.rotate_eq_drop_append_take (by simp; omega),
    List.drop_append_of_le_length hk, List.take_append_of_le_length hk,
    insert_split t a k hk]
  have h := List.isRotated_append (l := t.drop k) (l' := z :: (t.take k ++ [a]))
  simpa [List.append_assoc] using h

section Occupation
variable [DecidableEq α]
open Finset EganComponentGraph

theorem orbit_eq_of_rotated {p q : List α} (h : p.IsRotated q) :
    rotationOrbit p = rotationOrbit q := by
  ext w
  simp only [mem_rotationOrbit]
  exact ⟨fun hw => hw.trans h, fun hw => hw.trans h.symm⟩

def segmentOccupation (p : List α) (courses : ℕ) : Finset (List α) :=
  (range courses).biUnion (fun k => rotationOrbit (advance p k))

/-- An exact ordered partial-course-to-insertion bridge, uniform in n and in
the length of the partial segment. Each course contributes its full orbit. -/
theorem segment_occupation (t : List α) (z a : α) (courses : ℕ)
    (hc : courses ≤ t.length + 1) :
    segmentOccupation ((t ++ [z]) ++ [a]) courses =
      rootedOrbits z ((range courses).image (fun k => t.insertIdx k a)) := by
  rw [segmentOccupation, rootedOrbits, image_biUnion]
  apply biUnion_congr rfl
  intro k hk
  exact orbit_eq_of_rotated (pointed_course_entry t z a k (by
    have := mem_range.mp hk; omega))

theorem full_ordinary_occupation (t : List α) (z a : α)
    (ht : (z :: t).Nodup) (ha : a ∉ z :: t) :
    segmentOccupation ((t ++ [z]) ++ [a]) (t.length + 1) = markedCycle a (z :: t) := by
  rw [segment_occupation t z a _ (by omega), component_rooted z a t ht ha]
  rfl
end Occupation

/-- Fixing two trailing clocks collapses every macro transition back to a
lower-order overlap problem. These are literal endpoints of the full piece. -/
theorem fixed_clock_exit (q : List α) (a b : α) :
    finish (advance ((q ++ [b]) ++ [a]) q.length) 0 = a :: b :: q := by
  rw [ordinary_end _ a (by simp), List.rotate_append_length_eq]
  rfl

theorem fixed_clock_seam (q r : List α) (a b : α) (m k : ℕ)
    (_hq : q.length = m) (hr : r.length = m) (hk : k ≤ m) :
    (a :: b :: q).drop (m-k+2) = (r ++ [b,a]).take k ↔ q.drop (m-k) = r.take k := by
  have hd : m-k+2 = (m-k)+1+1 := by omega
  rw [hd, List.drop_succ_cons, List.drop_succ_cons,
    List.take_append_of_le_length (by omega)]

/-- Exact ledger for that fixed-clock subclass: it inherits the lower-order
length rather than erasing its attachment problem. P is the number of pieces,
lowerCost their realized lower-order transition sum. -/
theorem fixed_clock_length (n P lowerCost : ℤ) :
    P*(n*n+n-3) - ((n-2)*(P-1)-lowerCost) =
      P*(n*n-1) + ((n-2)+lowerCost) := by ring

theorem fixed_clock_factorial_prefix (m : ℕ) :
    ((m+2).factorial : ℤ) + ((m+1).factorial : ℤ) =
      (((m : ℤ)+2)^2-1) * (m.factorial : ℤ) := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- With q containing the inserted marker, the short piece has length(q)+1
courses. Its exit is obtained by literal course execution. -/
theorem short_exit (q : List α) (z x y a : α) :
    finish (advance (q ++ [z,x,y,a]) q.length) 0 = a :: z :: x :: y :: q := by
  have he : q ++ [z,x,y,a] = (q ++ [z,x,y]) ++ [a] := by simp
  rw [he, ordinary_end _ a (by simp)]
  rw [List.rotate_append_length_eq]
  rfl

def longAExit (s : List α) (z x y a b : α) : List α :=
  finish (advance
    (nextCourse (advance (s ++ [z,b,x,y,a]) (s.length + 1)) 1)
    (s.length + 2)) 0

def longBExit (s : List α) (z x y a b : α) : List α :=
  finish (advance
    (nextCourse (advance (y :: (s ++ [z,x,a,b])) (s.length + 3)) 1)
    s.length) 0

theorem longA_exit (s : List α) (z x y a b : α) :
    longAExit s z x y a b = b :: a :: x :: y :: (s ++ [z]) := by
  have he : s ++ [z,b,x,y,a] = ((s ++ [z]) ++ [b,x,y]) ++ [a] := by simp
  unfold longAExit
  rw [he, advance_ordinary _ a (by simp)]
  have hlen : (s ++ [z]).length = s.length + 1 := by simp
  rw [← hlen, List.rotate_append_length_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [extra_bridge]
  have he2 : (y :: (s ++ [z,a])) ++ [x,b] = ((y :: (s ++ [z])) ++ [a,x]) ++ [b] := by simp
  rw [he2, ordinary_end _ b (by simp)]
  have hlen2 : (y :: (s ++ [z])).length = s.length + 2 := by simp
  rw [← hlen2, List.rotate_append_length_eq]
  rfl

theorem longB_exit (s : List α) (z x y a b : α) :
    longBExit s z x y a b = a :: z :: x :: b :: y :: s := by
  have he : y :: (s ++ [z,x,a,b]) = ((y :: (s ++ [z,x])) ++ [a]) ++ [b] := by simp
  unfold longBExit
  rw [he, advance_ordinary _ b (by simp)]
  have hlen : (y :: (s ++ [z,x])).length = s.length + 3 := by simp
  rw [← hlen, List.rotate_append_length_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [extra_bridge]
  have he2 : s ++ [z,x,b] ++ [y,a] = (s ++ [z,x,b,y]) ++ [a] := by simp
  rw [he2, ordinary_end _ a (by simp), List.rotate_append_length_eq]
  rfl

/-- A guaranteed n-3 overlap between the two long ports. Using it is optional:
globally optimal words may interleave the two pieces. -/
theorem long_port_seam (s : List α) (z x y a b : α) :
    PacketAssembly.IsSeam (longAExit s z x y a b)
      (y :: (s ++ [z,x,a,b])) (s.length + 2) := by
  rw [longA_exit]
  simp only [PacketAssembly.IsSeam, List.length_cons, List.length_append, List.length_nil]
  refine ⟨by omega, by omega, ?_⟩
  have he : s.length + 1 + 1 + 1 + 1 + 1 - (s.length + 2) = 3 := by omega
  rw [he]
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons]
  have ht : (s ++ [z,x,a,b]).take (s.length + 1) = s ++ [z] := by
    rw [List.take_append]; simp
  exact congrArg (List.cons y) ht.symm

#print axioms advance_ordinary
#print axioms pointed_course_entry
#print axioms segment_occupation
#print axioms full_ordinary_occupation
#print axioms fixed_clock_exit
#print axioms fixed_clock_seam
#print axioms fixed_clock_length
#print axioms fixed_clock_factorial_prefix
#print axioms short_exit
#print axioms longA_exit
#print axioms longB_exit
#print axioms long_port_seam
end Coeff2.Charlieplex.PacketPorts
