module
public import BooleanScott.CompactArrays
public import Mathlib.Data.Fintype.Pi

/-! Canonical set-theoretic codes for clopens of compactified sums. The
finite support is exact, and the coordinate field records the actual
restriction at every exceptional index. This works even for empty packets. -/
@[expose] public section
namespace BooleanScott
open TopologicalSpace Set
open scoped OnePoint Classical

variable {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]

structure ArrayCode (X : I → Type) [∀ i, TopologicalSpace (X i)] where
  atInfinity : Bool
  support : Finset I
  entry : ∀ i : support, Clopens (X i.val)
  changed : ∀ i, entry i ≠ if atInfinity then ⊤ else ⊥

def packetRestriction (C : Clopens (OnePoint (Σ i, X i))) (i : I) : Clopens (X i) :=
  ⟨{x | OnePoint.some (Sigma.mk i x) ∈ C}, C.isClopen.preimage (OnePoint.continuous_coe.comp continuous_sigmaMk)⟩

theorem finite_changed (C : Clopens (OnePoint (Σ i, X i))) :
    {i | packetRestriction C i ≠ (if ∞ ∈ C then ⊤ else ⊥)}.Finite := by
  classical
  obtain ⟨_,F,tail⟩ := (clopen_array_iff _).mp C.isClopen
  apply F.finite_toSet.subset
  intro i hi
  by_contra hout
  apply hi
  ext x
  by_cases b : ∞ ∈ C
  · rw [ite_eq_left b]
    exact ⟨fun _ => trivial, fun _ => (tail i hout x).mpr b⟩
  · rw [ite_eq_right b]
    exact ⟨fun hp => b ((tail i hout x).mp hp), False.elim⟩

noncomputable def encodeClopen (C : Clopens (OnePoint (Σ i, X i))) : ArrayCode X := by
  classical
  let h := finite_changed C
  refine ⟨decide (∞ ∈ C), h.toFinset, fun i => packetRestriction C i.val, ?_⟩
  intro i
  have hp : packetRestriction C i.val ≠ (if ∞ ∈ C then ⊤ else ⊥) := h.mem_toFinset.mp i.property
  simpa using hp

noncomputable def ArrayCode.coordinate (d : ArrayCode X) (i : I) : Clopens (X i) := by
  classical exact if hi : i ∈ d.support then d.entry ⟨i,hi⟩ else if d.atInfinity then ⊤ else ⊥

noncomputable def ArrayCode.decode (d : ArrayCode X) : Clopens (OnePoint (Σ i, X i)) := by
  classical
  let S : Set (OnePoint (Σ i, X i)) := {z | z.elim (d.atInfinity = true)
    (fun p => p.2 ∈ d.coordinate p.1)}
  apply Clopens.mk S ((clopen_array_iff S).mpr ?_)
  refine ⟨fun i => (d.coordinate i).isClopen,d.support,?_⟩
  intro i hi x
  change x ∈ d.coordinate i ↔ d.atInfinity = true
  cases hb : d.atInfinity <;> simp [coordinate,hi,hb]
  · exact fun h => h
  · trivial

theorem coordinate_encodeClopen (C : Clopens (OnePoint (Σ i, X i))) (i : I) :
    (encodeClopen C).coordinate i = packetRestriction C i := by
  classical
  by_cases h : i ∈ (finite_changed C).toFinset
  · simp [ArrayCode.coordinate,encodeClopen,h]
  · have same : packetRestriction C i = (if ∞ ∈ C then ⊤ else ⊥) :=
      Classical.not_not.mp (fun hn => h ((finite_changed C).mem_toFinset.mpr hn))
    simp [ArrayCode.coordinate,encodeClopen,h,same]

theorem decode_encodeClopen (C : Clopens (OnePoint (Σ i, X i))) : (encodeClopen C).decode = C := by
  classical
  ext z
  induction z using OnePoint.rec with
  | infty => change decide (∞ ∈ C) = true ↔ ∞ ∈ C; simp
  | coe p =>
    change p.2 ∈ (encodeClopen C).coordinate p.1 ↔ _
    rw [coordinate_encodeClopen]
    rfl

theorem countable_array_clopens [Countable I] [∀ i, Countable (Clopens (X i))] :
    Countable (Clopens (OnePoint (Σ i, X i))) := by
  let rep (d : ArrayCode X) : Bool × (Σ F : Finset I, ∀ i : F, Clopens (X i.val)) :=
    (d.atInfinity,⟨d.support,d.entry⟩)
  have inj : Function.Injective rep := by
    rintro ⟨b,F,c,h⟩ ⟨b',F',c',h'⟩ eq
    cases eq
    rfl
  let := inj.countable
  exact (Function.LeftInverse.injective decode_encodeClopen).countable

end BooleanScott
