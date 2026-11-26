module
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.ClopenBox
public import Mathlib.Topology.InductiveDimension.Classes

/-! Realize every actual Boolean algebra, including the trivial algebra, as
the clopens of a compact zero-dimensional Hausdorff space. The spectrum of
the associated Boolean ring has a clopen basis because every element is
idempotent. Countability of the algebra supplies second countability. -/
@[expose] public section
namespace BooleanScott
open TopologicalSpace PrimeSpectrum

abbrev StoneModel (A : Type) [BooleanAlgebra A] := PrimeSpectrum (AsBoolRing A)

noncomputable def stoneRepresentation (A : Type) [BooleanAlgebra A] :
    A ≃o Clopens (StoneModel A) := by
  let toIdem : A ≃ {x : AsBoolRing A // IsIdempotentElem x} :=
    toBoolRing.trans (Equiv.subtypeUnivEquiv (fun x => BooleanRing.isIdempotentElem x)).symm
  let e := toIdem.trans (PrimeSpectrum.isIdempotentElemEquivClopens (R := AsBoolRing A)).toEquiv
  have meet (x y : A) : e (x ⊓ y) = e x ⊓ e y :=
    PrimeSpectrum.isIdempotentElemEquivClopens_mul (toIdem x) (toIdem y)
  refine { e with map_rel_iff' := ?_ }
  intro x y
  change e x ≤ e y ↔ x ≤ y
  rw [← inf_eq_left, ← meet, e.injective.eq_iff, inf_eq_left]

theorem stone_zeroDimensional (A : Type) [BooleanAlgebra A] : ZeroDimensionalSpace (StoneModel A) := by
  apply ZeroDimensionalSpace.of_isTopologicalBasis _ isTopologicalBasis_basic_opens
  rintro _ ⟨a,rfl⟩
  exact (PrimeSpectrum.isIdempotentElemEquivClopens ⟨a,BooleanRing.isIdempotentElem a⟩).isClopen

theorem stone_hausdorff (A : Type) [BooleanAlgebra A] : T2Space (StoneModel A) := by
  let :=  stone_zeroDimensional A
  constructor
  intro x y hxy
  obtain ⟨U,hU,h⟩ := exists_isOpen_xor_mem hxy
  rcases h with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · obtain ⟨V,hV,hxV,sub⟩ := exists_isClopen_mem_of_isOpen hU hx
    exact ⟨V,Vᶜ,hV.isOpen,hV.compl.isOpen,hxV,fun hyV => hy (sub hyV),disjoint_compl_right⟩
  · obtain ⟨V,hV,hyV,sub⟩ := exists_isClopen_mem_of_isOpen hU hy
    exact ⟨Vᶜ,V,hV.compl.isOpen,hV.isOpen,fun hxV => hx (sub hxV),hyV,disjoint_compl_left⟩

theorem stone_secondCountable (A : Type) [BooleanAlgebra A] [Countable A] :
    SecondCountableTopology (StoneModel A) := by
  let :=  stone_zeroDimensional A
  let :=  stone_hausdorff A
  exact Clopens.countable_iff_secondCountable.mp (stoneRepresentation A).surjective.countable

end BooleanScott
