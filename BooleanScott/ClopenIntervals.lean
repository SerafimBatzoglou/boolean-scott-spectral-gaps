module
public import BooleanScott.Relativization
public import BooleanScott.Coding
public import BooleanScott.StoneAbsorption

/-! A relative Scott sentence in a named clopen literally tests the clopen
algebra of that subspace, with complement taken relative to the subspace. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace

variable {X : Type} [TopologicalSpace X]

def clopenRestriction (C : Clopens X) : Iic C ≃o Clopens C where
  toFun U := clopenPreimage continuous_subtype_val U.val
  invFun V :=
    ⟨⟨Subtype.val '' (V : Set C),
      C.isClopen.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ V.isClopen.isClosed,
      C.isClopen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ V.isClopen.isOpen⟩,
      fun _ ⟨z,_,hz⟩ => hz ▸ z.property⟩
  left_inv U := by
    apply Subtype.ext
    apply SetLike.ext
    intro z
    change (∃ p : C, p.val ∈ U.val ∧ p.val = z) ↔ z ∈ U.val
    exact ⟨fun ⟨_,hp,eq⟩ => eq ▸ hp, fun hz => ⟨⟨z,U.property hz⟩,hz,rfl⟩⟩
  right_inv V := by
    apply SetLike.ext
    intro z
    change (∃ p : C, p ∈ V ∧ p.val = z.val) ↔ z ∈ V
    exact ⟨fun ⟨_,hp,eq⟩ => Subtype.ext eq ▸ hp, fun hz => ⟨z,hz,rfl⟩⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h z hz
      exact @h ⟨z,U.property hz⟩ hz
    · exact fun h _ hz => h hz

theorem relative_models_clopen (C : Clopens X) {φ : Formula 0} {pol : Polarity}
    {α : Ordinal.{0}} (h : AtLevel pol α φ) :
    (φ.relative (0 : Fin 1) Fin.elim0).Holds (BoolOps.ofAlgebra (Clopens X)) (fun _ => C) ↔
    Models (BoolOps.ofAlgebra (Clopens C)) φ := by
  rw [Formula.holds_relative]
  let := intervalAlgebra C
  have congruence := OpsIso.models h (OpsIso.ofOrder (clopenRestriction C))
  rw [intervalOps_eq]
  have empty : (fun _ : Fin 0 => restrictTo C C) = Fin.elim0 := Subsingleton.elim _ _
  rw [empty]
  exact congruence

end BooleanScott
