module
public import BooleanScott.StoneMaps

/-! A Boolean product with the clopens of the fixed summand corresponds
exactly to a disjoint topological sum. Both implications apply to any
countable Boolean model and also to finite Boolean algebras. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def clopenPreimage {f : X → Y} (hf : Continuous f) (C : Clopens Y) : Clopens X :=
  ⟨f ⁻¹' (C : Set Y), C.isClopen.preimage hf⟩

def clopensOfHomeomorph (h : X ≃ₜ Y) : Clopens X ≃o Clopens Y where
  toFun := clopenPreimage h.symm.continuous
  invFun := clopenPreimage h.continuous
  left_inv C := by ext x; change h.symm (h x) ∈ C ↔ x ∈ C; rw [h.symm_apply_apply]
  right_inv C := by ext y; change h (h.symm y) ∈ C ↔ y ∈ C; rw [h.apply_symm_apply]
  map_rel_iff' := by
    intro C D
    constructor
    · intro le x hx
      have hx' : h.symm (h x) ∈ C := (h.symm_apply_apply x).symm ▸ hx
      have hy : h.symm (h x) ∈ D := @le (h x) hx'
      simpa using hy
    · exact fun le _ hx => le hx

def sumClopen (C : Clopens X) (D : Clopens Y) : Clopens (X ⊕ Y) :=
  ⟨{p | p.elim (· ∈ C) (· ∈ D)}, isClosed_sum_iff.mpr ⟨C.isClopen.isClosed,D.isClopen.isClosed⟩,
    isOpen_sum_iff.mpr ⟨C.isClopen.isOpen,D.isClopen.isOpen⟩⟩

def sumClopensIso : Clopens (X ⊕ Y) ≃o (Clopens X × Clopens Y) where
  toFun C := (clopenPreimage continuous_inl C,clopenPreimage continuous_inr C)
  invFun p := sumClopen p.1 p.2
  left_inv C := by ext (x|y) <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro C D
    constructor
    · rintro ⟨hl,hr⟩ (x|y) hx
      · exact @hl x hx
      · exact @hr y hx
    · intro h
      exact ⟨fun _ ht => h ht, fun _ ht => h ht⟩

/-- Substituting this equivalence in the absorption field converts the
all-model Boolean isomorphism question to the homeomorphism question. -/
theorem algebra_absorption_iff (A : Type) [BooleanAlgebra A] (S : Type)
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [ZeroDimensionalSpace S] :
    Nonempty (A ≃o A × Clopens S) ↔ Nonempty ((StoneModel A ⊕ S) ≃ₜ StoneModel A) := by
  let := stone_zeroDimensional A
  let := stone_hausdorff A
  let e := stoneRepresentation A
  let product : (A × Clopens S) ≃o Clopens (StoneModel A ⊕ S) :=
    (e.prodCongr (OrderIso.refl (Clopens S))).trans sumClopensIso.symm
  constructor
  · rintro ⟨f⟩
    exact ⟨homeomorphOfClopens ((product.symm.trans f.symm).trans e)⟩
  · rintro ⟨h⟩
    exact ⟨(e.trans (clopensOfHomeomorph h.symm)).trans product.symm⟩

end BooleanScott
