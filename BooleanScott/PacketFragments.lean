module
public import BooleanScott.PacketBasis
public import BooleanScott.PacketStone
public import Mathlib.Topology.Category.TopCat.Basic

/-! Every clopen in a repeated compactified sum is a finite disjoint sum
of component fragments, together with a whole copy of the original space
when it retains the apex. The fragments may be arbitrary clopen subsets. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped OnePoint Classical

def addPieces (base : TopCat.{0}) : List TopCat.{0} → TopCat.{0}
  | [] => base
  | C :: l => TopCat.of ((addPieces base l : Type) ⊕ (C : Type))

noncomputable def splitSubspace {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y] (C : Clopens (X ⊕ Y)) :
    (clopenPreimage continuous_inl C ⊕ clopenPreimage continuous_inr C) ≃ₜ C := by
  let := clopen_compactSpace (clopenPreimage continuous_inl C)
  let := clopen_compactSpace (clopenPreimage continuous_inr C)
  let e : (clopenPreimage continuous_inl C ⊕ clopenPreimage continuous_inr C) ≃ C :=
    { toFun := Sum.elim (fun x => ⟨Sum.inl x.val,x.property⟩) (fun y => ⟨Sum.inr y.val,y.property⟩)
      invFun := fun ⟨z,h⟩ => match z,h with | Sum.inl x,h => Sum.inl ⟨x,h⟩ | Sum.inr y,h => Sum.inr ⟨y,h⟩
      left_inv := by rintro (⟨x,h⟩|⟨y,h⟩) <;> rfl
      right_inv := by rintro ⟨x|y,h⟩ <;> rfl }
  exact Continuous.homeoOfEquivCompactToT2 (f := e) ((continuous_inl.comp continuous_subtype_val).subtype_mk _
    |>.sumElim ((continuous_inr.comp continuous_subtype_val).subtype_mk _))

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem repeatedAbsorb_head (x : X) :
    repeatedAbsorb X (Sum.inr x) = packetInclusion (fun _ : ℕ => X) 0 x := by
  let := packetSum_hausdorff (fun _ : ℕ => X)
  let h := onePoint_withCompact (Copies X) X
  have eq : h.symm (Sum.inr x) = OnePoint.some (Sum.inr x) := h.symm_apply_eq.mpr rfl
  change (absorbCopy X).onePointCongr (h.symm (Sum.inr x)) = _
  rw [eq]
  rfl

noncomputable def nextClopen (C : Clopens (Repeated X)) : Clopens (Repeated X) :=
  clopenPreimage (dropFirst_open X).continuous C

noncomputable def splitFirst (C : Clopens (Repeated X)) :
    (nextClopen C ⊕ packetRestriction C 0) ≃ₜ C := by
  let := packetSum_hausdorff (fun _ : ℕ => X)
  let e := repeatedAbsorb X
  let D := clopenPreimage e.continuous C
  let head := (Homeomorph.refl X).subtype (p := fun x => x ∈ packetRestriction C 0)
    (q := fun x => x ∈ clopenPreimage continuous_inr D) (fun x => by
      change packetInclusion _ 0 x ∈ C ↔ repeatedAbsorb X (.inr x) ∈ C
      rw [repeatedAbsorb_head])
  exact (((Homeomorph.refl (nextClopen C)).sumCongr head).trans (splitSubspace D)).trans
    (e.subtype (p := fun z => z ∈ D) (q := fun z => z ∈ C) (fun _ => Iff.rfl))

private theorem finiteFront (C : Clopens (Repeated X)) (k : ℕ) :
    ∃ l : List (Clopens X), Nonempty
      (C ≃ₜ addPieces (TopCat.of ((nextClopen^[k] C) : Type)) (l.map (fun D : Clopens X => TopCat.of (D : Type)))) := by
  induction k generalizing C with
  | zero => exact ⟨[],⟨Homeomorph.refl C⟩⟩
  | succ k ih =>
    obtain ⟨l,⟨g⟩⟩ := ih (nextClopen C)
    exact ⟨(packetRestriction C 0)::l,⟨(splitFirst C).symm.trans
      (g.sumCongr (.refl (packetRestriction C 0)))⟩⟩

theorem mem_next_iterate (C : Clopens (Repeated X)) (k : ℕ) (p : Repeated X) :
    p ∈ nextClopen^[k] C ↔ (dropFirst X)^[k] p ∈ C := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply',ih]
    rfl

theorem fragments_repeated (C : Clopens (Repeated X)) :
    ∃ (l : List (Clopens X)) (D : Clopens (Repeated X)),
      (∀ p : Repeated X, p ∈ D ↔ ∞ ∈ C) ∧ Nonempty
      (C ≃ₜ addPieces (TopCat.of (D : Type)) (l.map (fun V : Clopens X => TopCat.of (V : Type)))) := by
  classical
  obtain ⟨_,F,hF⟩ := (clopen_array_iff _).mp C.isClopen
  let k := F.sup id + 1
  obtain ⟨l,h⟩ := finiteFront C k
  refine ⟨l,nextClopen^[k] C,fun p => ?_,h⟩
  rw [mem_next_iterate]
  induction p using OnePoint.rec with
  | infty =>
    rw [show (dropFirst X)^[k] ∞ = ∞ from Function.IsFixedPt.iterate (dropFirst_infty X) k]
  | coe p =>
    rcases p with ⟨i,x⟩
    change (dropFirst X)^[k] (packetInclusion _ i x) ∈ C ↔ _
    rw [tail_image]
    apply hF
    intro hi
    have bound : i+k ≤ F.sup id := Finset.le_sup (f := id) hi
    dsimp [k] at bound
    omega

end BooleanScott
