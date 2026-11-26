module
public import BooleanScott.MixedPacket

/-! The actual mixed packet of index d absorbs a Cantor piece and every
scattered tower of height at most d. The isomorphisms are homeomorphisms
of entire spaces. No Scott-type test is used to infer absorption. -/
@[expose] public section
namespace BooleanScott
open Set Topology
open scoped OnePoint

def AbsorbsSpace (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :=
  Nonempty ((X ⊕ Y) ≃ₜ X)

theorem AbsorbsSpace.trans {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (xy : AbsorbsSpace X Y) (yz : AbsorbsSpace Y Z) : AbsorbsSpace X Z := by
  obtain ⟨f⟩ := xy
  obtain ⟨g⟩ := yz
  let expose := (f.symm.sumCongr (.refl Z)).trans (.sumAssoc X Y Z)
  exact ⟨(expose.trans ((Homeomorph.refl X).sumCongr g)).trans f⟩

def sumSwapLast (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    ((X ⊕ Y) ⊕ Z) ≃ₜ ((X ⊕ Z) ⊕ Y) :=
  ((Homeomorph.sumAssoc X Y Z).trans ((Homeomorph.refl X).sumCongr (.sumComm Y Z))).trans
    (Homeomorph.sumAssoc X Z Y).symm

theorem AbsorbsSpace.sumLeft {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : AbsorbsSpace X Y) (Z : Type) [TopologicalSpace Z] : AbsorbsSpace (X ⊕ Z) Y := by
  obtain ⟨f⟩ := h
  exact ⟨(sumSwapLast X Z Y).trans (f.sumCongr (.refl Z))⟩

theorem AbsorbsSpace.transport {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X ≃ₜ Y) (h : AbsorbsSpace Y Z) : AbsorbsSpace X Z := by
  obtain ⟨g⟩ := h
  exact ⟨((f.sumCongr (.refl Z)).trans g).trans f.symm⟩

noncomputable def onePoint_withCompact (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space (OnePoint X)] [T2Space Y] [CompactSpace Y] :
    OnePoint (X ⊕ Y) ≃ₜ (OnePoint X ⊕ Y) := by
  let f : X ⊕ Y → OnePoint X ⊕ Y := Sum.map OnePoint.some id
  have emb : IsOpenEmbedding f := IsOpenEmbedding.of_continuous_injective_isOpenMap
    (OnePoint.continuous_coe.sumMap continuous_id) (Sum.map_injective.mpr ⟨OnePoint.coe_injective,Function.injective_id⟩)
    (OnePoint.isOpenEmbedding_coe.isOpenMap.sumMap IsOpenMap.id)
  apply OnePoint.equivOfIsEmbeddingOfRangeEq (Sum.inl ∞) f emb.isEmbedding
  ext z
  cases z with
  | inl p =>
    induction p using OnePoint.rec with
    | infty =>
      apply iff_of_false _ (fun h => h rfl)
      rintro ⟨x|y,h⟩
      · exact OnePoint.coe_ne_infty x (Sum.inl.inj h)
      · cases h
    | coe x => exact iff_of_true ⟨Sum.inl x,rfl⟩ (fun h => OnePoint.coe_ne_infty x (Sum.inl.inj h))
  | inr y => exact iff_of_true ⟨Sum.inr y,rfl⟩ (fun h => by cases h)

theorem AbsorbsSpace.onePoint {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space (OnePoint X)] [T2Space Y] [CompactSpace Y] (h : AbsorbsSpace X Y) : AbsorbsSpace (OnePoint X) Y := by
  obtain ⟨g⟩ := h
  exact ⟨(onePoint_withCompact X Y).symm.trans g.onePointCongr⟩

abbrev Copies (X : Type) := Σ _ : ℕ, X

def absorbCopy (X : Type) [TopologicalSpace X] : (Copies X ⊕ X) ≃ₜ Copies X where
  toFun := Sum.elim (fun p => ⟨p.1+1,p.2⟩) (fun x => ⟨0,x⟩)
  invFun := fun ⟨i,x⟩ => match i with | 0 => Sum.inr x | n+1 => Sum.inl ⟨n,x⟩
  left_inv := by rintro (⟨n,x⟩|x) <;> rfl
  right_inv := by rintro ⟨_|n,x⟩ <;> rfl
  continuous_toFun := (continuous_sigma (fun i => continuous_sigmaMk (σ := fun _ : ℕ => X)
    (i := i+1))).sumElim (continuous_sigmaMk (σ := fun _ : ℕ => X) (i := 0))
  continuous_invFun := continuous_sigma (fun i => by
    cases i with
    | zero => exact continuous_inr
    | succ n => exact continuous_inl.comp (continuous_sigmaMk (σ := fun _ : ℕ => X) (i := n)))

def splitCopies (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Copies (X ⊕ Y) ≃ₜ (Copies X ⊕ Copies Y) where
  toFun := fun ⟨n,p⟩ => p.elim (fun x => Sum.inl ⟨n,x⟩) (fun y => Sum.inr ⟨n,y⟩)
  invFun := Sum.elim (fun p => ⟨p.1,Sum.inl p.2⟩) (fun p => ⟨p.1,Sum.inr p.2⟩)
  left_inv := by rintro ⟨_,x|y⟩ <;> rfl
  right_inv := by rintro (⟨_,x⟩|⟨_,y⟩) <;> rfl
  continuous_toFun := continuous_sigma (fun i =>
    (continuous_inl.comp (continuous_sigmaMk (σ := fun _ : ℕ => X) (i := i))).sumElim
    (continuous_inr.comp (continuous_sigmaMk (σ := fun _ : ℕ => Y) (i := i))))
  continuous_invFun := by
    apply Continuous.sumElim
    · apply continuous_sigma
      intro i
      exact (continuous_sigmaMk (σ := fun _ : ℕ => X ⊕ Y) (i := i)).comp continuous_inl
    · apply continuous_sigma
      intro i
      exact (continuous_sigmaMk (σ := fun _ : ℕ => X ⊕ Y) (i := i)).comp continuous_inr

theorem tower_absorbs_lower {q d : ℕ} (lt : q < d) : AbsorbsSpace (tower d) (tower q) := by
  induction d with
  | zero => omega
  | succ d ih =>
    have step : AbsorbsSpace (tower (d+1)) (tower d) := by
      let := packetSum_hausdorff (fun _ : ℕ => (tower d : Type))
      exact AbsorbsSpace.onePoint ⟨absorbCopy (tower d)⟩
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ lt) with rfl | less
    · exact step
    · exact step.trans (ih less)

theorem mixed_absorbs_cantor (d : ℕ) : AbsorbsSpace (Mixed d) CantorBits := by
  let := packetSum_hausdorff (fun _ : ℕ => CantorBits ⊕ (tower d : Type))
  have hc : AbsorbsSpace (Copies CantorBits) CantorBits := ⟨absorbCopy CantorBits⟩
  exact (AbsorbsSpace.transport (splitCopies CantorBits (tower d)) (hc.sumLeft (Copies (tower d)))).onePoint

theorem mixed_absorbs_tower (d q : ℕ) (le : q ≤ d) : AbsorbsSpace (Mixed d) (tower q) := by
  let := packetSum_hausdorff (fun _ : ℕ => CantorBits ⊕ (tower d : Type))
  have ht : AbsorbsSpace (Copies (tower d)) (tower d) := ⟨absorbCopy _⟩
  have step : AbsorbsSpace (Mixed d) (tower d) :=
    (AbsorbsSpace.transport ((splitCopies CantorBits (tower d)).trans (.sumComm _ _))
      (ht.sumLeft (Copies CantorBits))).onePoint
  rcases Nat.eq_or_lt_of_le le with rfl | lt
  · exact step
  · exact step.trans (tower_absorbs_lower lt)

end BooleanScott
