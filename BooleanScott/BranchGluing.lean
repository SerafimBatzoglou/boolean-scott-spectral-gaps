module
public import BooleanScott.BranchSchedule

/-! Extend a homeomorphism on countably many converging clopen blocks
over the common limit and arbitrary unchanged exterior in a guard model. -/
@[expose] public section
namespace BooleanScott
open Set Topology Filter TopologicalSpace
open scoped Classical OnePoint

variable {X : Type} [TopologicalSpace X] [T2Space X] [ZeroDimensionalSpace X]

def blockExterior (t : X) (W : ℕ → Clopens X) : Set X := {x | x ≠ t ∧ ∀ n, x ∉ W n}

theorem blockExterior_open (t : X) (W : ℕ → Clopens X) (converges : ConvergingSites t W) :
    IsOpen (blockExterior t W) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨ne,avoid⟩
  obtain ⟨H,hH,hx,sub⟩ := exists_isClopen_mem_of_isOpen (isClosed_singleton (X := X) (x := t)).isOpen_compl ne
  let C : Clopens X := ⟨H,hH⟩
  have tC : t ∉ C := fun h => sub h rfl
  obtain ⟨N,hN⟩ := eventually_atTop.mp (converges Cᶜ tC)
  let V := C \ (Finset.range N).sup W
  have here : x ∈ V := ⟨hx,fun h => by
    obtain ⟨i,_,h⟩ := (mem_clopen_finSup _ _ _).mp h
    exact avoid i h⟩
  apply mem_of_superset (V.isClopen.isOpen.mem_nhds here)
  intro y hy
  refine ⟨fun eq => tC (eq ▸ hy.1),fun n atW => ?_⟩
  rcases lt_or_ge n N with lt|ge
  · exact hy.2 ((mem_clopen_finSup _ _ _).mpr ⟨n,Finset.mem_range.mpr lt,atW⟩)
  · exact (hN n ge atW) hy.1

theorem block_sum_absorption [CompactSpace X] (t : X) (W : ℕ → Clopens X)
    (apart : Pairwise (fun i j => Disjoint (W i : Set X) (W j : Set X)))
    (avoids : ∀ n, t ∉ W n) (converges : ConvergingSites t W)
    {R : Type} [TopologicalSpace R] [CompactSpace R] [T2Space R] (h : AbsorbsSpace (Σ n, W n) R) :
    AbsorbsSpace X R := by
  let E := blockExterior t W
  let whole (p : Σ n, W n) : X := p.2.val
  have inj : Function.Injective whole := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    have ij : i=j := by
      by_contra ne
      exact Set.disjoint_left.mp (apart ne) x.property ((show x.val=y.val from eq).symm ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext eq)
  let f : (Σ n, W n) ⊕ E → X := Sum.elim whole Subtype.val
  have hf : Function.Injective f := by
    rintro (p|x) (q|y) eq
    · exact congrArg Sum.inl (inj eq)
    · exact False.elim (y.property.2 p.1 ((show p.2.val=y.val from eq) ▸ p.2.property))
    · exact False.elim (x.property.2 q.1 ((show x.val=q.2.val from eq).symm ▸ q.2.property))
    · exact congrArg Sum.inr (Subtype.ext eq)
  have cont : Continuous whole := continuous_sigma fun _ => continuous_subtype_val
  have op : IsOpenMap whole := isOpenMap_sigma.mpr fun i => (W i).isClopen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have emb : IsOpenEmbedding f := .of_continuous_injective_isOpenMap
    (cont.sumElim continuous_subtype_val) hf (op.sumElim (blockExterior_open t W converges).isOpenEmbedding_subtypeVal.isOpenMap)
  have rangeEq : range f = {t}ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨n,y⟩|y,rfl⟩
      · exact fun eq => avoids n ((show y.val=t from eq) ▸ y.property)
      · exact y.property.1
    · intro ne
      by_cases hit : ∃ n, x ∈ W n
      · obtain ⟨n,hx⟩ := hit
        exact ⟨.inl ⟨n,⟨x,hx⟩⟩,rfl⟩
      · exact ⟨.inr ⟨x,ne,fun n hx => hit ⟨n,hx⟩⟩,rfl⟩
  let e := OnePoint.equivOfIsEmbeddingOfRangeEq t f emb.isEmbedding rangeEq
  let := e.isEmbedding.t2Space
  exact AbsorbsSpace.transport e.symm (h.sumLeft E).onePoint

/-- Separate the two sequences of summands in a disjoint sum of pairs. -/
def splitFamilies {I : Type} (A B : I → Type) [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    (Σ i, A i ⊕ B i) ≃ₜ ((Σ i, A i) ⊕ (Σ i, B i)) where
  toFun := fun ⟨i,p⟩ => p.elim (fun x => Sum.inl ⟨i,x⟩) (fun y => Sum.inr ⟨i,y⟩)
  invFun := Sum.elim (fun ⟨i,x⟩ => ⟨i,Sum.inl x⟩) (fun ⟨i,y⟩ => ⟨i,Sum.inr y⟩)
  left_inv := by rintro ⟨_,x|y⟩ <;> rfl
  right_inv := by rintro (⟨_,x⟩|⟨_,y⟩) <;> rfl
  continuous_toFun := continuous_sigma (fun i =>
    (continuous_inl.comp (continuous_sigmaMk (σ := A) (i := i))).sumElim
    (continuous_inr.comp (continuous_sigmaMk (σ := B) (i := i))))
  continuous_invFun := (continuous_sigma fun i => (continuous_sigmaMk (σ := fun i => A i ⊕ B i) (i := i)).comp continuous_inl).sumElim
    (continuous_sigma fun i => (continuous_sigmaMk (σ := fun i => A i ⊕ B i) (i := i)).comp continuous_inr)

def shiftFamily (R : TopCat.{0}) (B : ℕ → TopCat.{0}) : ℕ → TopCat.{0}
  | 0 => R
  | n+1 => B n

def shiftFamilyHomeo (R : TopCat.{0}) (B : ℕ → TopCat.{0}) :
    ((Σ n, B n) ⊕ R) ≃ₜ (Σ n, shiftFamily R B n) where
  toFun := Sum.elim (fun ⟨n,x⟩ => (⟨n+1,x⟩ : Σ k, shiftFamily R B k))
    (fun x : R => (⟨0,x⟩ : Σ k, shiftFamily R B k))
  invFun := fun ⟨n,x⟩ => match n with | 0 => Sum.inr x | k+1 => Sum.inl ⟨k,x⟩
  left_inv := by rintro (⟨n,x⟩|x) <;> rfl
  right_inv := by rintro ⟨_|n,x⟩ <;> rfl
  continuous_toFun := by
    apply Continuous.sumElim
    · apply continuous_sigma
      intro n
      exact continuous_sigmaMk (σ := fun k => (shiftFamily R B k : Type)) (i := n+1)
    · exact continuous_sigmaMk (σ := fun k => (shiftFamily R B k : Type)) (i := 0)
  continuous_invFun := continuous_sigma fun n => by
    cases n with
    | zero => exact continuous_inr
    | succ n => exact continuous_inl.comp continuous_sigmaMk

theorem ray_absorption (R : TopCat.{0}) (W A B : ℕ → TopCat.{0})
    (targets : ∀ n, spaceType (W n)=spaceType (A n)+spaceType (B n))
    (exchange : ∀ n, spaceType (A n)+spaceType (shiftFamily R B n)=spaceType (A n)+spaceType (B n)) :
    AbsorbsSpace (Σ n, W n) R := by
  let target (n : ℕ) := ((spaceType_eq_iff (W n) (A n ⊕ B n)).mp (targets n)).some
  let swap (n : ℕ) := ((spaceType_eq_iff (A n ⊕ shiftFamily R B n) (A n ⊕ B n)).mp (exchange n)).some
  let separate := (sigmaFamilyCongr (Equiv.refl ℕ) target).trans (splitFamilies (fun n => (A n : Type)) (fun n => (B n : Type)))
  let paired := splitFamilies (fun n => (A n : Type)) (fun n => (shiftFamily R B n : Type))
  let start := (separate.sumCongr (.refl R)).trans (.sumAssoc _ _ _)
  let shift := (Homeomorph.refl (Σ n, A n)).sumCongr (shiftFamilyHomeo R B)
  let matchAll := sigmaFamilyCongr (Y := fun n => A n ⊕ B n) (Equiv.refl ℕ) swap
  let lineUp := ((start.trans shift).trans paired.symm).trans matchAll
  exact ⟨lineUp.trans (sigmaFamilyCongr (Y := fun n => A n ⊕ B n) (Equiv.refl ℕ) target).symm⟩

end BooleanScott
