module
public import BooleanScott.RowArrayMatching

/-! Realizing either choice of the outer compactification point when whole
subarrays are selected. The missing-point criterion is phrased for arbitrary
clopen subspaces, so it also applies to nested rows. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

noncomputable def capped (atRoot : Bool) (Y : TopCat.{0}) : TopCat.{0} :=
  if atRoot then TopCat.of (OnePoint Y) else Y

theorem capped_congr {Y Z : TopCat.{0}} (b : Bool) (f : Y ≃ₜ Z) :
    spaceType (capped b Y) = spaceType (capped b Z) := by
  cases b
  · exact (spaceType_eq_iff _ _).mpr ⟨f⟩
  · exact (spaceType_eq_iff _ _).mpr ⟨f.onePointCongr⟩

theorem slice_type {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    (C : Clopens X) (z : X) (f : Y → X) (embedding : IsEmbedding f)
    (image : range f = (C : Set X) \ {z}) :
    spaceType C = spaceType (capped (decide (z ∈ C)) (TopCat.of Y)) := by
  classical
  let g (y : Y) : C := ⟨f y,(image ▸ mem_range_self y : f y ∈ (C : Set X) \ {z}).1⟩
  have emb : IsEmbedding g := IsEmbedding.of_comp (embedding.continuous.subtype_mk _)
    (continuous_subtype_val (p := fun x => x ∈ C)) embedding
  by_cases hz : z ∈ C
  · rw [show decide (z ∈ C) = true from decide_eq_true hz]
    let c : C := ⟨z,hz⟩
    let := clopen_compactSpace C
    apply (spaceType_eq_iff _ _).mpr
    refine ⟨(OnePoint.equivOfIsEmbeddingOfRangeEq c g emb ?_).symm⟩
    ext x
    constructor
    · rintro ⟨y,rfl⟩ h
      exact (image ▸ mem_range_self y : f y ∈ (C : Set X) \ {z}).2 (congrArg Subtype.val h)
    · intro h
      obtain ⟨y,hy⟩ := image.symm ▸ (show x.val ∈ (C : Set X) \ {z} from ⟨x.property,fun he => h (Subtype.ext he)⟩)
      exact ⟨y,Subtype.ext hy⟩
  · rw [show decide (z ∈ C) = false from decide_eq_false hz]
    apply (spaceType_eq_iff _ _).mpr
    have onto : Function.Surjective g := by
      intro x
      obtain ⟨y,hy⟩ := image.symm ▸ (show x.val ∈ (C : Set X) \ {z} from
        ⟨x.property,fun he => hz ((show x.val=z from he) ▸ x.property)⟩)
      exact ⟨y,Subtype.ext hy⟩
    exact ⟨(IsHomeomorph.homeomorph g (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨emb,onto⟩)).symm⟩

variable {I J : Type} {X : I → Type} {Y : J → Type} [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]

def subarrayMap (index : J ↪ I) (component : ∀ j, Y j → X (index j)) : (Σ j, Y j) → PacketSum X :=
  OnePoint.some ∘ Sigma.map index component

theorem subarrayMap_embedding (index : J ↪ I) (component : ∀ j, Y j → X (index j))
    (openEmb : ∀ j, IsOpenEmbedding (component j)) : IsOpenEmbedding (subarrayMap index component) :=
  OnePoint.isOpenEmbedding_coe.comp ((isOpenEmbedding_sigmaMap index.injective).mpr openEmb)

omit [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)] in
theorem subarrayMap_ne_root (index : J ↪ I) (component : ∀ j, Y j → X (index j)) (p : Σ j, Y j) :
    subarrayMap index component p ≠ ∞ := OnePoint.coe_ne_infty _

theorem subarray_type [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    (C : Clopens (PacketSum X)) (index : J ↪ I) (component : ∀ j, Y j → X (index j))
    (openEmb : ∀ j, IsOpenEmbedding (component j))
    (fibers : ∀ i (x : X i), packetInclusion X i x ∈ C ↔
      ∃ p, subarrayMap index component p = packetInclusion X i x) :
    spaceType C = spaceType (capped (decide (∞ ∈ C)) (TopCat.of (Σ j, Y j))) := by
  let := packetSum_hausdorff X
  apply slice_type C ∞ _ (subarrayMap_embedding index component openEmb).isEmbedding
  ext y
  induction y using OnePoint.rec with
  | infty => exact iff_of_false (fun ⟨p,h⟩ => subarrayMap_ne_root index component p h) (fun h => h.2 rfl)
  | coe p =>
    obtain ⟨i,x⟩ := p
    exact ⟨fun h => ⟨(fibers i x).mpr h,OnePoint.coe_ne_infty _⟩,fun h => (fibers i x).mp h.1⟩

/-- Assemble a clopen by prescribing all fibers and a compactification bit. -/
def arrayClopen [∀ i, CompactSpace (X i)] (b : Bool) (U : ∀ i, Clopens (X i))
    (uniform : ∃ F : Finset I, ∀ i ∉ F, ∀ x : X i, x ∈ U i ↔ b = true) : Clopens (PacketSum X) :=
  ⟨{p | p.elim (b=true) (fun q => q.2 ∈ U q.1)},(clopen_array_iff _).mpr ⟨fun i => (U i).isClopen,uniform⟩⟩

end BooleanScott
