module
public import BooleanScott.CompactArrays
public import Mathlib.Topology.DerivedSet

/-! Computing derivatives in compactified packet sums. Inside an open
component they are entirely local. At infinity they depend on the number of
components hit, regardless of the number of points in any one component. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology
open scoped OnePoint

def derivatives {X : Type} [TopologicalSpace X] (n : ℕ) (S : Set X) : Set X :=
  derivedSet^[n] S

theorem local_derivative {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (e : IsOpenEmbedding f) (S : Set Y) :
    f ⁻¹' derivedSet S = derivedSet (f ⁻¹' S) := by
  ext x
  change AccPt (f x) (𝓟 S) ↔ AccPt x (𝓟 (f ⁻¹' S))
  rw [accPt_iff_nhds,accPt_iff_nhds]
  constructor
  · intro h U hU
    obtain ⟨y,⟨⟨z,hz,rfl⟩,hS⟩,hne⟩ := h _ (e.image_mem_nhds.mpr hU)
    exact ⟨z,⟨hz,hS⟩,fun eq => hne (congrArg f eq)⟩
  · intro h U hU
    obtain ⟨z,⟨hz,hS⟩,hne⟩ := h _ (e.continuous.continuousAt hU)
    exact ⟨f z,⟨hz,hS⟩,e.injective.ne hne⟩

theorem local_derivatives {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (e : IsOpenEmbedding f) (n : ℕ) (S : Set Y) :
    f ⁻¹' derivatives n S = derivatives n (f ⁻¹' S) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [derivatives, Function.iterate_succ_apply']
    rw [local_derivative e]
    exact congrArg derivedSet ih

abbrev PacketSum {I : Type} (X : I → Type) := OnePoint (Σ i, X i)

theorem packetSum_hausdorff {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] : T2Space (PacketSum X) := by
  let : WeaklyLocallyCompactSpace (Σ i, X i) := ⟨fun ⟨i,x⟩ =>
    ⟨range (Sigma.mk i),isCompact_range continuous_sigmaMk,
      IsOpenEmbedding.sigmaMk.isOpen_range.mem_nhds (mem_range_self x)⟩⟩
  infer_instance

theorem derivatives_succ {X : Type} [TopologicalSpace X] (k : ℕ) (S : Set X) :
    derivatives (k+1) S = derivedSet (derivatives k S) := Function.iterate_succ_apply' ..

def packetInclusion {I : Type} (X : I → Type) (i : I) : X i → PacketSum X :=
  fun x => OnePoint.some (Sigma.mk i x)

theorem open_packetInclusion {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)] (i : I) :
    IsOpenEmbedding (packetInclusion X i) :=
  OnePoint.isOpenEmbedding_coe.comp IsOpenEmbedding.sigmaMk

def occupied {I : Type} {X : I → Type} (S : Set (PacketSum X)) : Set I :=
  {i | ∃ x, packetInclusion X i x ∈ S}

theorem infty_in_derived_iff {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] (S : Set (PacketSum X)) :
    ∞ ∈ derivedSet S ↔ (occupied S).Infinite := by
  classical
  rw [mem_derivedSet,accPt_iff_nhds]
  constructor
  · intro h finite
    let F := finite.toFinset
    let U : Set (PacketSum X) := {p | p.elim True (fun z => z.1 ∉ F)}
    have hU : U ∈ 𝓝 ∞ := nhds_of_cofinite_components (show ∞ ∈ U from trivial) F (fun _ hi _ => hi)
    obtain ⟨y,⟨hy,hs⟩,hn⟩ := h U hU
    induction y using OnePoint.rec with
    | infty => exact hn rfl
    | coe p => exact hy (finite.mem_toFinset.mpr ⟨p.2,hs⟩)
  · intro inf U hU
    obtain ⟨F,hF⟩ := cofinite_components_of_nhds hU
    obtain ⟨i,⟨x,hx⟩,hi⟩ := inf.exists_notMem_finset F
    exact ⟨_,⟨hF i hi x,hx⟩,OnePoint.coe_ne_infty _⟩

end BooleanScott
