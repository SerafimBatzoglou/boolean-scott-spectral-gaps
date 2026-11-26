module
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Tactic

/-! Compact subsets of a sum meet finitely many components. In a sum of
compact packets this gives both directions of the whole-packet neighborhood
criterion at infinity, and the finite-deviation description of its clopens. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology
open scoped OnePoint

variable {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)]

theorem compact_finite_components {K : Set (Σ i, X i)} (h : IsCompact K) :
    ∃ F : Finset I, ∀ (p : Σ i, X i), p ∈ K → p.1 ∈ F := by
  obtain ⟨s,t,hs,_,hst⟩ := h.sigma_exists_finite_sigma_eq _
  refine ⟨hs.toFinset, fun p hp => hs.mem_toFinset.mpr ?_⟩
  rw [← hst] at hp
  exact hp.1

/-- An arbitrary neighborhood of the compactification point contains whole
components outside one finite list. No local compactness is necessary here. -/
theorem cofinite_components_of_nhds {U : Set (OnePoint (Σ i, X i))}
    (hU : U ∈ 𝓝 ∞) : ∃ F : Finset I, ∀ i ∉ F, ∀ x : X i,
    OnePoint.some (Sigma.mk i x) ∈ U := by
  classical
  obtain ⟨K,⟨_,hc⟩,hKU⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
  obtain ⟨F,hF⟩ := compact_finite_components hc
  exact ⟨F, fun i hi x => hKU (Or.inl ⟨⟨i,x⟩,fun hk => hi (hF _ hk),rfl⟩)⟩

/-- Whole components outside a finite list, together with infinity, give
a neighborhood if the omitted components are compact. -/
theorem nhds_of_cofinite_components [∀ i, CompactSpace (X i)] {U : Set (OnePoint (Σ i, X i))}
    (ht : ∞ ∈ U) (F : Finset I)
    (outside : ∀ i ∉ F, ∀ x : X i, OnePoint.some (Sigma.mk i x) ∈ U) :
    U ∈ 𝓝 ∞ := by
  classical
  let K := (F : Set I).sigma (fun i => (univ : Set (X i)))
  have hc : IsCompact K := Set.isCompact_sigma F.finite_toSet (fun _ _ => isCompact_univ)
  have hclosed : IsClosed K := by
    apply isClosed_sigma_iff.mpr
    intro i
    by_cases h : i ∈ F <;> simp [K, Set.preimage, h]
  apply OnePoint.hasBasis_nhds_infty.mem_iff.mpr
  refine ⟨K,⟨hclosed,hc⟩,?_⟩
  rintro z (⟨⟨i,x⟩,hz,rfl⟩ | hz)
  · exact outside i (fun hi => hz ⟨hi,mem_univ x⟩) x
  · simpa using (show z = ∞ from hz) ▸ ht

theorem clopen_array_iff [∀ i, CompactSpace (X i)] (C : Set (OnePoint (Σ i, X i))) :
    IsClopen C ↔
    (∀ i, IsClopen {x : X i | OnePoint.some (Sigma.mk i x) ∈ C}) ∧
    ∃ F : Finset I, ∀ i ∉ F, ∀ x : X i, OnePoint.some (Sigma.mk i x) ∈ C ↔ ∞ ∈ C := by
  classical
  constructor
  · intro hc
    refine ⟨fun i => hc.preimage (OnePoint.continuous_coe.comp continuous_sigmaMk), ?_⟩
    by_cases h : ∞ ∈ C
    · obtain ⟨F,hF⟩ := cofinite_components_of_nhds (hc.isOpen.mem_nhds h)
      exact ⟨F,fun i hi x => iff_of_true (hF i hi x) h⟩
    · obtain ⟨F,hF⟩ := cofinite_components_of_nhds (hc.compl.isOpen.mem_nhds h)
      exact ⟨F,fun i hi x => iff_of_false (hF i hi x) h⟩
  · rintro ⟨hf,F,hF⟩
    have open_of (U : Set (OnePoint (Σ i, X i)))
        (hu : ∀ i, IsOpen {x : X i | OnePoint.some (Sigma.mk i x) ∈ U})
        (he : ∀ i ∉ F, ∀ x : X i, OnePoint.some (Sigma.mk i x) ∈ U ↔ ∞ ∈ U) :
        IsOpen U := by
      apply isOpen_iff_mem_nhds.mpr
      intro p hp
      induction p using OnePoint.rec with
      | infty => exact nhds_of_cofinite_components hp F (fun i hi x => (he i hi x).mpr hp)
      | coe p =>
        have hpre : IsOpen (OnePoint.some ⁻¹' U : Set (Σ i, X i)) := isOpen_sigma_iff.mpr hu
        rw [OnePoint.nhds_coe_eq]
        exact hpre.mem_nhds hp
    refine ⟨isOpen_compl_iff.mp (open_of Cᶜ (fun i => (hf i).isClosed.isOpen_compl)
      (fun i hi x => not_congr (hF i hi x))), open_of C (fun i => (hf i).isOpen) hF⟩

end BooleanScott
