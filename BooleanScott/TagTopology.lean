module
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.InductiveDimension.Classes
public import Mathlib.Tactic

/-! Compactness and clopen tests underlying the two private-tag derivatives. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem clopen_hits_derived {C S : Set X} (hc : IsClopen C) :
    (C ∩ derivedSet S).Nonempty ↔ (C ∩ S).Infinite := by
  constructor
  · rintro ⟨x, hx, hacc⟩
    exact Infinite.of_accPt ((mem_derivedSet.mp hacc).nhds_inter (hc.isOpen.mem_nhds hx))
  · intro hinf
    obtain ⟨x,hx,hacc⟩ := hinf.exists_accPt_of_subset_isCompact hc.isClosed.isCompact
      inter_subset_left
    exact ⟨x,hx,hacc.mono (Filter.principal_mono.mpr inter_subset_right)⟩

/-- Every root of a tag outside the union of its eligible charts is part of
a finite set, irrespective of the number of other tags in the exterior. -/
theorem finite_exterior {C S : Set X} (hc : IsClopen C) (h : derivedSet S ⊆ C) :
    (S \ C).Finite := by
  by_contra hinf
  obtain ⟨x,hout,hd⟩ := (clopen_hits_derived (S := S) hc.compl).mpr
    (by simpa [Set.sdiff_eq, Set.inter_comm] using hinf)
  exact hout (h hd)

omit [CompactSpace X] in
/-- Size at least n in a clopen is equivalent to n disjoint clopen witnesses.
The forward direction also works for marks that are neither closed nor open. -/
theorem clopen_threshold [ZeroDimensionalSpace X] {C S : Set X} (hc : IsClopen C) (n : ℕ) :
    (∃ f : Fin n ↪ X, ∀ i, f i ∈ C ∩ S) ↔
    ∃ U : Fin n → Set X, (∀ i, IsClopen (U i) ∧ U i ⊆ C ∧ (U i ∩ S).Nonempty) ∧
       Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨V,hV,hdis⟩ := (finite_range f).t2_separation
    have hex (i : Fin n) := exists_isClopen_mem_of_isOpen
      (hc.isOpen.inter (hV (f i)).2) ⟨(hf i).1,(hV (f i)).1⟩
    choose U hU hmem hsub using hex
    refine ⟨U,fun i => ⟨hU i,(hsub i).trans inter_subset_left,f i,hmem i,(hf i).2⟩,?_⟩
    intro i j hij
    exact (hdis (mem_range_self i) (mem_range_self j) (f.injective.ne hij)).mono
      ((hsub i).trans inter_subset_right) ((hsub j).trans inter_subset_right)
  · rintro ⟨U,hU,hd⟩
    choose f hmem using fun i => (hU i).2.2
    refine ⟨⟨f,?_⟩,fun i => ⟨(hU i).2.1 (hmem i).1,(hmem i).2⟩⟩
    intro i j he
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (hmem i).1 (he ▸ (hmem j).1)

/-- In the guard each clopen contains finitely or cofinitely many distinct
anchors. This pins a unique limit even when the ambient compact space has
arbitrary additional points. -/
theorem unique_anchor_limit [ZeroDimensionalSpace X] (S : Set X) (hi : S.Infinite)
    (bipartition : ∀ C : Set X, IsClopen C → (C ∩ S).Finite ∨ (Cᶜ ∩ S).Finite) :
    ∃! t, t ∈ derivedSet S := by
  obtain ⟨t,ht⟩ := hi.exists_accPt_principal
  refine ⟨t,ht,?_⟩
  intro x hx
  by_contra hne
  obtain ⟨C,hC,hxC,hCt⟩ := exists_isClopen_mem_of_isOpen
    (isOpen_compl_singleton (x := t)) (show x ∈ ({t} : Set X)ᶜ from hne)
  rcases bipartition C hC with h | h
  · exact ((clopen_hits_derived hC).mp ⟨x,hxC,hx⟩) h
  · have htC : t ∈ Cᶜ := fun htc => hCt htc rfl
    exact ((clopen_hits_derived hC.compl).mp ⟨t,htC,ht⟩) h

end BooleanScott
