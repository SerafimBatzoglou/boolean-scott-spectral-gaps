module
public import BooleanScott.PacketFragments

/-! Homeomorphism types under finite disjoint sum. Equality in this monoid
is equivalent to the existence of an actual homeomorphism. It permits the
finite remainders in a packet fragment to be rearranged algebraically. -/
@[expose] public section
namespace BooleanScott
open TopologicalSpace
open scoped OnePoint Classical

def homeomorphismSetoid : Setoid TopCat.{0} where
  r X Y := Nonempty (X ≃ₜ Y)
  iseqv := ⟨fun X => ⟨.refl X⟩,fun ⟨h⟩ => ⟨h.symm⟩,fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

abbrev SpaceType := Quotient homeomorphismSetoid

def spaceType (X : Type) [TopologicalSpace X] : SpaceType :=
  Quotient.mk _ (TopCat.of X)

theorem spaceType_eq_iff (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    spaceType X = spaceType Y ↔ Nonempty (X ≃ₜ Y) :=
  Quotient.eq

instance : Zero SpaceType := ⟨spaceType Empty⟩

instance : Add SpaceType := ⟨Quotient.map₂ (fun X Y : TopCat.{0} => TopCat.of (X ⊕ Y))
  (fun _ _ ⟨f⟩ _ _ ⟨g⟩ => ⟨f.sumCongr g⟩)⟩

instance : AddCommMonoid SpaceType where
  nsmul := nsmulRec
  add_assoc := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact Quotient.sound ⟨Homeomorph.sumAssoc X Y Z⟩
  zero_add := by
    rintro ⟨X⟩
    exact Quotient.sound ⟨Homeomorph.emptySum X Empty⟩
  add_zero := by
    rintro ⟨X⟩
    exact Quotient.sound ⟨Homeomorph.sumEmpty X Empty⟩
  add_comm := by
    rintro ⟨X⟩ ⟨Y⟩
    exact Quotient.sound ⟨Homeomorph.sumComm X Y⟩

theorem spaceType_sum (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    spaceType (X ⊕ Y) = spaceType X + spaceType Y := rfl

theorem spaceType_absorbs {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] :
    spaceType X + spaceType Y = spaceType X ↔ AbsorbsSpace X Y := spaceType_eq_iff _ _

theorem spaceType_addPieces (base : TopCat.{0}) (l : List TopCat.{0}) :
    spaceType (addPieces base l) = spaceType base + (l.map (fun C : TopCat.{0} => spaceType C)).sum := by
  induction l with
  | nil => change spaceType base = spaceType base + 0; rw [add_zero]
  | cons C l ih =>
    change spaceType (addPieces base l) + spaceType C = _
    rw [ih,List.map_cons,List.sum_cons]
    ac_rfl

theorem empty_spaceType (X : Type) [TopologicalSpace X] [IsEmpty X] : spaceType X = 0 := by
  apply (spaceType_eq_iff X Empty).mpr
  exact ⟨{ toEquiv := Equiv.equivOfIsEmpty X Empty
           continuous_toFun := continuous_of_discreteTopology
           continuous_invFun := continuous_of_discreteTopology }⟩

theorem univ_clopen_spaceType {X : Type} [TopologicalSpace X] {C : Clopens X}
    (h : ∀ x, x ∈ C) : spaceType C = spaceType X := by
  have eq : (C : Set X) = Set.univ := Set.eq_univ_of_forall h
  exact (spaceType_eq_iff _ _).mpr ⟨(Homeomorph.setCongr eq).trans (Homeomorph.Set.univ X)⟩

theorem spaceType_fragment {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (C : Clopens (Repeated X)) : ∃ l : List (Clopens X), spaceType C =
      (if (∞ : Repeated X) ∈ C then spaceType (Repeated X) else 0) +
        (l.map (fun D : Clopens X => spaceType D)).sum := by
  classical
  obtain ⟨l,D,hD,⟨e⟩⟩ := fragments_repeated C
  refine ⟨l,((spaceType_eq_iff _ _).mpr ⟨e⟩).trans ?_⟩
  rw [spaceType_addPieces,List.map_map]
  by_cases hc : (∞ : Repeated X) ∈ C
  · rw [ite_eq_left hc,univ_clopen_spaceType (fun x => (hD x).mpr hc)]
    rfl
  · let : IsEmpty D := ⟨fun x => hc ((hD x).mp x.property)⟩
    rw [ite_eq_right hc,empty_spaceType D]
    rfl

end BooleanScott
