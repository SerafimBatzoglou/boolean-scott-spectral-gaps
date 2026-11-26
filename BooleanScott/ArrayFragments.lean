module
public import BooleanScott.FragmentScott

/-! Finite packet slices in arbitrary compactified sums. Each fragment
avoiding the compactification point is exactly the finite disjoint sum of
its component restrictions, also for non-identical or empty components. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped OnePoint Classical

theorem clopen_sup_type {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W]
    (U V : Clopens W) (apart : Disjoint (U : Set W) (V : Set W)) :
    spaceType (U ⊔ V : Clopens W) = spaceType U + spaceType V := by
  let l (x : U) : (U ⊔ V : Clopens W) := ⟨x.val,Or.inl x.property⟩
  let r (x : V) : (U ⊔ V : Clopens W) := ⟨x.val,Or.inr x.property⟩
  let f := Sum.elim l r
  have inj : Function.Injective f := by
    rintro (x|x) (y|y) eq
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun p : (U ⊔ V : Clopens W) => (p : W)) eq))
    · have xy : x.val=y.val := congrArg (fun p : (U ⊔ V : Clopens W) => (p : W)) eq
      exact False.elim (Set.disjoint_left.mp apart x.property (xy.symm ▸ y.property))
    · have xy : x.val=y.val := congrArg (fun p : (U ⊔ V : Clopens W) => (p : W)) eq
      exact False.elim (Set.disjoint_left.mp apart y.property (xy ▸ x.property))
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun p : (U ⊔ V : Clopens W) => (p : W)) eq))
  have surj : Function.Surjective f := by
    rintro ⟨x,hx⟩
    rcases hx with h|h
    · exact ⟨.inl ⟨x,h⟩,rfl⟩
    · exact ⟨.inr ⟨x,h⟩,rfl⟩
  let := clopen_compactSpace U
  let := clopen_compactSpace V
  let e := Equiv.ofBijective f ⟨inj,surj⟩
  have cont : Continuous f := (continuous_subtype_val.subtype_mk (fun x : U => (l x).property)).sumElim
    (continuous_subtype_val.subtype_mk (fun x : V => (r x).property))
  exact (spaceType_eq_iff _ _).mpr ⟨(Continuous.homeoOfEquivCompactToT2 (f := e) cont).symm⟩

theorem clopen_bot_type (W : Type) [TopologicalSpace W] : spaceType (⊥ : Clopens W) = 0 := by
  let : IsEmpty (⊥ : Clopens W) := ⟨fun x => x.property⟩
  exact empty_spaceType _

theorem mem_clopen_finSup {I W : Type} [TopologicalSpace W] (s : Finset I) (U : I → Clopens W) (x : W) :
    x ∈ s.sup U ↔ ∃ i ∈ s, x ∈ U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty,Finset.notMem_empty,false_and,exists_false]; exact Iff.rfl
  | insert i s hi ih =>
    rw [Finset.sup_insert]
    change (x ∈ U i ∨ x ∈ s.sup U) ↔ _
    rw [ih]
    simp

theorem clopen_finSup_type {I W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W]
    (s : Finset I) (U : I → Clopens W) (apart : Pairwise (fun i j => Disjoint (U i : Set W) (U j : Set W))) :
    spaceType (s.sup U : Clopens W) = ∑ i ∈ s, spaceType (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact clopen_bot_type W
  | insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi,clopen_sup_type,ih]
    apply Set.disjoint_left.mpr
    intro x hx h
    obtain ⟨j,hj,xj⟩ := (mem_clopen_finSup s U x).mp h
    have ne : i ≠ j := fun eq => hi (eq.symm ▸ hj)
    exact Set.disjoint_left.mp (apart ne) hx xj

variable {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]

def packetLift (i : I) (D : Clopens (X i)) : Clopens (PacketSum X) := by
  let := packetSum_hausdorff X
  let e := open_packetInclusion X i
  exact ⟨packetInclusion X i '' (D : Set (X i)),(D.isClopen.isClosed.isCompact.image e.continuous).isClosed,
    e.isOpenMap _ D.isClopen.isOpen⟩

theorem packetLift_type (i : I) (D : Clopens (X i)) : spaceType (packetLift X i D) = spaceType D := by
  let f (p : D) := packetInclusion X i p.val
  have emb : IsEmbedding f := (open_packetInclusion X i).isEmbedding.comp .subtypeVal
  have eq : ((packetLift X i D) : Set (PacketSum X)) = range f := by
    ext p
    exact ⟨fun ⟨x,hx,h⟩ => ⟨⟨x,hx⟩,h⟩,fun ⟨x,h⟩ => ⟨x,x.property,h⟩⟩
  exact (spaceType_eq_iff _ _).mpr ⟨(Homeomorph.setCongr eq).trans emb.toHomeomorph.symm⟩

theorem packetLifts_apart (D : ∀ i, Clopens (X i)) :
    Pairwise (fun i j => Disjoint (packetLift X i (D i) : Set (PacketSum X)) (packetLift X j (D j) : Set (PacketSum X))) := by
  intro i j ne
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,_,rfl⟩ ⟨y,_,eq⟩
  exact ne (congrArg Sigma.fst (OnePoint.coe_injective eq)).symm

theorem array_fragment_away (C : Clopens (PacketSum X)) (away : ∞ ∉ C) :
    ∃ F : Finset I, spaceType C = ∑ i ∈ F, spaceType (packetRestriction C i) := by
  classical
  let := packetSum_hausdorff X
  obtain ⟨_,F,tail⟩ := (clopen_array_iff _).mp C.isClopen
  let U i := packetLift X i (packetRestriction C i)
  have eq : C = F.sup U := by
    ext p
    apply Iff.trans _ (mem_clopen_finSup F U p).symm
    constructor
    · intro hp
      induction p using OnePoint.rec with
      | infty => exact (away hp).elim
      | coe p =>
        obtain ⟨i,x⟩ := p
        have hi : i ∈ F := by by_contra hn; exact away ((tail i hn x).mp hp)
        exact ⟨i,hi,x,hp,rfl⟩
    · rintro ⟨i,_,x,hx,rfl⟩
      exact hx
  refine ⟨F,?_⟩
  calc
    spaceType C = spaceType (F.sup U : Clopens (PacketSum X)) := congrArg (fun V : Clopens (PacketSum X) => spaceType V) eq
    _ = ∑ i ∈ F, spaceType (U i) := clopen_finSup_type _ _ (packetLifts_apart X _)
    _ = _ := Finset.sum_congr rfl fun i _ => packetLift_type X i _

theorem finiteIso_sum {I : Type} (F : Finset I) (x : I → SpaceType) (h : ∀ i ∈ F, FiniteIso (x i)) :
    FiniteIso (∑ i ∈ F, x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using finiteIso_empty
  | insert i F hi ih =>
    rw [Finset.sum_insert hi]
    exact finiteIso_add (h _ (Finset.mem_insert_self ..)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end BooleanScott
