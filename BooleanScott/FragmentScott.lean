module
public import BooleanScott.GuardAtoms

/-! Finite-Scott clopen fragments. The predicate below is invariant under
homeomorphism and closed under finite disjoint sum, with no uniform rank
required across different finite sums. It covers root-free chart pieces. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Topology

def FiniteIso (x : SpaceType) := FiniteTest (n := 0) (fun X _ _ => spaceType X = x)

theorem finiteIso_of_scott {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X]
    {k : ℕ} {σ : Formula 0} (lev : AtLevel .pi (k : Ordinal.{0}) σ)
    (iso : ∀ (B : Type) [Countable B] [BooleanAlgebra B], Models (BoolOps.ofAlgebra B) σ ↔
      Nonempty (Clopens X ≃o B)) : FiniteIso (spaceType X) := by
  refine ⟨k+1,by omega,σ,lev.liftLevel (by exact_mod_cast Nat.le_succ k),fun Y _ _ _ _ _ u => ?_⟩
  have e : u = Fin.elim0 := Subsingleton.elim _ _
  rw [e]
  apply (iso (Clopens Y)).trans
  change _ ↔ spaceType Y = spaceType X
  rw [eq_comm (a := spaceType Y),spaceType_eq_iff]
  exact ⟨fun ⟨g⟩ => ⟨homeomorphOfClopens g⟩,fun ⟨g⟩ => ⟨clopensOfHomeomorph g⟩⟩

theorem finiteIso_mixed (d : ℕ) : FiniteIso (spaceType (Mixed d)) := by
  obtain ⟨ht,hz,_⟩ := mixed_stone d
  obtain ⟨_,_,lev,iso⟩ := mixed_finite_scott d
  exact finiteIso_of_scott lev iso

theorem finiteIso_tower (d : ℕ) : FiniteIso (towerType d) := by
  let := tower_zeroDimensional d
  let := tower_countable_clopens d
  let P (i : Fin (d+1)) := scatteredStage i
  have classify (C E : Clopens (tower d)) (same : ∀ i, (P i).count (spaceType C) = (P i).count (spaceType E)) :
      Nonempty (C ≃ₜ E) := by
    apply (spaceType_eq_iff _ _).mp
    exact towerForm_determined (tower_clopen_form d C) (tower_clopen_form d E) (fun k hk => same ⟨k,by omega⟩)
  obtain ⟨_,_,lev,iso⟩ := scott_of_finite_counts P (fun _ => finiteHit_stages isolatedClosure_finiteHit _) classify
  exact finiteIso_of_scott lev iso

theorem finiteIso_cantor : FiniteIso cantorType :=
  finiteIso_of_scott (k := 2) cantorSentence_level cantorScott

theorem finiteIso_empty : FiniteIso 0 := by
  apply (FiniteHit.emptyTest full_finiteHit).congr
  intro X _ _ _ _ _ _
  change (univ : Set X) = ∅ ↔ spaceType X = 0
  constructor
  · intro h
    let : IsEmpty X := ⟨fun x => (Set.ext_iff.mp h x).mp trivial⟩
    exact empty_spaceType X
  · intro eq
    obtain ⟨e⟩ := (spaceType_eq_iff X Empty).mp eq
    exact eq_empty_iff_forall_notMem.mpr (fun x => (e x).elim)

noncomputable def splitClopen {W : Type} [TopologicalSpace W] (C : Clopens W) : (C ⊕ (Cᶜ : Clopens W)) ≃ₜ W := by
  classical
  let e := Equiv.Set.sumCompl (C : Set W)
  exact e.toHomeomorphOfContinuousOpen (continuous_subtype_val.sumElim continuous_subtype_val)
    (C.isClopen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.sumElim C.isClopen.compl.isOpen.isOpenEmbedding_subtypeVal.isOpenMap)

theorem split_spaceType {W : Type} [TopologicalSpace W] (x y : SpaceType) :
    spaceType W = x+y ↔ ∃ C : Clopens W, spaceType C = x ∧ spaceType (Cᶜ : Clopens W) = y := by
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>
  constructor
  · intro eq
    obtain ⟨g⟩ := (spaceType_eq_iff W (X ⊕ Y)).mp eq
    let l : X → W := g.symm ∘ Sum.inl
    let r : Y → W := g.symm ∘ Sum.inr
    have hl : IsOpenEmbedding l := g.symm.isOpenEmbedding.comp .inl
    have hr : IsOpenEmbedding r := g.symm.isOpenEmbedding.comp .inr
    let C : Clopens W := ⟨g ⁻¹' range (Sum.inl : X → X ⊕ Y),isClopen_range_inl.preimage g.continuous⟩
    have left : (C : Set W) = range l := by
      ext z
      obtain ⟨z,rfl⟩ := g.symm.surjective z
      simp [C,l,range_comp]
    have right : ((Cᶜ : Clopens W) : Set W) = range r := by
      ext z
      obtain ⟨z,rfl⟩ := g.symm.surjective z
      cases z <;> simp [C,r,range_comp]
    exact ⟨C,(spaceType_eq_iff _ _).mpr ⟨(Homeomorph.setCongr left).trans hl.toIsEmbedding.toHomeomorph.symm⟩,
      (spaceType_eq_iff _ _).mpr ⟨(Homeomorph.setCongr right).trans hr.toIsEmbedding.toHomeomorph.symm⟩⟩
  · rintro ⟨C,hC,hD⟩
    rw [← hC,← hD]
    exact (spaceType_eq_iff _ _).mpr ⟨(splitClopen C).symm⟩

theorem FiniteIso.clopenTest {x : SpaceType} (h : FiniteIso x) :
    FiniteTest (n := 1) (fun _ _ v => spaceType (v 0) = x) := by
  obtain ⟨k,pos,φ,lev,t⟩ := h
  refine ⟨k,pos,φ.relative 0 Fin.elim0,lev.relative _ _,fun X _ _ _ _ _ v => ?_⟩
  let C := v 0
  let := clopen_compactSpace C
  let := (clopenRestriction C).surjective.countable
  have eq : v = fun _ => C := funext fun i => congrArg v (Subsingleton.elim ..)
  exact (show (φ.relative 0 Fin.elim0).Holds _ v ↔ Models (BoolOps.ofAlgebra (Clopens C)) φ from
    eq ▸ relative_models_clopen C lev).trans (t C Fin.elim0)

theorem finiteIso_add {x y : SpaceType} (hx : FiniteIso x) (hy : FiniteIso y) : FiniteIso (x+y) := by
  have both := hx.clopenTest.and (hy.clopenTest.substitute (m := 1) (fun _ => .compl (.var 0)))
  obtain ⟨k,_,h⟩ := both
  refine ⟨k+1+1,by omega,?_⟩
  have lifted := (h.someClopen (n := 0)).asPi
  apply (show StoneDef .pi ((k+1+1 : ℕ) : Ordinal.{0}) _ from by simpa using lifted).congr
  intro X _ _ _ _ _ v
  exact (split_spaceType x y).symm

theorem finiteIso_multiple {x : SpaceType} (h : FiniteIso x) (m : ℕ) : FiniteIso (m • x) := by
  induction m with
  | zero => simpa using finiteIso_empty
  | succ m ih => simpa only [succ_nsmul] using finiteIso_add ih h

theorem finiteIso_remainder {d : ℕ} {x : SpaceType} (h : PureRemainder d x) : FiniteIso x := by
  obtain ⟨c,t,hc,ht,rfl⟩ := h
  apply finiteIso_add
  · rcases hc with rfl|rfl
    · exact finiteIso_empty
    · exact finiteIso_cantor
  · rcases ht with rfl | ⟨j,_,m,_,rfl⟩
    · exact finiteIso_empty
    · exact finiteIso_multiple (finiteIso_tower j) m

theorem finiteIso_mixed_clopen (d : ℕ) (C : Clopens (Mixed d)) : FiniteIso (spaceType C) := by
  by_cases h : OnePoint.infty ∈ C
  · rw [(mixed_clopen_form d C).1 h]
    exact finiteIso_mixed d
  · exact finiteIso_remainder ((mixed_clopen_form d C).2 h)

end BooleanScott
