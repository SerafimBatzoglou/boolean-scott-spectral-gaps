module
public import BooleanScott.StoneAbsorption
public import BooleanScott.TupleSystem

/-! The signs of a finite tuple of clopens partition the entire space.
Independent homeomorphisms of corresponding signs glue to a homeomorphism
carrying every coordinate of the tuple to its target. Empty signs are allowed. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Topology
open scoped Classical

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}

abbrev Pattern (n : ℕ) := Fin n → Bool

noncomputable def pointPattern (v : Fin n → Clopens X) (x : X) : Pattern n :=
  fun i => decide (x ∈ v i)

noncomputable def signCell (v : Fin n → Clopens X) (p : Pattern n) : Clopens X := by
  classical
  let U (i : Fin n) : Set X := if p i then (v i : Set X) else (v i : Set X)ᶜ
  refine ⟨⋂ i, U i,isClopen_iInter_of_finite (fun i => ?_)⟩
  cases hp : p i <;> simp only [U,hp,Bool.false_eq_true,ite_false,ite_true]
  · exact (v i).isClopen.compl
  · exact (v i).isClopen

theorem mem_signCell {v : Fin n → Clopens X} {p : Pattern n} {x : X} :
    x ∈ signCell v p ↔ pointPattern v x = p := by
  classical
  change (x ∈ ⋂ i, if p i then (v i : Set X) else (v i : Set X)ᶜ) ↔ _
  rw [mem_iInter,funext_iff]
  apply forall_congr'
  intro i
  cases hp : p i <;> simp [pointPattern]

noncomputable def collapseSigns (v : Fin n → Clopens X) : (Σ p : Pattern n, signCell v p) ≃ₜ X := by
  let f : (Σ p : Pattern n, signCell v p) ≃ X :=
    { toFun := fun z => z.2.val
      invFun := fun x => ⟨pointPattern v x,x,mem_signCell.mpr rfl⟩
      left_inv := by
        rintro ⟨p,x,hx⟩
        obtain rfl := (mem_signCell.mp hx).symm
        rfl
      right_inv := fun _ => rfl }
  exact f.toHomeomorphOfContinuousOpen (continuous_sigma (fun _ => continuous_subtype_val))
    (isOpenMap_sigma.mpr (fun p => (signCell v p).isClopen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap))

noncomputable def glueSigns (v : Fin n → Clopens X) (w : Fin n → Clopens Y)
    (e : ∀ p, signCell v p ≃ₜ signCell w p) : X ≃ₜ Y := by
  let parts : (Σ p : Pattern n, signCell v p) ≃ₜ (Σ p : Pattern n, signCell w p) :=
    { toFun := fun z => ⟨z.1,e z.1 z.2⟩
      invFun := fun z => ⟨z.1,(e z.1).symm z.2⟩
      left_inv := by rintro ⟨p,x⟩; simp
      right_inv := by rintro ⟨p,y⟩; simp
      continuous_toFun := continuous_sigma (fun p =>
        (continuous_sigmaMk (σ := fun p : Pattern n => (signCell w p : Type)) (i := p)).comp (e p).continuous)
      continuous_invFun := continuous_sigma (fun p =>
        (continuous_sigmaMk (σ := fun p : Pattern n => (signCell v p : Type)) (i := p)).comp (e p).symm.continuous) }
  exact ((collapseSigns v).symm.trans parts).trans (collapseSigns w)

theorem glueSigns_pattern (v : Fin n → Clopens X) (w : Fin n → Clopens Y)
    (e : ∀ p, signCell v p ≃ₜ signCell w p) (x : X) :
    pointPattern w (glueSigns v w e x) = pointPattern v x :=
  mem_signCell.mp ((e (pointPattern v x)) ⟨x,mem_signCell.mpr rfl⟩).property

theorem clopen_tuple_of_signs (v : Fin n → Clopens X) (w : Fin n → Clopens Y)
    (h : ∀ p, Nonempty (signCell v p ≃ₜ signCell w p)) :
    ∃ e : Clopens X ≃o Clopens Y, ∀ i, e (v i) = w i := by
  classical
  let e (p : Pattern n) := Classical.choice (h p)
  let g := glueSigns v w e
  refine ⟨clopensOfHomeomorph g,fun i => ?_⟩
  ext y
  change g.symm y ∈ v i ↔ y ∈ w i
  obtain ⟨x,rfl⟩ := g.surjective y
  rw [g.symm_apply_apply]
  have hi := congrFun (glueSigns_pattern v w e x) i
  change decide (g x ∈ w i) = decide (x ∈ v i) at hi
  by_cases hx : x ∈ v i <;> by_cases hy : g x ∈ w i <;> simp_all

end BooleanScott
