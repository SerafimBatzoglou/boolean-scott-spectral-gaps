module
public import BooleanScott.CrossingCounts
public import BooleanScott.TagCurrents
public import BooleanScott.GuardBorel

/-! Necessity in every geometric guard model. An absorbing homeomorphism
produces finitely supported signed currents at all vertices. Conservation
at a tag follows by counting its finite exterior, including transfers that
cross the two endpoint charts. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Descriptive
open scoped Classical

theorem rootRow_other_tag {e : ℕ} (ne : tagNumber (.inl []) ≠ e) (D : Clopens RootRow) :
    (tagRoot e).count (spaceType D) = 0 := by
  rw [LocalLocus.count_clopen,tagRoot_row,ite_eq_right ne,inter_empty,encard_empty]

theorem rootRow_private_exterior (v : Vertex) :
    (tagRoot (tagNumber (.inl v))).count (spaceType ((extraRow v)ᶜ : Clopens RootRow)) = 0 := by
  by_cases h : v=[]
  · rw [extraRow,ite_eq_left h,compl_top,clopen_bot_type,map_zero]
  · exact rootRow_other_tag (fun eq => h (Sum.inl.inj (tagNumber_injective eq)).symm) _

theorem rootRow_edge_exterior (v : Vertex) (i : ℕ) (D : Clopens RootRow) :
    (tagRoot (tagNumber (.inr (v,i)))).count (spaceType D) = 0 := by
  apply rootRow_other_tag
  intro eq
  cases tagNumber_injective eq

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem image_exterior (f : (X ⊕ RootRow) ≃ₜ X) (e : ℕ) (C : Clopens X) (D : Clopens RootRow)
    (cover : (tagAnchor e).points X ⊆ C) (noExtra : (tagRoot e).count (spaceType (Dᶜ : Clopens RootRow)) = 0) :
    (pointsInside (tagRoot e) (imageCut f C D))ᶜ.Finite ∧ (pointsInside (tagRoot e) C)ᶜ.Finite ∧
      (pointsInside (tagRoot e) (imageCut f C D))ᶜ.ncard = (pointsInside (tagRoot e) C)ᶜ.ncard := by
  let P := tagRoot e
  have finite : (pointsInside P C)ᶜ.Finite :=
    ((finite_roots_outside e C cover).preimage Subtype.val_injective.injOn).subset (fun x h => ⟨x.property,h⟩)
  have eq : (pointsInside P (imageCut f C D))ᶜ.encard = (pointsInside P C)ᶜ.encard := by
    change (pointsInside P ((imageCut f C D)ᶜ)).encard = (pointsInside P Cᶜ).encard
    rw [pointsInside_count,pointsInside_count,imageCut_compl,imageCut_type,map_add,noExtra,add_zero]
  exact ⟨finite_of_encard_eq_coe (eq.trans finite.cast_ncard_eq.symm),finite,congrArg ENat.toNat eq⟩

theorem guarded_absorption_implies_branch {T : tree ℕ} (G : GuardData T X) (f : (X ⊕ RootRow) ≃ₜ X) :
    HasBranch T := by
  classical
  obtain ⟨b,pair⟩ := disjoint_vertex_sectors G
  choose a imageEq using fun v => shifted_sector (b v) f
  let delta (v : Vertex) : ℕ := if v=[] then 1 else 0
  have excess (v : Vertex) (j : ℕ) : (privateLocus (2*j)).count (spaceType (a v).region) =
      (privateLocus (2*j)).count (spaceType (b v).region) + (delta v : ℕ∞) := by
    rw [imageEq,shiftedCut,imageCut_type,map_add,extraRow_ledger]; split <;> simp_all [delta]
  choose d changeAt div using fun v => crossing_balance (a v) (b v) (delta v) (excess v)
  let I (v : Vertex) (e : ℕ) := pointsInside (tagRoot e) (a v).region
  let J (v : Vertex) (e : ℕ) := pointsInside (tagRoot e) (b v).region
  have finDiff (v : Vertex) (e : ℕ) : (differenceSupport (I v e) (J v e)).Finite := by
    apply finite_root_differences
    · exact (a v).balance _ sdiff_le (fun h => h.2 (b v).center)
    · exact (b v).balance _ sdiff_le (fun h => h.2 (a v).center)
  refine TagCurrents.hasBranch (T := T) ⟨d,?_,?_,?_,?_⟩
  · intro v e ne
    by_contra out
    have empty (b : Sector G v) : pointsInside (tagRoot e) b.region = ∅ :=
      encard_eq_zero.mp ((pointsInside_count _ _).trans (b.absent e out))
    exact ne (by rw [changeAt,empty,empty]; simp [netChange])
  · intro v
    let e := tagNumber (.inl v)
    have cover : (tagAnchor e).points X ⊆ (b v).region := by
      rw [G.private_anchor]
      exact singleton_subset_iff.mpr (b v).center
    obtain ⟨af,bf,eq⟩ := image_exterior f e (b v).region (extraRow v) cover (rootRow_private_exterior v)
    rw [changeAt,imageEq,shiftedCut,netChange_finite_exteriors _ _ af bf,eq]
    simp
  · intro v i retained
    let w := v++[i]
    let e := tagNumber (.inr (v,i))
    have ne : v ≠ w := by intro h; have hw := congrArg List.length h; simp [w] at hw
    let C := (b v).region ⊔ (b w).region
    let D := extraRow v ⊔ extraRow w
    have cover : (tagAnchor e).points X ⊆ C := by
      intro x hx
      rcases G.edge_anchor v i retained hx with rfl|h
      · exact Or.inl (b v).center
      · exact Or.inr (h ▸ (b w).center)
    obtain ⟨af,bf,eq⟩ := image_exterior f e C D cover (rootRow_edge_exterior v i _)
    have cutEq : (a v).region ⊔ (a w).region = imageCut f C D := by rw [imageEq,imageEq]; exact imageCut_sup ..
    have src : I v e ∪ I w e = pointsInside (tagRoot e) (imageCut f C D) :=
      congrArg (pointsInside (tagRoot e)) cutEq
    have dst : J v e ∪ J w e = pointsInside (tagRoot e) C := rfl
    have db : Disjoint (J v e) (J w e) := (pair ne).preimage Subtype.val
    have da : Disjoint (I v e) (I w e) := by
      have h := imageCut_disjoint f (pair ne) (extraRow_disjoint ne)
      dsimp only [I]
      rw [show (a v).region = _ from imageEq v,show (a w).region = _ from imageEq w]
      exact h.preimage Subtype.val
    rw [changeAt,changeAt]
    exact edge_conservation _ _ _ _ (finDiff v e) (finDiff w e) da db (src.symm ▸ af) (dst.symm ▸ bf)
      (by rw [src,dst]; exact eq)
  · intro v
    rw [div]
    split <;> simp_all [delta]

def BranchRealization := ∀ (c : Baire) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ZeroDimensionalSpace X] [Countable (Clopens X)], GuardData (diagonalTree c) X →
    HasBranch (diagonalTree c) → Nonempty ((X ⊕ RootRow) ≃ₜ X)

theorem negativeResolution_of_chart_isolation_and_branch_realization
    (charts : ∀ c, ChartIsolation (diagonalTree c)) (realize : BranchRealization) : NegativeResolution :=
  negativeResolution_of_chart_isolation_and_absorption charts (fun c X _ _ _ _ _ G =>
    ⟨fun ⟨f⟩ => guarded_absorption_implies_branch G f,realize c X G⟩)

end BooleanScott
