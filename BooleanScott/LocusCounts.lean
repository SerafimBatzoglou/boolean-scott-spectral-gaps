module
public import BooleanScott.TowerFragments
public import Mathlib.Data.Set.Card

/-! Counts of intrinsic local point predicates are additive invariants of
actual homeomorphism types. Counts can be infinite. The uppermost nonempty
derivative of a finite scattered tower has exactly one point. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped OnePoint

structure LocalLocus where
  points (X : Type) [TopologicalSpace X] : Set X
  restricts {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} :
    IsOpenEmbedding f → f ⁻¹' points Y = points X

def LocalLocus.stage (k : ℕ) (P : LocalLocus) : LocalLocus where
  points X _ := derivatives k (P.points X)
  restricts e := (local_derivatives e _ _).trans (congrArg (derivatives k) (P.restricts e))

def fullLocus : LocalLocus := ⟨fun _ _ => univ,fun _ => preimage_univ⟩
def isolatedClosureLocus : LocalLocus := ⟨fun X _ => scatteredLocus X,local_scatteredLocus⟩
def privateLocus (j : ℕ) : LocalLocus := ⟨fun X _ => privateMark X j,fun e => local_privateMark e j⟩

theorem LocalLocus.homeomorph_count (P : LocalLocus) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (P.points X).encard = (P.points Y).encard := by
  rw [← P.restricts e.isOpenEmbedding]
  exact encard_preimage_of_bijective e.bijective _

theorem LocalLocus.sum_count (P : LocalLocus) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    (P.points (X ⊕ Y)).encard = (P.points X).encard + (P.points Y).encard := by
  have split := image_preimage_inl_union_image_preimage_inr (P.points (X ⊕ Y))
  rw [P.restricts IsOpenEmbedding.inl,P.restricts IsOpenEmbedding.inr] at split
  rw [← split,encard_union_eq disjoint_image_inl_image_inr,Sum.inl_injective.encard_image,
    Sum.inr_injective.encard_image]

noncomputable def LocalLocus.count (P : LocalLocus) : SpaceType →+ ℕ∞ where
  toFun := Quotient.lift (fun X : TopCat.{0} => (P.points X).encard) (fun _ _ ⟨e⟩ => P.homeomorph_count e)
  map_zero' := by change (P.points Empty).encard = 0; simp [(P.points Empty).eq_empty_of_isEmpty]
  map_add' := by rintro ⟨X⟩ ⟨Y⟩; exact P.sum_count X Y

theorem LocalLocus.count_eval (P : LocalLocus) (X : Type) [TopologicalSpace X] :
    P.count (spaceType X) = (P.points X).encard := rfl

theorem tower_last (d : ℕ) : ∃ x : tower d, derivatives d univ = {x} := by
  cases d with
  | zero =>
    refine ⟨(),?_⟩
    change (univ : Set Unit) = {()}
    ext x; cases x; simp
  | succ d =>
    refine ⟨(∞ : Repeated (tower d)),?_⟩
    change derivatives (d+1) (univ : Set (Repeated (tower d))) = {∞}
    ext p
    induction p using OnePoint.rec with
    | infty => exact iff_of_true ((repeated_root d).mpr ((tower_height d d).mpr le_rfl)) rfl
    | coe p =>
      apply iff_of_false _ (OnePoint.coe_ne_infty _)
      intro hp
      have hin := (derivative_packet (fun _ : ℕ => (tower d : Type)) p.1 (d+1)).mp hp
      exact Nat.not_succ_le_self d ((tower_height d (d+1)).mp ⟨_,hin⟩)

def scatteredStage (k : ℕ) := isolatedClosureLocus.stage k

theorem tower_last_count (d : ℕ) : (scatteredStage d).count (towerType d) = 1 := by
  change (derivatives d (closure (isolatedPoints (tower d)))).encard = 1
  rw [tower_dense_isolated, encard_eq_one]
  exact tower_last d

theorem tower_later_count {d k : ℕ} (lt : d < k) : (scatteredStage k).count (towerType d) = 0 := by
  change (derivatives k (closure (isolatedPoints (tower d)))).encard = 0
  rw [tower_dense_isolated,encard_eq_zero,← not_nonempty_iff_eq_empty,tower_height]
  exact lt.not_ge

theorem cantor_scattered_count (k : ℕ) : (scatteredStage k).count cantorType = 0 := by
  change (derivatives k (closure (isolatedPoints CantorBits))).encard = 0
  rw [cantor_no_isolated,closure_empty,derivatives_empty,encard_empty]

theorem towerForm_determined {d : ℕ} {x y : SpaceType} (hx : TowerForm d x) (hy : TowerForm d y)
    (same : ∀ k ≤ d, (scatteredStage k).count x = (scatteredStage k).count y) : x = y := by
  have topcount (j m : ℕ) : (scatteredStage j).count (m • towerType j) = (m : ℕ∞) := by
    rw [map_nsmul,tower_last_count,nsmul_one]
  have later {j k : ℕ} (lt : j < k) (m : ℕ) : (scatteredStage k).count (m • towerType j) = 0 := by
    rw [map_nsmul,tower_later_count lt,nsmul_zero]
  rcases hx with rfl | ⟨i,hi,n,hn,rfl⟩ <;> rcases hy with rfl | ⟨j,hj,m,hm,rfl⟩
  · rfl
  · have h := same j hj
    rw [map_zero,topcount] at h
    exact False.elim ((Nat.cast_ne_zero.mpr hm.ne') h.symm)
  · have h := same i hi
    rw [map_zero,topcount] at h
    exact False.elim ((Nat.cast_ne_zero.mpr hn.ne') h)
  · rcases lt_trichotomy i j with lt | rfl | gt
    · have h := same j hj
      rw [later lt,topcount] at h
      exact False.elim ((Nat.cast_ne_zero.mpr hm.ne') h.symm)
    · have h := same i hi
      rw [topcount,topcount] at h
      congr 1
      exact_mod_cast h
    · have h := same i hi
      rw [topcount,later gt] at h
      exact False.elim ((Nat.cast_ne_zero.mpr hn.ne') h)

end BooleanScott
