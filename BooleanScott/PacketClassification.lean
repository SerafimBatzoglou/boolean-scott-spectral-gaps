module
public import BooleanScott.LocusCounts

/-! The counts needed to compare arbitrary clopens in a single mixed packet.
A test at stage d+1 distinguishes an apex-containing clopen. In its absence
the scattered counts determine the finite tower remainder and the ordinary
derivative at d+1 records whether a Cantor summand is present. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped OnePoint

theorem LocalLocus.count_clopen (P : LocalLocus) {X : Type} [TopologicalSpace X] (C : Clopens X) :
    P.count (spaceType C) = ((C : Set X) ∩ P.points X).encard := by
  have e : IsOpenEmbedding (fun a : C => (a : X)) := C.isClopen.isOpen.isOpenEmbedding_subtypeVal
  rw [P.count_eval, ← P.restricts e,
    ← (Subtype.val_injective (p := fun x => x ∈ C)).encard_image, image_preimage_eq_inter_range,
    Subtype.range_coe_subtype,inter_comm]
  rfl

def ordinaryStage (k : ℕ) := fullLocus.stage k

theorem ordinary_tower (k j : ℕ) : (ordinaryStage k).count (towerType j) = (scatteredStage k).count (towerType j) := by
  change (derivatives k univ).encard = (derivatives k (closure (isolatedPoints (tower j)))).encard
  rw [tower_dense_isolated]

theorem cantor_ordinary_nonzero (k : ℕ) : (ordinaryStage k).count cantorType ≠ 0 := by
  have perfect : derivedSet (univ : Set CantorBits) = univ := by
    apply compl_injective
    simpa only [compl_univ,isolatedPoints] using cantor_no_isolated
  have all : derivatives k (univ : Set CantorBits) = univ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [derivatives_succ,ih,perfect]
  change (derivatives k (univ : Set CantorBits)).encard ≠ 0
  rw [all,ne_eq,encard_eq_zero]
  exact univ_nonempty.ne_empty

theorem towerForm_later {d k : ℕ} {x : SpaceType} (h : TowerForm d x) (late : d < k) :
    (scatteredStage k).count x = 0 ∧ (ordinaryStage k).count x = 0 := by
  rcases h with rfl | ⟨j,hj,m,_,rfl⟩
  · simp
  · simp only [map_nsmul, ordinary_tower,tower_later_count (hj.trans_lt late),nsmul_zero,and_self]

theorem pureRemainder_later {d : ℕ} {x : SpaceType} (h : PureRemainder d x) :
    (scatteredStage (d+1)).count x = 0 := by
  obtain ⟨c,t,hc,ht,rfl⟩ := h
  rw [map_add,(towerForm_later ht (Nat.lt_succ_self _)).1,add_zero]
  rcases hc with rfl|rfl
  · exact map_zero _
  · exact cantor_scattered_count _

theorem pureRemainder_determined {d : ℕ} {x y : SpaceType} (hx : PureRemainder d x) (hy : PureRemainder d y)
    (same : ∀ k ≤ d, (scatteredStage k).count x = (scatteredStage k).count y)
    (ord : (ordinaryStage (d+1)).count x = (ordinaryStage (d+1)).count y) : x=y := by
  obtain ⟨c,t,hc,ht,rfl⟩ := hx
  obtain ⟨b,u,hb,hu,rfl⟩ := hy
  have zeroC {a : SpaceType} (h : a=0 ∨ a=cantorType) (k : ℕ) : (scatteredStage k).count a = 0 := by
    rcases h with rfl|rfl
    · exact map_zero _
    · exact cantor_scattered_count _
  have eq := towerForm_determined ht hu (fun k hk => by simpa only [map_add,zeroC hc,zeroC hb,zero_add] using same k hk)
  rw [map_add,map_add,(towerForm_later ht (Nat.lt_succ_self _)).2,(towerForm_later hu (Nat.lt_succ_self _)).2,
    add_zero,add_zero] at ord
  have ceq : c = b := by
    rcases hc with rfl|rfl <;> rcases hb with rfl|rfl
    · rfl
    · exact False.elim (cantor_ordinary_nonzero _ (ord.symm.trans (map_zero _)))
    · exact False.elim (cantor_ordinary_nonzero _ (ord.trans (map_zero _)))
    · rfl
  rw [ceq,eq]

theorem mixed_clopens_determined (d : ℕ) (C E : Clopens (Mixed d))
    (same : ∀ k ≤ d+1, (scatteredStage k).count (spaceType C) = (scatteredStage k).count (spaceType E))
    (ord : (ordinaryStage (d+1)).count (spaceType C) = (ordinaryStage (d+1)).count (spaceType E)) :
    Nonempty (C ≃ₜ E) := by
  have pos : (scatteredStage (d+1)).count (spaceType (Mixed d)) ≠ 0 := by
    change (derivatives (d+1) (scatteredLocus (Mixed d))).encard ≠ 0
    rw [ne_eq,encard_eq_zero]
    apply Set.Nonempty.ne_empty
    exact ⟨∞,(mixed_root_height d d).mpr le_rfl⟩
  apply (spaceType_eq_iff _ _).mp
  have top := same (d+1) le_rfl
  by_cases hc : ∞ ∈ C <;> by_cases he : ∞ ∈ E
  · exact ((mixed_clopen_form d C).1 hc).trans ((mixed_clopen_form d E).1 he).symm
  · rw [(mixed_clopen_form d C).1 hc,pureRemainder_later ((mixed_clopen_form d E).2 he)] at top
    exact (pos top).elim
  · rw [(mixed_clopen_form d E).1 he,pureRemainder_later ((mixed_clopen_form d C).2 hc)] at top
    exact (pos top.symm).elim
  · exact pureRemainder_determined ((mixed_clopen_form d C).2 hc) ((mixed_clopen_form d E).2 he)
      (fun k hk => same k (hk.trans (Nat.le_succ _))) ord

end BooleanScott
