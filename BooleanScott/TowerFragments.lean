module
public import BooleanScott.SpaceTypes
public import BooleanScott.CantorScott

/-! Exact upper normal forms for clopens of the finite scattered towers and
the mixed packets. The listed equalities are equalities of homeomorphism types.
The multiplicity of the largest tower is retained, including in a root-free
fragment that has no infinite supply of ledger packets. -/
@[expose] public section
namespace BooleanScott
open TopologicalSpace Topology Set
open scoped OnePoint Classical

noncomputable def towerType (j : ℕ) := spaceType (tower j)

def TowerForm (d : ℕ) (x : SpaceType) : Prop :=
  x = 0 ∨ ∃ j ≤ d, ∃ m : ℕ, 0 < m ∧ x = m • towerType j

theorem absorb_multiple {x y : SpaceType} (h : x + y = x) (r : ℕ) :
    x + r • y = x := by
  induction r with
  | zero => simp
  | succ r ih => rw [succ_nsmul,← add_assoc,ih,h]

theorem absorb_both_multiples {x y : SpaceType} (h : x+y=x) (n r : ℕ) (hn : 0 < n) :
    n • x + r • y = n • x := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [succ_nsmul,add_assoc,absorb_multiple h]

theorem towerForm_add {d : ℕ} {x y : SpaceType} (hx : TowerForm d x) (hy : TowerForm d y) :
    TowerForm d (x+y) := by
  rcases hx with rfl | ⟨i,hi,n,hn,rfl⟩
  · simpa using hy
  rcases hy with rfl | ⟨j,hj,m,hm,rfl⟩
  · exact Or.inr ⟨i,hi,n,hn,add_zero _⟩
  rcases lt_trichotomy i j with less | rfl | gt
  · refine Or.inr ⟨j,hj,m,hm,?_⟩
    rw [add_comm]
    exact absorb_both_multiples (spaceType_absorbs.mpr (tower_absorbs_lower less)) _ _ hm
  · exact Or.inr ⟨i,hi,n+m,by omega,(add_nsmul ..).symm⟩
  · exact Or.inr ⟨i,hi,n,hn,absorb_both_multiples (spaceType_absorbs.mpr (tower_absorbs_lower gt)) _ _ hn⟩

theorem towerForm_mono {d e : ℕ} {x : SpaceType} (le : d ≤ e) (h : TowerForm d x) : TowerForm e x := by
  rcases h with h | ⟨j,hj,m,hm,eq⟩
  · exact Or.inl h
  · exact Or.inr ⟨j,hj.trans le,m,hm,eq⟩

theorem towerForm_list {X : Type} [TopologicalSpace X] {d : ℕ} (l : List (Clopens X))
    (h : ∀ C ∈ l, TowerForm d (spaceType C)) : TowerForm d (l.map (fun C : Clopens X => spaceType C)).sum := by
  induction l with
  | nil => exact Or.inl rfl
  | cons C l ih =>
    exact towerForm_add (h C List.mem_cons_self) (ih (fun D hd => h D (List.mem_cons_of_mem _ hd)))

theorem tower_clopen_form (d : ℕ) (C : Clopens (tower d)) : TowerForm d (spaceType C) := by
  induction d with
  | zero =>
    let : Subsingleton (tower 0) := (inferInstance : Subsingleton Unit)
    by_cases h : (C : Set (tower 0)).Nonempty
    · have full (x : tower 0) : x ∈ C := (Subsingleton.elim h.choose x) ▸ h.choose_spec
      exact Or.inr ⟨0,le_rfl,1,by decide,(univ_clopen_spaceType full).trans (one_nsmul _).symm⟩
    · let : IsEmpty C := ⟨fun x => h ⟨x,x.property⟩⟩
      exact Or.inl (empty_spaceType C)
  | succ d ih =>
    have next (C : Clopens (Repeated (tower d))) : TowerForm (d+1) (spaceType C) := by
      obtain ⟨l,eq⟩ := spaceType_fragment C
      rw [eq]
      apply towerForm_add
      · split
        · exact Or.inr ⟨d+1,le_rfl,1,by decide,(one_nsmul _).symm⟩
        · exact Or.inl rfl
      · exact towerForm_mono (Nat.le_succ d) (towerForm_list l (fun C _ => ih C))
    exact next C

def cantorType := spaceType CantorBits

theorem cantorType_idem : cantorType + cantorType = cantorType := by
  let := cantor_countable_clopens
  let := (sumClopensIso (X := CantorBits) (Y := CantorBits)).injective.countable
  let := sum_zeroDimensional CantorBits CantorBits
  have none : isolatedPoints (CantorBits ⊕ CantorBits) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p
    cases p with
    | inl x =>
      have h := local_isolated (IsOpenEmbedding.inl (X := CantorBits) (Y := CantorBits))
      rw [cantor_no_isolated] at h
      exact fun hx => (Set.ext_iff.mp h x).mp hx
    | inr y =>
      have h := local_isolated (IsOpenEmbedding.inr (X := CantorBits) (Y := CantorBits))
      rw [cantor_no_isolated] at h
      exact fun hy => (Set.ext_iff.mp h y).mp hy
  obtain ⟨e⟩ := splitting_clopens_iso (splits_of_no_isolated _ none) (splits_of_no_isolated _ cantor_no_isolated)
  exact (spaceType_eq_iff _ _).mpr ⟨homeomorphOfClopens e⟩

def PureRemainder (d : ℕ) (x : SpaceType) : Prop :=
  ∃ c t : SpaceType, (c = 0 ∨ c = cantorType) ∧ TowerForm d t ∧ x = c+t

theorem pureRemainder_add {d : ℕ} {x y : SpaceType} (hx : PureRemainder d x) (hy : PureRemainder d y) :
    PureRemainder d (x+y) := by
  obtain ⟨a,t,ha,ht,rfl⟩ := hx
  obtain ⟨b,u,hb,hu,rfl⟩ := hy
  refine ⟨a+b,t+u,?_,towerForm_add ht hu,by ac_rfl⟩
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp [cantorType_idem]

theorem mixed_piece_form (d : ℕ) (C : Clopens (CantorBits ⊕ (tower d : Type))) :
    PureRemainder d (spaceType C) := by
  let U := clopenPreimage continuous_inl C
  let V := clopenPreimage continuous_inr C
  refine ⟨spaceType U,spaceType V,?_,tower_clopen_form d V,(spaceType_eq_iff _ _).mpr ⟨(splitSubspace C).symm⟩⟩
  by_cases hn : (U : Set CantorBits).Nonempty
  · exact Or.inr ((spaceType_eq_iff _ _).mpr (cantor_nonempty_clopen U hn))
  · let : IsEmpty U := ⟨fun x => hn ⟨x,x.property⟩⟩
    exact Or.inl (empty_spaceType U)

theorem mixed_absorbs_remainder {d : ℕ} {r : SpaceType} (h : PureRemainder d r) :
    spaceType (Mixed d) + r = spaceType (Mixed d) := by
  obtain ⟨c,t,hc,ht,rfl⟩ := h
  have absorbC : spaceType (Mixed d) + c = spaceType (Mixed d) := by
    rcases hc with rfl|rfl
    · exact add_zero _
    · exact spaceType_absorbs.mpr (mixed_absorbs_cantor _)
  rw [← add_assoc,absorbC]
  rcases ht with rfl | ⟨j,hj,m,_,rfl⟩
  · exact add_zero _
  · exact absorb_multiple (spaceType_absorbs.mpr (mixed_absorbs_tower _ _ hj)) m

theorem mixed_clopen_form (d : ℕ) (C : Clopens (Mixed d)) :
    (∞ ∈ C → spaceType C = spaceType (Mixed d)) ∧
    (∞ ∉ C → PureRemainder d (spaceType C)) := by
  obtain ⟨l,eq⟩ := spaceType_fragment C
  have pure : PureRemainder d (l.map (fun D : Clopens (CantorBits ⊕ (tower d : Type)) => spaceType D)).sum := by
    clear eq
    induction l with
    | nil => exact ⟨0,0,Or.inl rfl,Or.inl rfl,(zero_add _).symm⟩
    | cons D l ih => exact pureRemainder_add (mixed_piece_form d D) ih
  constructor
  · intro h
    rw [eq,ite_eq_left h]
    exact mixed_absorbs_remainder pure
  · intro h
    rw [eq,ite_eq_right h,zero_add]
    exact pure

end BooleanScott
