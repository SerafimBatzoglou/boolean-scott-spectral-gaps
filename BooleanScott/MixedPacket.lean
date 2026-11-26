module
public import BooleanScott.ScatteredTowers

/-! An explicit alternative supply of private topological markers.
The compactification has a Cantor piece and a finite-height scattered
piece in each slot. The two closed loci used to recognize its unique
mixed point and its finite height are invariant under open embeddings. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology
open scoped OnePoint

abbrev CantorBits := ℕ → Bool

theorem cantor_no_isolated : isolatedPoints CantorBits = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hx
  apply accPt_iff_nhds.mpr
  let f (n i : ℕ) := if i = n then !(x i) else x i
  have conv : Tendsto f atTop (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn using (ite_eq_right hn.ne).symm
  intro U hU
  obtain ⟨n,hn⟩ := (conv.eventually hU).exists
  refine ⟨f n,⟨hn,trivial⟩,?_⟩
  intro eq
  have hn := congrFun eq n
  cases hb : x n <;> simp [f,hb] at hn

abbrev Mixed (d : ℕ) := Repeated (CantorBits ⊕ (tower d : Type))

def cantorSide (d n : ℕ) : CantorBits → Mixed d :=
  packetInclusion (fun _ : ℕ => CantorBits ⊕ (tower d : Type)) n ∘ Sum.inl

def towerSide (d n : ℕ) : tower d → Mixed d :=
  packetInclusion (fun _ : ℕ => CantorBits ⊕ (tower d : Type)) n ∘ Sum.inr

theorem cantorSide_open (d n : ℕ) : IsOpenEmbedding (cantorSide d n) :=
  (open_packetInclusion _ _).comp .inl

theorem towerSide_open (d n : ℕ) : IsOpenEmbedding (towerSide d n) :=
  (open_packetInclusion _ _).comp .inr

def scatteredLocus (X : Type) [TopologicalSpace X] := closure (isolatedPoints X)

def mixedBoundary (X : Type) [TopologicalSpace X] : Set X :=
  scatteredLocus X ∩ closure (scatteredLocus X)ᶜ

theorem local_scatteredLocus {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (e : IsOpenEmbedding f) :
    f ⁻¹' scatteredLocus Y = scatteredLocus X := by
  rw [scatteredLocus, e.isOpenMap.preimage_closure_eq_closure_preimage e.continuous,local_isolated e]
  rfl

theorem local_mixedBoundary {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (e : IsOpenEmbedding f) :
    f ⁻¹' mixedBoundary Y = mixedBoundary X := by
  simp only [mixedBoundary,preimage_inter,e.isOpenMap.preimage_closure_eq_closure_preimage e.continuous,
    preimage_compl,local_scatteredLocus e]

theorem cantorSide_scattered (d n : ℕ) : cantorSide d n ⁻¹' scatteredLocus (Mixed d) = ∅ := by
  rw [local_scatteredLocus (cantorSide_open d n),scatteredLocus,cantor_no_isolated,closure_empty]

theorem towerSide_scattered (d n : ℕ) : towerSide d n ⁻¹' scatteredLocus (Mixed d) = univ :=
  (local_scatteredLocus (towerSide_open d n)).trans (tower_dense_isolated d)

theorem mixedBoundary_singleton (d : ℕ) : mixedBoundary (Mixed d) = {∞} := by
  let D := scatteredLocus (Mixed d)
  have full (S : Set (Mixed d)) (h : ∀ i : ℕ, ∃ x, packetInclusion _ i x ∈ S) :
      (∞ : Mixed d) ∈ closure S := by
    apply derivedSet_subset_closure
    apply (infty_in_derived_iff S).mpr
    exact (eq_univ_of_forall h : occupied S = univ) ▸ infinite_univ
  have at_root : (∞ : Mixed d) ∈ mixedBoundary (Mixed d) := by
    constructor
    · apply isClosed_closure.closure_subset
      apply full D
      intro i
      obtain ⟨x,_⟩ := (tower_height d 0).mpr (Nat.zero_le _)
      exact ⟨Sum.inr x,(Set.ext_iff.mp (towerSide_scattered d i) x).mpr trivial⟩
    · apply full Dᶜ
      intro i
      let x : CantorBits := fun _ => false
      exact ⟨Sum.inl x,fun hx => (Set.ext_iff.mp (cantorSide_scattered d i) x).mp hx⟩
  ext p
  induction p using OnePoint.rec with
  | infty => exact iff_of_true at_root rfl
  | coe p =>
    rcases p with ⟨i,x | y⟩
    · exact iff_of_false (fun hb => (Set.ext_iff.mp (cantorSide_scattered d i) x).mp hb.1)
        (OnePoint.coe_ne_infty _)
    · have empty : towerSide d i ⁻¹' closure Dᶜ = ∅ := by
        rw [(towerSide_open d i).isOpenMap.preimage_closure_eq_closure_preimage (towerSide_open d i).continuous,
          preimage_compl,towerSide_scattered,compl_univ,closure_empty]
      exact iff_of_false (fun hb => (Set.ext_iff.mp empty y).mp hb.2) (OnePoint.coe_ne_infty _)

theorem derivatives_empty {X : Type} [TopologicalSpace X] (k : ℕ) : derivatives k (∅ : Set X) = ∅ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [derivatives_succ,ih]
    exact subset_empty_iff.mp ((derivedSet_subset_closure _).trans (by simp))

theorem mixed_root_height (d k : ℕ) :
    (∞ : Mixed d) ∈ derivatives (k+1) (scatteredLocus (Mixed d)) ↔ k ≤ d := by
  let D := scatteredLocus (Mixed d)
  have left (i : ℕ) : cantorSide d i ⁻¹' derivatives k D = ∅ := by
    rw [local_derivatives (cantorSide_open d i),cantorSide_scattered,derivatives_empty]
  have right (i : ℕ) : towerSide d i ⁻¹' derivatives k D = derivatives k univ := by
    rw [local_derivatives (towerSide_open d i),towerSide_scattered]
  rw [derivatives_succ,infty_in_derived_iff]
  constructor
  · intro h
    obtain ⟨i,x|y,hx⟩ := h.nonempty
    · exact ((Set.ext_iff.mp (left i) x).mp hx).elim
    · exact (tower_height d k).mp ⟨y,(Set.ext_iff.mp (right i) y).mp hx⟩
  · intro h
    obtain ⟨y,hy⟩ := (tower_height d k).mpr h
    have all : occupied (derivatives k D) = univ := eq_univ_of_forall (fun i =>
      ⟨Sum.inr y,(Set.ext_iff.mp (right i) y).mpr hy⟩)
    exact all ▸ infinite_univ

def privateMark (X : Type) [TopologicalSpace X] (j : ℕ) :=
  mixedBoundary X ∩ (derivatives (j+1) (scatteredLocus X) \ derivatives (j+2) (scatteredLocus X))

theorem mixed_private_mark (d j : ℕ) : privateMark (Mixed d) j = if j=d then {∞} else ∅ := by
  ext p
  simp only [privateMark,mem_inter_iff,mixedBoundary_singleton,mem_singleton_iff,Set.mem_sdiff]
  by_cases hp : p = ∞
  · subst p
    have next : (∞ : Mixed d) ∈ derivatives (j+2) (scatteredLocus (Mixed d)) ↔ j+1 ≤ d :=
      mixed_root_height d (j+1)
    simp only [next,mixed_root_height,true_and]
    by_cases hj : j=d <;> simp [hj]
    omega
  · by_cases hj : j=d <;> simp [hj,hp]

theorem local_privateMark {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (e : IsOpenEmbedding f) (j : ℕ) :
    f ⁻¹' privateMark Y j = privateMark X j := by
  simp only [privateMark,preimage_inter,preimage_sdiff,local_mixedBoundary e,local_derivatives e,
    local_scatteredLocus e]

theorem mixed_open_embedding_index {d j : ℕ} {f : Mixed d → Mixed j} (e : IsOpenEmbedding f) :
    d = j := by
  have root : (∞ : Mixed d) ∈ privateMark (Mixed d) d := by simp [mixed_private_mark]
  have inside : f ∞ ∈ privateMark (Mixed j) d := (Set.ext_iff.mp (local_privateMark e d) ∞).mpr root
  by_contra diff
  simp [mixed_private_mark,diff] at inside

end BooleanScott
