module
public import BooleanScott.ChartTails

/-! The finite remainder after removing all retained row tails. Private
mark counts recover the multiplicity of each full mixed packet. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

noncomputable def mixedSum : (ℕ →₀ ℕ) →+ SpaceType :=
  Finsupp.liftAddHom (fun j => multiplesHom SpaceType (spaceType (Mixed j)))

theorem mixedSum_single (j n : ℕ) : mixedSum (Finsupp.single j n) = n • spaceType (Mixed j) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem private_count_mixed (j d : ℕ) : (privateLocus j).count (spaceType (Mixed d)) = if j=d then 1 else 0 := by
  change (privateMark _ _).encard = _
  rw [mixed_private_mark]
  split <;> simp

theorem private_count_sum (j : ℕ) (m : ℕ →₀ ℕ) : (privateLocus j).count (mixedSum m) = (m j : ℕ∞) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb]
  | single d n =>
    rw [mixedSum_single,map_nsmul,private_count_mixed]
    by_cases eq : j=d
    · subst d; simp
    · simp [eq,Finsupp.single_eq_of_ne eq]

theorem pure_mono {a b : ℕ} {x : SpaceType} (le : a ≤ b) (h : PureRemainder a x) : PureRemainder b x := by
  obtain ⟨c,t,hc,ht,eq⟩ := h
  refine ⟨c,t,hc,?_,eq⟩
  rcases ht with emp|⟨j,hj,n,hn,form⟩
  · exact Or.inl emp
  · exact Or.inr ⟨j,hj.trans le,n,hn,form⟩

theorem pure_zero (d : ℕ) : PureRemainder d 0 := ⟨0,0,Or.inl rfl,Or.inl rfl,(add_zero _).symm⟩

theorem private_count_pure {d : ℕ} {x : SpaceType} (h : PureRemainder d x) (j : ℕ) :
    (privateLocus j).count x = 0 := by
  obtain ⟨c,t,hc,ht,rfl⟩ := h
  have cant : (privateLocus j).count cantorType = 0 := by
    change (privateMark CantorBits j).encard = 0
    simp [privateMark,mixedBoundary,scatteredLocus,cantor_no_isolated]
  have towerC (k : ℕ) : (privateLocus j).count (towerType k) = 0 := by
    change (privateMark (tower k) j).encard = 0
    simp [privateMark,mixedBoundary,scatteredLocus,tower_dense_isolated]
  have tc : (privateLocus j).count t = 0 := by
    rcases ht with rfl|⟨k,_,n,_,rfl⟩
    · exact map_zero _
    · rw [map_nsmul,towerC,nsmul_zero]
  rw [map_add,tc,add_zero]
  rcases hc with rfl|rfl
  · exact map_zero _
  · exact cant

def LooseForm (x : SpaceType) : Prop :=
  ∃ (m : ℕ →₀ ℕ) (p : SpaceType) (d : ℕ), PureRemainder d p ∧ x = mixedSum m + p

theorem loose_zero : LooseForm 0 := ⟨0,0,0,pure_zero 0,by simp⟩

theorem loose_add {x y : SpaceType} (hx : LooseForm x) (hy : LooseForm y) : LooseForm (x+y) := by
  obtain ⟨m,p,a,hp,rfl⟩ := hx
  obtain ⟨n,q,b,hq,rfl⟩ := hy
  refine ⟨m+n,p+q,max a b,pureRemainder_add (pure_mono (le_max_left ..) hp) (pure_mono (le_max_right ..) hq),?_⟩
  rw [map_add]; ac_rfl

theorem loose_finset {I : Type} (s : Finset I) (x : I → SpaceType) (h : ∀ i ∈ s, LooseForm (x i)) :
    LooseForm (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loose_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact loose_add (h _ (Finset.mem_insert_self ..)) (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem loose_mixed_clopen (d : ℕ) (C : Clopens (Mixed d)) : LooseForm (spaceType C) := by
  by_cases root : ∞ ∈ C
  · refine ⟨Finsupp.single d 1,0,0,pure_zero 0,?_⟩
    rw [mixedSum_single,one_smul,add_zero,(mixed_clopen_form d C).1 root]
  · exact ⟨0,spaceType C,d,(mixed_clopen_form d C).2 root,by simp⟩

theorem loose_row {a n : ℕ} (C : Clopens (TagRow a n)) (away : ∞ ∉ C) : LooseForm (spaceType C) := by
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket a n i) := (mixed_stone _).1
  obtain ⟨F,eq⟩ := array_fragment_away (RowPacket a n) C away
  rw [eq]
  exact loose_finset _ _ (fun i _ => loose_mixed_clopen _ _)

theorem loose_chart {S : Set ℕ} (C : Clopens (VertexChart S)) (away : ∞ ∉ C)
    (rows : ∀ r : ChartIndex S, packetInclusion ChartRow r ∞ ∉ C) : LooseForm (spaceType C) := by
  let ht (r : ChartIndex S) : T2Space (ChartRow r) := (row_stone _ _).1
  obtain ⟨F,eq⟩ := array_fragment_away ChartRow C away
  rw [eq]
  exact loose_finset _ _ (fun r _ => loose_row _ (rows r))

theorem ChartTailSpec.remainder {S : Set ℕ} {C : Clopens (VertexChart S)} (d : ChartTailSpec C) :
    LooseForm (spaceType (C \ d.core : Clopens (VertexChart S))) :=
  loose_chart _ (fun h => h.2 (d.core_vertex.mpr h.1)) (fun r h => h.2 ((d.core_root r).mpr h.1))

end BooleanScott
