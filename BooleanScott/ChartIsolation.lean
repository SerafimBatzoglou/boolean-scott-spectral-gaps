module
public import BooleanScott.CoreAbsorption
public import BooleanScott.AbsorptionNecessity

/-! Pure Π_(ω+2) Scott sentences for the actual vertex charts. This
discharges chart isolation, including the uniform Borel guard consequences. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace Descriptive
open scoped Classical OnePoint Ordinal

theorem add_finset_congr_base {I : Type} {A : Type*} [AddCommMonoid A] (s : Finset I) (b : A) (f g : I → A)
    (eq : ∀ i ∈ s, b+f i=b+g i) : b+∑ i ∈ s, f i = b+∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,← add_assoc,eq i (Finset.mem_insert_self ..)]
    have old := ih (fun k hk => eq k (Finset.mem_insert_of_mem hk))
    calc
      b+g i+∑ k ∈ s, f k = (b+∑ k ∈ s, f k)+g i := by ac_rfl
      _ = (b+∑ k ∈ s, g k)+g i := congrArg (·+g i) old
      _ = _ := by ac_rfl

theorem mixedSum_match (b : SpaceType) (m n : ℕ →₀ ℕ)
    (compare : ∀ j, m j=n j ∨ b+spaceType (Mixed j)=b) : b+mixedSum m=b+mixedSum n := by
  classical
  let s := m.support ∪ n.support
  have expand (a : ℕ →₀ ℕ) (sub : a.support ⊆ s) : mixedSum a = ∑ i ∈ s, a i • spaceType (Mixed i) := by
    change a.sum (fun i k => k • spaceType (Mixed i)) = _
    exact Finsupp.sum_of_support_subset a sub _ (fun _ _ => zero_smul ..)
  rw [expand m Finset.subset_union_left,expand n Finset.subset_union_right]
  apply add_finset_congr_base
  intro j _
  rcases compare j with eq|abs
  · rw [eq]
  · exact (absorb_multiple abs _).trans (absorb_multiple abs _).symm

theorem rooted_chart_comparison {S : Set ℕ} (hn : S.Nonempty) (C E : Clopens (VertexChart S))
    (same : SameFiniteClopens C E) (root : retainedRows C) : spaceType C = spaceType E := by
  classical
  let := (chart_stone S).1
  obtain ⟨a₀⟩ := chart_tail_spec C
  obtain ⟨b₀⟩ := chart_tail_spec E
  let a := a₀.raise _ (le_max_left a₀.threshold b₀.threshold)
  let b := b₀.raise _ (le_max_right a₀.threshold b₀.threshold)
  have cores := a.core_matches b hn same rfl
  obtain ⟨f,_⟩ := retained_equiv C E same
  obtain ⟨m,p,i,hp,formA⟩ := a.remainder
  obtain ⟨n,q,k,hq,formB⟩ := b.remainder
  have left : spaceType C = spaceType a.core + mixedSum m := by
    rw [split_subclopen a.core_subset,formA]
    calc
      spaceType a.core+(mixedSum m+p) = (spaceType a.core+p)+mixedSum m := by ac_rfl
      _ = _ := congrArg (·+mixedSum m) (a.core_absorbs_pure root hp)
  have right : spaceType E = spaceType b.core + mixedSum n := by
    rw [split_subclopen b.core_subset,formB]
    calc
      spaceType b.core+(mixedSum n+q) = (spaceType b.core+q)+mixedSum n := by ac_rfl
      _ = _ := congrArg (·+mixedSum n) (b.core_absorbs_pure (f root) hq)
  have finite_equal (j : ℕ) (finite : (privateLocus j).count (spaceType a.core) ≠ ⊤) : m j=n j := by
    have sameCount := same.count (private_finiteHit j)
    rw [left,right,map_add,map_add,← cores,private_count_sum,private_count_sum] at sameCount
    exact_mod_cast (ENat.add_right_injective_of_ne_top finite sameCount)
  rw [left,right,← cores]
  apply mixedSum_match
  intro j
  by_cases even : j%2=0
  · have eq : j=2*(j/2) := by omega
    refine Or.inl (finite_equal j ?_)
    rw [eq,LocalLocus.count_clopen]
    exact (chart_ledger_finite hn a.core (j/2)).encard_lt_top.ne
  · let e := j/2
    have eq : j=2*e+1 := by dsimp [e]; omega
    by_cases has : ∃ r : retainedRows C, r.val.1.val=e
    · obtain ⟨r,hr⟩ := has
      rw [eq,← hr]
      exact Or.inr (a.core_absorbs_tag r)
    · refine Or.inl (finite_equal j ?_)
      rw [eq,a.core_missing_odd hn (fun r hr => has ⟨r,hr⟩)]
      exact ENat.natCast_ne_top 0

theorem chart_clopens_determined {S : Set ℕ} (hn : S.Nonempty) (C E : Clopens (VertexChart S))
    (same : SameFiniteClopens C E) : Nonempty (C ≃ₜ E) := by
  by_cases has : (retainedRows C).Nonempty
  · obtain ⟨r,hr⟩ := has
    exact (spaceType_eq_iff _ _).mp (rooted_chart_comparison hn C E same ⟨r,hr⟩)
  · have away : ∞ ∉ C := by
      intro here
      obtain ⟨F,tail⟩ := cofinite_components_of_nhds (C.isClopen.isOpen.mem_nhds here)
      obtain ⟨e,he⟩ := hn
      obtain ⟨r,_,hr⟩ := ((infinity_of_tag_rows S e).mpr he).exists_notMem_finset F
      exact has ⟨r,tail r hr ∞⟩
    exact chart_root_free_comparison C E same away (fun r h => has ⟨r,h⟩)

theorem vertex_chart_scott {S : Set ℕ} (hn : S.Nonempty) :
    ∃ σ : Formula 0, AtLevel .pi (ω+2) σ ∧ ∀ (B : Type) [Countable B] [BooleanAlgebra B],
      Models (BoolOps.ofAlgebra B) σ ↔ Nonempty (Clopens (VertexChart S) ≃o B) := by
  obtain ⟨ht,hz,hc⟩ := chart_stone S
  apply chartScott_of_finite_types
  intro n v w same
  exact clopen_tuple_of_signs v w (fun p => chart_clopens_determined hn _ _ (sameFiniteClopens_of_tuple v w same p))

theorem chart_isolation (T : tree ℕ) : ChartIsolation T := fun v => vertex_chart_scott (sectorTags_nonempty T v)

theorem negativeResolution_of_branch_realization (realize : BranchRealization) : NegativeResolution :=
  negativeResolution_of_chart_isolation_and_branch_realization (fun _ => chart_isolation _) realize

end BooleanScott
