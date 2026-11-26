module
public import BooleanScott.ChartTails

/-! Full row tails in two clopens of the same finite type are homeomorphic.
The root correspondence is chosen tag-by-tag. Ledger comparisons use exact
finite column counts and allow different cutoffs on corresponding rows. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

theorem countable_sets_equiv {I J : Type} [Countable I] [Countable J] {s : Set I} {t : Set J}
    (eq : s.encard = t.encard) : Nonempty (s ≃ t) := by
  classical
  by_cases hs : s.Finite
  · have ht := finite_of_encard_eq_coe (eq.symm.trans hs.encard_eq_coe_toFinset_card)
    let := hs.fintype
    let := ht.fintype
    exact ⟨Fintype.equivOfCardEq (by
      have sizes : s.ncard = t.ncard := congrArg ENat.toNat eq
      simpa using sizes)⟩
  · let := infinite_coe_iff.mpr hs
    let := infinite_coe_iff.mpr (encard_eq_top_iff.mp (eq.symm.trans (Infinite.encard_eq hs)))
    exact nonempty_equiv_of_countable

theorem retained_equiv {S : Set ℕ} (C E : Clopens (VertexChart S)) (same : SameFiniteClopens C E) :
    ∃ f : retainedRows C ≃ retainedRows E, ∀ r, (f r).val.1.val = r.val.1.val := by
  let tag (D : Clopens (VertexChart S)) (r : retainedRows D) := r.val.1.val
  have bij (e : ℕ) : Nonempty ({r // tag C r=e} ≃ {r // tag E r=e}) := by
    have h := same.count (tagRoot_finiteHit e)
    rw [chart_tag_count,chart_tag_count] at h
    obtain ⟨g⟩ := countable_sets_equiv h
    let flatten (D : Clopens (VertexChart S)) :=
      Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ retainedRows D) (fun r : ChartIndex S => r.1.val=e)
    exact ⟨((flatten C).trans g).trans (flatten E).symm⟩
  let g e := (bij e).some
  exact ⟨Equiv.ofFiberEquiv g,Equiv.ofFiberEquiv_map g⟩

namespace ChartTailSpec
variable {S : Set ℕ} {C : Clopens (VertexChart S)} (d : ChartTailSpec C)

abbrev cut (r : retainedRows C) := max d.threshold (rowStart r.val)

theorem finite_cut (j : ℕ) : {r : retainedRows C | d.cut r ≤ j}.Finite :=
  ((finite_ledger_rows S j).preimage Subtype.val_injective.injOn).subset
    fun q h => (le_max_right d.threshold (rowStart q.val)).trans h

theorem column (hn : S.Nonempty) (j : ℕ) (late : d.threshold ≤ j) :
    {r : retainedRows C | d.cut r ≤ j}.encard = (privateLocus (2*j)).count (spaceType C) := by
  rw [chart_ledger_count hn,← (Subtype.val_injective (p := fun r => r ∈ retainedRows C)).encard_image]
  apply congrArg Set.encard
  ext r
  have membership :
      packetInclusion ChartRow r (chartMarker r j) ∈ C ↔ r ∈ retainedRows C :=
    d.whole r (.inl (j-rowStart r)) (Nat.sub_le_sub_right late _) ∞
  constructor
  · rintro ⟨q,ok,rfl⟩
    have eligible := (le_max_right d.threshold (rowStart q.val)).trans (show d.cut q ≤ j from ok)
    exact ⟨eligible,membership.mpr q.property⟩
  · rintro ⟨ok,h⟩
    exact ⟨⟨r,membership.mp h⟩,max_le late ok,rfl⟩

theorem core_matches {E : Clopens (VertexChart S)} (a : ChartTailSpec C) (b : ChartTailSpec E)
    (hn : S.Nonempty) (same : SameFiniteClopens C E) (threshold : a.threshold = b.threshold) :
    spaceType a.core = spaceType b.core := by
  classical
  obtain ⟨f,tagEq⟩ := retained_equiv C E same
  have sizes (j : ℕ) : {r : retainedRows C | a.cut r ≤ j}.encard = {r : retainedRows E | b.cut r ≤ j}.encard := by
    by_cases le : a.threshold ≤ j
    · rw [a.column hn j le,b.column hn j (threshold ▸ le),same.count (private_finiteHit _)]
    · have empty (D : Clopens (VertexChart S)) (k : ChartTailSpec D) (lt : j < k.threshold) :
          {r : retainedRows D | k.cut r ≤ j} = ∅ := eq_empty_iff_forall_notMem.mpr (fun r h => lt.not_ge ((le_max_left ..).trans h))
      rw [empty C a (lt_of_not_ge le),empty E b (threshold ▸ lt_of_not_ge le),encard_empty,encard_empty]
  obtain ⟨h⟩ := match_row_arrays (fun r : retainedRows C => r.val.1.val) a.cut (b.cut ∘ f)
    a.finite_cut (fun j => (b.finite_cut j).preimage f.injective.injOn) (fun j => by
      apply congrArg ENat.toNat
      exact (sizes j).trans (encard_preimage_of_bijective f.bijective _).symm)
  have changeTag (e d k : ℕ) (eq : e=d) : TagRow e k ≃ₜ TagRow d k := by subst d; exact Homeomorph.refl _
  let g := sigmaFamilyCongr (X := fun r : retainedRows C => TagRow r.val.1.val (b.cut (f r)))
    (Y := fun r : retainedRows E => TagRow r.val.1.val (b.cut r)) f
    (fun r => changeTag _ _ _ (tagEq r).symm)
  rw [a.core_type,b.core_type]
  have bits : decide (∞ ∈ C) = decide (∞ ∈ E) := by simp only [chart_vertex_bit hn C E same]
  rw [bits]
  exact capped_congr _ (h.trans g)

end ChartTailSpec
end BooleanScott
