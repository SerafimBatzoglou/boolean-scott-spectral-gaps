module
public import BooleanScott.ChartLedger
public import BooleanScott.Flow

/-! One finite multiset of tag roots explains both censuses on each
off-vertex fragment: it gives every tag's exact count and its total is the
eventual count in a ledger column. The comparison is preserved by actual
homeomorphisms and additive for arbitrary disjoint sums. -/
@[expose] public section
namespace BooleanScott
open Set Filter TopologicalSpace
open scoped OnePoint Classical

noncomputable def rootTotal {A : Type} [AddCommMonoid A] : (ℕ →₀ A) →+ A :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id A)

def HasLedgerBalance (x : SpaceType) := ∃ b : ℕ →₀ ℕ,
  (∀ e, (tagRoot e).count x = (b e : ℕ∞)) ∧ ∀ᶠ j : ℕ in atTop,
    (privateLocus (2*j)).count x = ((rootTotal b : ℕ) : ℕ∞)

theorem ledgerBalance_add {x y : SpaceType} (hx : HasLedgerBalance x) (hy : HasLedgerBalance y) :
    HasLedgerBalance (x+y) := by
  obtain ⟨b,tags,late⟩ := hx
  obtain ⟨c,tags',late'⟩ := hy
  refine ⟨b+c,fun e => ?_,?_⟩
  · simp only [map_add,tags,tags',Finsupp.add_apply,Nat.cast_add]
  · filter_upwards [late,late'] with j hj hj'
    rw [map_add,hj,hj',map_add,Nat.cast_add]

theorem row_clopen_balance (a n : ℕ) (C : Clopens (TagRow a n)) : HasLedgerBalance (spaceType C) := by
  let present : ℕ := if (∞ : TagRow a n) ∈ C then 1 else 0
  let b := Finsupp.single a present
  have total : rootTotal b = present := Finsupp.liftAddHom_apply_single _ _ _
  refine ⟨b,fun e => ?_,?_⟩
  · rw [LocalLocus.count_clopen,tagRoot_row]
    by_cases h : a=e
    · subst e
      simp only [ite_true,b,Finsupp.single_eq_same]
      by_cases hc : ∞ ∈ C
      · rw [inter_singleton_of_mem hc,encard_singleton]
        simp [present,hc]
      · rw [inter_singleton_eq_empty.mpr hc,encard_empty]
        simp [present,hc]
    · simp [h,b]
  · have stable : ∀ᶠ j in atTop, ledgerMarker a n j ∈ C ↔ ∞ ∈ C := by
      by_cases hc : ∞ ∈ C
      · filter_upwards [ledgerMarker_tendsto a n (C.isClopen.isOpen.mem_nhds hc)] with j hj using iff_of_true hj hc
      · filter_upwards [ledgerMarker_tendsto a n (C.isClopen.compl.isOpen.mem_nhds hc)] with j hj using iff_of_false hj hc
    filter_upwards [stable,eventually_ge_atTop n] with j hj le
    rw [LocalLocus.count_clopen,total]
    have eq : (privateLocus (2*j)).points (TagRow a n) = {ledgerMarker a n j} := Set.ext (fun p =>
      (row_ledger_points a n j p).trans (and_iff_right le))
    rw [eq]
    by_cases hc : ∞ ∈ C
    · rw [inter_singleton_of_mem (hj.mpr hc),encard_singleton]
      simp [present,hc]
    · rw [inter_singleton_eq_empty.mpr (fun h => hc (hj.mp h)),encard_empty]
      simp [present,hc]

theorem chart_clopen_balance {S : Set ℕ} (hn : S.Nonempty) (C : Clopens (VertexChart S)) (away : ∞ ∉ C) :
    HasLedgerBalance (spaceType C) := by
  classical
  obtain ⟨finite,late⟩ := chart_fragment_ledger hn C away
  let F := finite.toFinset
  let b : ℕ →₀ ℕ := ∑ r ∈ F, Finsupp.single r.1.val 1
  have total : rootTotal b = F.card := by
    simp [b,map_sum,rootTotal]
  refine ⟨b,fun e => ?_,?_⟩
  · rw [chart_tag_count]
    have eq : {r : ChartIndex S | r ∈ rootRows chartRoot (C : Set (VertexChart S)) ∧ r.1.val=e} =
        (F.filter (fun r => r.1.val=e) : Finset _) := by
      ext r
      simp [F]
    rw [eq]
    have co : b e = (F.filter (fun r => r.1.val=e)).card := by
      simp [b,Finset.sum_apply',Finsupp.single_apply]
    rw [co]
    exact encard_coe_eq_coe_finsetCard _
  · filter_upwards [late] with j hj
    rw [hj,total]
    exact finite.encard_eq_coe_toFinset_card

end BooleanScott
