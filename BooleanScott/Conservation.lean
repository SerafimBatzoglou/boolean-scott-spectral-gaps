module
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-! Signed net changes of infinite charts. Only their differences are counted.
Two charts on the same side must be disjoint. The source and target charts
may overlap arbitrarily, including transfers between different endpoints. -/
@[expose] public section
namespace BooleanScott
open Set

variable {α : Type*}

def differenceSupport (A B : Set α) := (A \ B) ∪ (B \ A)

noncomputable def netChange (A B : Set α) : ℤ :=
  ((A \ B).ncard : ℤ) - (B \ A).ncard

noncomputable def mark (A : Set α) (x : α) : ℤ := by
  classical exact if x ∈ A then 1 else 0

private theorem sum_mark (A : Set α) (F : Finset α) (h : A ⊆ F) :
    ∑ x ∈ F, mark A x = A.ncard := by
  classical
  have same : ((F.filter (· ∈ A) : Finset α) : Set α) = A := by
    ext x
    simp only [Finset.coe_filter, mem_ofPred_eq]
    exact ⟨And.right,fun hx => ⟨h hx,hx⟩⟩
  simp only [mark, Finset.sum_boole]
  exact_mod_cast ((ncard_coe_finset _).symm.trans (congrArg Set.ncard same))

theorem netChange_eq_sum (A B : Set α) (F : Finset α) (h : differenceSupport A B ⊆ F) :
    netChange A B = ∑ x ∈ F, (mark A x - mark B x) := by
  have pointwise (x : α) : mark A x - mark B x = mark (A \ B) x - mark (B \ A) x := by
    classical
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [mark,ha,hb]
  simp_rw [pointwise]
  rw [Finset.sum_sub_distrib, sum_mark _ _ (union_subset_iff.mp h).1,
    sum_mark _ _ (union_subset_iff.mp h).2]
  rfl

/-- Separate finite chart differences add even if points switch chart names. -/
theorem netChange_union (A B C D : Set α)
    (hab : (differenceSupport A B).Finite) (hcd : (differenceSupport C D).Finite)
    (src : Disjoint A C) (dst : Disjoint B D) :
    netChange (A ∪ C) (B ∪ D) = netChange A B + netChange C D := by
  classical
  let F := (hab.union hcd).toFinset
  have hset : (F : Set α) = differenceSupport A B ∪ differenceSupport C D :=
    Set.Finite.coe_toFinset _
  have hu : differenceSupport (A ∪ C) (B ∪ D) ⊆ F := by
    rw [hset]
    unfold differenceSupport
    intro x
    simp only [mem_union, mem_sdiff]
    tauto
  have h1 : differenceSupport A B ⊆ F := hset ▸ subset_union_left
  have h2 : differenceSupport C D ⊆ F := hset ▸ subset_union_right
  rw [netChange_eq_sum _ _ F hu, netChange_eq_sum _ _ F h1, netChange_eq_sum _ _ F h2,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hAC : x ∈ A → x ∈ C → False := fun hp => Set.disjoint_left.mp src hp
  have hBD : x ∈ B → x ∈ D → False := fun hp => Set.disjoint_left.mp dst hp
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> by_cases hc : x ∈ C <;> by_cases hd : x ∈ D <;>
    simp_all [mark]

/-- For a single tag take α to be the subtype of all its roots. The signed
excess inside equals the excess of target exterior over source exterior. -/
theorem netChange_finite_exteriors (A B : Set α) (ha : Aᶜ.Finite) (hb : Bᶜ.Finite) :
    netChange A B = (Bᶜ.ncard : ℤ) - Aᶜ.ncard := by
  classical
  let F := (ha.union hb).toFinset
  have heq : (F : Set α) = Aᶜ ∪ Bᶜ := Set.Finite.coe_toFinset _
  have hc : differenceSupport A B ⊆ F := by
    rw [heq]
    intro x hx
    rcases hx with ⟨_,hn⟩ | ⟨_,hn⟩
    · exact Or.inr hn
    · exact Or.inl hn
  have h1 : Aᶜ ⊆ F := heq ▸ subset_union_left
  have h2 : Bᶜ ⊆ F := heq ▸ subset_union_right
  rw [netChange_eq_sum _ _ F hc, ← sum_mark _ _ h1, ← sum_mark _ _ h2,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [mark,ha,hb]

theorem edge_conservation (A B C D : Set α)
    (hab : (differenceSupport A B).Finite) (hcd : (differenceSupport C D).Finite)
    (src : Disjoint A C) (dst : Disjoint B D)
    (hs : (A ∪ C)ᶜ.Finite) (ht : (B ∪ D)ᶜ.Finite)
    (same : (A ∪ C)ᶜ.ncard = (B ∪ D)ᶜ.ncard) :
    netChange A B + netChange C D = 0 := by
  rw [← netChange_union _ _ _ _ hab hcd src dst, netChange_finite_exteriors _ _ hs ht, same]
  simp

end BooleanScott
