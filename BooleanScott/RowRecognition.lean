module
public import BooleanScott.ConcreteCharts
public import BooleanScott.TagTopology

/-! The isolated points of the first derivative of a tag recognize its row
roots in every concrete chart. In an arbitrary model all accumulations of
these points lie in the second derivative. This gives the finite exterior
bound needed for conservation without a global classification of germs. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace
open scoped OnePoint Classical

def tagFirst (e : ℕ) := (privateLocus (2*e+1)).stage 1
def tagAnchor (e : ℕ) := (privateLocus (2*e+1)).stage 2
def tagRoot (e : ℕ) := (tagFirst e).difference (tagAnchor e)

theorem tagAnchor_finiteHit (e : ℕ) : FiniteHit (tagAnchor e) :=
  finiteHit_stages (private_finiteHit _) 2

theorem tagRoot_finiteHit (e : ℕ) : FiniteHit (tagRoot e) := by
  apply finiteHit_difference (finiteHit_stages (private_finiteHit _) 1) (tagAnchor_finiteHit e)
  intro X _ _ _ _
  exact isClosed_derivedSet (derivedSet (privateMark X (2*e+1)))

theorem tagRoot_accumulations (e : ℕ) (X : Type) [TopologicalSpace X] :
    derivedSet ((tagRoot e).points X) ⊆ (tagAnchor e).points X :=
  derivedSet_mono _ _ (show (tagRoot e).points X ⊆ (tagFirst e).points X from sdiff_subset)

theorem finite_roots_outside {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (e : ℕ)
    (C : Clopens X) (contains : (tagAnchor e).points X ⊆ C) :
    ((tagRoot e).points X \ (C : Set X)).Finite :=
  finite_exterior C.isClopen ((tagRoot_accumulations e X).trans contains)

theorem tagAnchor_row (a n e : ℕ) : (tagAnchor e).points (TagRow a n) = ∅ := by
  change derivedSet (derivedSet (privateMark (TagRow a n) (2*e+1))) = ∅
  rw [row_private_derivative]
  let := (row_stone a n).1
  apply finite_mark_derivative_empty
  split <;> simp

theorem tagRoot_row (a n e : ℕ) : (tagRoot e).points (TagRow a n) = if a=e then {∞} else ∅ := by
  change (derivedSet (privateMark (TagRow a n) (2*e+1)) \ (tagAnchor e).points (TagRow a n)) = _
  rw [tagAnchor_row,sdiff_empty,row_private_derivative]
  by_cases h : a = e
  · subst e; simp
  · rw [ite_eq_right (by omega),ite_eq_right h]

theorem tagAnchor_chart (tags : Set ℕ) (e : ℕ) :
    (tagAnchor e).points (VertexChart tags) = if e ∈ tags then {∞} else ∅ :=
  chart_second_tag tags e

theorem tagRoot_chart_vertex (tags : Set ℕ) (e : ℕ) : (∞ : VertexChart tags) ∉ (tagRoot e).points (VertexChart tags) := by
  rintro ⟨first,excl⟩
  have he := (chart_root_tag_derivative tags e).mp first
  apply excl
  rw [tagAnchor_chart,ite_eq_left he]
  rfl

theorem tagRoot_chart_row {tags : Set ℕ} (r : ChartIndex tags) (e : ℕ) (x : ChartRow r) :
    packetInclusion ChartRow r x ∈ (tagRoot e).points (VertexChart tags) ↔ r.1.val=e ∧ x=∞ := by
  apply (local_component ChartRow (tagRoot e) r x).trans
  rw [tagRoot_row]
  by_cases h : r.1.val=e
  · rw [ite_eq_left h]
    exact ⟨fun h' => ⟨h,h'⟩,And.right⟩
  · rw [ite_eq_right h]
    exact iff_of_false id (fun z => h z.1)

end BooleanScott
