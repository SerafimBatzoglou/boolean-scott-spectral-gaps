module
public import BooleanScott.RowTails

/-! In an arbitrary chart clopen all sufficiently late ledger packets are
whole, simultaneously in every row. Selecting the corresponding row tails
leaves a compact remainder containing no vertex or row root. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

abbrev rowStart {S : Set ℕ} (r : ChartIndex S) := r.1.val+r.2
noncomputable abbrev retainedRows {S : Set ℕ} (C : Clopens (VertexChart S)) := rootRows chartRoot (C : Set (VertexChart S))

structure ChartTailSpec {S : Set ℕ} (C : Clopens (VertexChart S)) where
  threshold : ℕ
  oddSkip : ChartIndex S → ℕ
  exceptional : Finset (ChartIndex S)
  zero_outside : ∀ r ∉ exceptional, oddSkip r = 0
  outer : ∀ r ∉ exceptional, ∀ x : ChartRow r, packetInclusion ChartRow r x ∈ C ↔ ∞ ∈ C
  whole (r : ChartIndex S) (i : ℕ ⊕ ℕ) : inRowTail (threshold-rowStart r) (oddSkip r) i →
    ∀ x : RowPacket r.1.val (rowStart r) i,
      packetInclusion ChartRow r (packetInclusion _ i x) ∈ C ↔ r ∈ retainedRows C

theorem chart_tail_spec {S : Set ℕ} (C : Clopens (VertexChart S)) : Nonempty (ChartTailSpec C) := by
  classical
  obtain ⟨_,F,outside⟩ := (clopen_array_iff _).mp C.isClopen
  choose E localTail using fun r : ChartIndex S => ((clopen_array_iff _).mp (packetRestriction C r).isClopen).2
  let bound (r : ChartIndex S) := (E r).sup (Sum.elim id id) + 1
  let K := F.sup (fun r => rowStart r + bound r)
  let o (r : ChartIndex S) := if r ∈ F then bound r else 0
  refine ⟨⟨K,o,F,fun r h => ite_eq_right h,outside,?_⟩⟩
  intro r i keep x
  by_cases hr : r ∈ F
  · apply localTail r i _ x
    intro hi
    have small : Sum.elim id id i < bound r := Nat.lt_succ_of_le (Finset.le_sup hi)
    have large : rowStart r + bound r ≤ K := Finset.le_sup (f := fun r => rowStart r + bound r) hr
    cases i with
    | inl n =>
      change K-rowStart r ≤ n at keep
      change n < bound r at small
      omega
    | inr n =>
      change o r ≤ n at keep
      rw [show o r = bound r from ite_eq_left hr] at keep
      exact (Nat.not_lt_of_ge keep) small
  · exact (outside r hr _).trans (outside r hr ∞).symm

namespace ChartTailSpec
variable {S : Set ℕ} {C : Clopens (VertexChart S)} (d : ChartTailSpec C)

def raise (K : ℕ) (le : d.threshold ≤ K) : ChartTailSpec C where
  threshold := K
  oddSkip := d.oddSkip
  exceptional := d.exceptional
  zero_outside := d.zero_outside
  outer := d.outer
  whole r i keep := d.whole r i (by
    cases i with
    | inl n => exact (Nat.sub_le_sub_right le _).trans keep
    | inr n => exact keep)

noncomputable def fiber (r : ChartIndex S) : Clopens (ChartRow r) :=
  if r ∈ retainedRows C then rowTail r.1.val (rowStart r) (d.threshold-rowStart r) (d.oddSkip r) else ⊥

theorem fiber_root (r : ChartIndex S) : (∞ : ChartRow r) ∈ d.fiber r ↔ r ∈ retainedRows C := by
  unfold fiber
  split
  · rename_i h; exact iff_of_true rfl h
  · rename_i h; exact iff_of_false id h

theorem fiber_uniform : ∃ F : Finset (ChartIndex S), ∀ r ∉ F, ∀ x : ChartRow r,
    x ∈ d.fiber r ↔ decide (∞ ∈ C) = true := by
  classical
  let early := (finite_ledger_rows S d.threshold).toFinset
  refine ⟨d.exceptional ∪ early,?_⟩
  intro r hr x
  have good : r ∉ d.exceptional := fun h => hr (Finset.mem_union_left _ h)
  have late : d.threshold < rowStart r := lt_of_not_ge (fun h => hr (Finset.mem_union_right _
    ((finite_ledger_rows S d.threshold).mem_toFinset.mpr h)))
  rw [decide_eq_true_eq]
  have root := d.outer r good ∞
  by_cases h : r ∈ retainedRows C
  · rw [fiber,ite_eq_left h,Nat.sub_eq_zero_of_le late.le,d.zero_outside r good]
    refine iff_of_true ?_ (root.mp h)
    induction x using OnePoint.rec with
    | infty => rfl
    | coe p =>
      obtain ⟨i,y⟩ := p
      apply (rowTail_fiber _ _ _ _ i y).mpr
      cases i <;> exact Nat.zero_le _
  · rw [fiber,ite_eq_right h]
    exact iff_of_false id (fun hc => h (root.mpr hc))

noncomputable def core : Clopens (VertexChart S) := arrayClopen (decide (∞ ∈ C)) d.fiber d.fiber_uniform

theorem core_vertex : ∞ ∈ d.core ↔ ∞ ∈ C := decide_eq_true_iff

theorem core_root (r : ChartIndex S) : packetInclusion ChartRow r ∞ ∈ d.core ↔ r ∈ retainedRows C :=
  d.fiber_root r

theorem core_subset : d.core ≤ C := by
  intro z hz
  induction z using OnePoint.rec with
  | infty => exact d.core_vertex.mp hz
  | coe p =>
    obtain ⟨r,x⟩ := p
    change x ∈ d.fiber r at hz
    rw [fiber] at hz
    split at hz
    · rename_i carry
      induction x using OnePoint.rec with
      | infty => exact carry
      | coe p =>
        obtain ⟨i,y⟩ := p
        exact (d.whole r i ((rowTail_fiber _ _ _ _ i y).mp hz) y).mpr carry
    · exact False.elim hz

theorem core_type : spaceType d.core = spaceType (capped (decide (∞ ∈ C))
    (TopCat.of (Σ r : retainedRows C, TagRow r.val.1.val (max d.threshold (rowStart r.val))))) := by
  classical
  let ht (r : ChartIndex S) : T2Space (ChartRow r) := (row_stone _ _).1
  let Y (r : retainedRows C) := TagRow r.val.1.val (max d.threshold (rowStart r.val))
  have h (r : retainedRows C) : Nonempty (Y r ≃ₜ d.fiber r.val) := by
    apply (spaceType_eq_iff _ _).mp
    rw [fiber,ite_eq_left r.property,rowTail_type]
    exact congrArg (fun k => spaceType (TagRow r.val.1.val k))
      (show max d.threshold (rowStart r.val) = rowStart r.val + (d.threshold-rowStart r.val) by omega)
  let g (r : retainedRows C) := (h r).some
  let f (r : retainedRows C) (x : Y r) : ChartRow r.val := (g r x).val
  let idx : retainedRows C ↪ ChartIndex S := ⟨Subtype.val,Subtype.val_injective⟩
  have fe (r : retainedRows C) : IsOpenEmbedding (f r) :=
    (d.fiber r.val).isClopen.isOpen.isOpenEmbedding_subtypeVal.comp (g r).isOpenEmbedding
  have fibers (r : ChartIndex S) (x : ChartRow r) : packetInclusion ChartRow r x ∈ d.core ↔
      ∃ p, subarrayMap idx f p = packetInclusion ChartRow r x := by
    change x ∈ d.fiber r ↔ _
    constructor
    · intro hx
      have hr : r ∈ retainedRows C := by
        by_contra no
        rw [fiber,ite_eq_right no] at hx
        exact hx
      let q : retainedRows C := ⟨r,hr⟩
      obtain ⟨y,hy⟩ := (g q).surjective ⟨x,hx⟩
      exact ⟨⟨q,y⟩,congrArg (packetInclusion ChartRow r) (congrArg Subtype.val hy)⟩
    · rintro ⟨⟨q,y⟩,eq⟩
      have hmem : subarrayMap idx f ⟨q,y⟩ ∈ d.core := (g q y).property
      change packetInclusion ChartRow r x ∈ d.core
      exact eq ▸ hmem
  have eq := subarray_type d.core idx f fe fibers
  rwa [show decide (∞ ∈ d.core) = decide (∞ ∈ C) by simp only [d.core_vertex]] at eq

end ChartTailSpec
end BooleanScott
