module
public import BooleanScott.LooseFragments
public import BooleanScott.ChartCoreMatching

/-! A retained row absorbs a further packet of its own tag, and its
arbitrarily high ledger packets absorb every finite pure remainder. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

theorem split_subclopen {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A B : Clopens X} (sub : A ≤ B) : spaceType B = spaceType A + spaceType (B \ A : Clopens X) := by
  have eq : A ⊔ (B \ A) = B := by
    ext x
    change (x ∈ A ∨ x ∈ B ∧ x ∉ A) ↔ x ∈ B
    exact ⟨fun h => h.elim (fun ha => sub ha) And.left,fun hb => or_iff_not_imp_left.mpr (fun h => ⟨hb,h⟩)⟩
  have apart : Disjoint (A : Set X) ((B \ A : Clopens X) : Set X) :=
    Set.disjoint_left.mpr (fun _ ha h => h.2 ha)
  exact (congrArg (fun D : Clopens X => spaceType D) eq.symm).trans (clopen_sup_type _ _ apart)

def SpaceSummand (z x : SpaceType) : Prop := ∃ t, x=z+t

theorem SpaceSummand.absorbs {z x p : SpaceType} (s : SpaceSummand z x) (hz : z+p=z) : x+p=x := by
  obtain ⟨u,rfl⟩ := s
  calc
    z+u+p = z+p+u := by ac_rfl
    _ = _ := congrArg (·+u) hz

theorem clopen_summand {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] (A : Clopens X) :
    SpaceSummand (spaceType A) (spaceType X) := by
  have eq := split_subclopen (show A ≤ ⊤ from le_top)
  rw [univ_clopen_spaceType (C := (⊤ : Clopens X)) (fun _ => trivial)] at eq
  exact ⟨_,eq⟩

theorem row_summand (e n : ℕ) (i : ℕ ⊕ ℕ) : SpaceSummand (spaceType (RowPacket e n i)) (spaceType (TagRow e n)) := by
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket e n i) := (mixed_stone _).1
  let := (row_stone e n).1
  have s := clopen_summand (packetLift (RowPacket e n) i ⊤)
  rwa [packetLift_type,univ_clopen_spaceType (fun _ => trivial)] at s

theorem row_absorbs_pure (e n : ℕ) {d : ℕ} {p : SpaceType} (h : PureRemainder d p) :
    spaceType (TagRow e n) + p = spaceType (TagRow e n) := by
  apply (row_summand e n (.inl d)).absorbs
  exact mixed_absorbs_remainder (pure_mono (show d ≤ 2*(n+d) by omega) h)

theorem row_absorbs_tag (e n : ℕ) : spaceType (TagRow e n) + spaceType (Mixed (2*e+1)) = spaceType (TagRow e n) := by
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket e n i) := (mixed_stone _).1
  let := (row_stone e n).1
  let A := rowTail e n 0 1
  let B := packetLift (RowPacket e n) (.inr 0) ⊤
  have complement : (⊤ \ A : Clopens (TagRow e n)) = B := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      apply iff_of_false (fun h => h.2 (show ∞ ∈ A from rfl))
      rintro ⟨y,_,eq⟩
      exact OnePoint.coe_ne_infty _ eq
    | coe p =>
      obtain ⟨i,y⟩ := p
      change (_ ∧ packetInclusion _ i y ∉ rowTail e n 0 1) ↔ _
      rw [rowTail_fiber]
      cases i with
      | inl i =>
        apply iff_of_false (fun h => h.2 (Nat.zero_le _))
        rintro ⟨z,_,eq⟩
        cases congrArg Sigma.fst (OnePoint.coe_injective eq)
      | inr i =>
        cases i with
        | zero => exact iff_of_true ⟨trivial,Nat.not_succ_le_zero 0⟩ ⟨y,trivial,rfl⟩
        | succ i =>
          apply iff_of_false (fun h => h.2 (Nat.succ_le_succ (Nat.zero_le _)))
          rintro ⟨z,_,eq⟩
          cases congrArg Sigma.fst (OnePoint.coe_injective eq)
  have eq := split_subclopen (show A ≤ ⊤ from le_top)
  rw [complement,univ_clopen_spaceType (C := (⊤ : Clopens (TagRow e n))) (fun _ => trivial)] at eq
  change spaceType (TagRow e n) = spaceType (rowTail e n 0 1) + spaceType (packetLift (RowPacket e n) (.inr 0) ⊤) at eq
  rw [rowTail_type,packetLift_type,univ_clopen_spaceType (fun _ => trivial)] at eq
  exact eq.symm

namespace ChartTailSpec
variable {S : Set ℕ} {C : Clopens (VertexChart S)} (d : ChartTailSpec C)

theorem row_summand_core (r : retainedRows C) : SpaceSummand (spaceType (TagRow r.val.1.val (d.cut r))) (spaceType d.core) := by
  let ht (r : ChartIndex S) : T2Space (ChartRow r) := (row_stone _ _).1
  let := (chart_stone S).1
  let V := packetLift ChartRow r.val (d.fiber r.val)
  have sub : V ≤ d.core := by
    rintro _ ⟨x,hx,rfl⟩; exact hx
  have eq := split_subclopen sub
  change spaceType d.core = spaceType (packetLift ChartRow r.val (d.fiber r.val)) + _ at eq
  rw [packetLift_type,fiber,ite_eq_left r.property,rowTail_type] at eq
  refine ⟨spaceType (d.core \ V : Clopens (VertexChart S)),?_⟩
  rw [show d.cut r = rowStart r.val + (d.threshold-rowStart r.val) by unfold cut; omega]
  exact eq

theorem core_absorbs_pure (r : retainedRows C) {p : SpaceType} {k : ℕ} (h : PureRemainder k p) :
    spaceType d.core + p = spaceType d.core :=
  (d.row_summand_core r).absorbs (row_absorbs_pure _ _ h)

theorem core_absorbs_tag (r : retainedRows C) : spaceType d.core + spaceType (Mixed (2*r.val.1.val+1)) = spaceType d.core :=
  (d.row_summand_core r).absorbs (row_absorbs_tag _ _)

theorem core_missing_odd {e : ℕ} (hn : S.Nonempty) (absent : ∀ r : retainedRows C, r.val.1.val ≠ e) :
    (privateLocus (2*e+1)).count (spaceType d.core) = 0 := by
  rw [LocalLocus.count_clopen,encard_eq_zero,eq_empty_iff_forall_notMem]
  rintro p ⟨inside,mark⟩
  induction p using OnePoint.rec with
  | infty => exact chart_root_not_private hn _ mark
  | coe p =>
    obtain ⟨r,x⟩ := p
    have tag := (row_odd_mark_exists r.1.val (rowStart r) e).mp
      ⟨x,(local_component ChartRow (privateLocus (2*e+1)) r x).mp mark⟩
    change x ∈ d.fiber r at inside
    rw [fiber] at inside
    split at inside
    · rename_i hr; exact absent ⟨r,hr⟩ tag
    · exact inside

end ChartTailSpec
end BooleanScott
