module
public import BooleanScott.PrivateIncidence
public import BooleanScott.RowCounts

/-! Each actual row has one even packet in each ledger column beyond the
cut, and infinitely many copies of one odd tag packet. The derivative of
its j-markers is the row root exactly for that odd tag. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped OnePoint Classical

def rowDegree (e n : ℕ) : ℕ ⊕ ℕ → ℕ
  | .inl i => 2*(n+i)
  | .inr _ => 2*e+1

abbrev RowPacket (e n : ℕ) (i : ℕ ⊕ ℕ) := Mixed (rowDegree e n i)
abbrev TagRow (e n : ℕ) := PacketSum (RowPacket e n)

theorem row_stone (e n : ℕ) :
    T2Space (TagRow e n) ∧ ZeroDimensionalSpace (TagRow e n) ∧ Countable (Clopens (TagRow e n)) := by
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket e n i) := (mixed_stone _).1
  let hz (i : ℕ ⊕ ℕ) : ZeroDimensionalSpace (RowPacket e n i) := (mixed_stone _).2.1
  let hc (i : ℕ ⊕ ℕ) : Countable (Clopens (RowPacket e n i)) := (mixed_stone _).2.2
  exact ⟨packetSum_hausdorff _,packetSum_zeroDimensional _,countable_array_clopens⟩

theorem local_component {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)] (P : LocalLocus)
    (i : I) (p : X i) : packetInclusion X i p ∈ P.points (PacketSum X) ↔ p ∈ P.points (X i) :=
  Set.ext_iff.mp (P.restricts (open_packetInclusion X i)) p

theorem mixed_root_stage_of_le {k d : ℕ} (le : k ≤ d) : (∞ : Mixed d) ∈ (scatteredStage k).points (Mixed d) := by
  cases k with
  | zero =>
    have h : (∞ : Mixed d) ∈ mixedBoundary (Mixed d) := by simp [mixedBoundary_singleton]
    exact h.1
  | succ k => exact (mixed_root_height d k).mpr (Nat.le_of_succ_le le)

theorem row_root_stage (e n k : ℕ) : (∞ : TagRow e n) ∈ (scatteredStage (k+1)).points (TagRow e n) := by
  change ∞ ∈ derivatives (k+1) _
  rw [derivatives_succ,infty_in_derived_iff]
  let f (i : ℕ) : ℕ ⊕ ℕ := .inl (k+i)
  apply infinite_of_injective_forall_mem (f := f) (fun a b eq => Nat.add_left_cancel (Sum.inl.inj eq))
  intro i
  refine ⟨∞,(local_component (RowPacket e n) (scatteredStage k) (f i) ∞).mpr ?_⟩
  apply mixed_root_stage_of_le
  change k ≤ 2*(n+(k+i))
  omega

theorem row_root_not_private (e n j : ℕ) : (∞ : TagRow e n) ∉ privateMark (TagRow e n) j :=
  fun h => h.2.2 (row_root_stage e n (j+1))

theorem row_packet_private (e n j : ℕ) (i : ℕ ⊕ ℕ) (x : RowPacket e n i) :
    packetInclusion (RowPacket e n) i x ∈ privateMark (TagRow e n) j ↔ rowDegree e n i = j ∧ x = ∞ := by
  apply (local_component _ (privateLocus j) i x).trans
  change x ∈ privateMark (Mixed _) j ↔ _
  rw [mixed_private_mark]
  by_cases h : j = rowDegree e n i
  · rw [ite_eq_left h]
    exact ⟨fun hx => ⟨h.symm,hx⟩, And.right⟩
  · rw [ite_eq_right h]
    exact iff_of_false id (fun z => h z.1.symm)

theorem row_occupied_private (e n j : ℕ) : occupied (privateMark (TagRow e n) j) =
    {i | rowDegree e n i = j} := by
  ext i
  change (∃ x, _) ↔ _
  simp only [row_packet_private,exists_and_left,exists_eq,and_true,mem_ofPred_eq]

theorem row_infinite_tag (e n j : ℕ) :
    (occupied (privateMark (TagRow e n) j)).Infinite ↔ j = 2*e+1 := by
  rw [row_occupied_private]
  constructor
  · intro infinite
    by_contra diff
    apply infinite
    apply ((finite_le_nat j).image (Sum.inl : ℕ → ℕ ⊕ ℕ)).subset
    rintro (i|i) hi
    · refine ⟨i,?_,rfl⟩
      change 2*(n+i) = j at hi
      change i ≤ j
      omega
    · exact (diff hi.symm).elim
  · rintro rfl
    exact infinite_of_injective_forall_mem (f := Sum.inr) Sum.inr_injective (fun _ : ℕ => rfl)

theorem finite_mark_derivative_empty {X : Type} [TopologicalSpace X] [T1Space X] {S : Set X} (h : S.Finite) :
    derivedSet S = ∅ := eq_empty_iff_forall_notMem.mpr fun _ acc => (Infinite.of_accPt (mem_derivedSet.mp acc)) h

theorem row_private_derivative (e n j : ℕ) :
    derivedSet (privateMark (TagRow e n) j) = if j = 2*e+1 then {∞} else ∅ := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    rw [infty_in_derived_iff,row_infinite_tag]
    by_cases h : j = 2*e+1 <;> simp [h]
  | coe p =>
    rcases p with ⟨i,x⟩
    have loc := local_derivative (open_packetInclusion (RowPacket e n) i) (privateMark (TagRow e n) j)
    rw [local_privateMark (open_packetInclusion (RowPacket e n) i)] at loc
    have fin : (privateMark (RowPacket e n i) j).Finite := by
      rw [mixed_private_mark]; split <;> simp
    let := (mixed_stone (rowDegree e n i)).1
    rw [finite_mark_derivative_empty fin] at loc
    have no : packetInclusion (RowPacket e n) i x ∉ derivedSet (privateMark (TagRow e n) j) :=
      fun h => (Set.ext_iff.mp loc x).mp h
    apply iff_of_false no
    split
    · exact OnePoint.coe_ne_infty _
    · exact id

end BooleanScott
