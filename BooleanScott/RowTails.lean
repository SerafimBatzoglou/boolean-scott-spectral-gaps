module
public import BooleanScott.ArraySlices

/-! Simultaneously remove finite initial segments of the ledger column
indices and of the repeated tag packets, preserving a complete compact row. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

def tailIndex (l o : ℕ) : (ℕ ⊕ ℕ) ↪ (ℕ ⊕ ℕ) :=
  Function.Embedding.sumMap ⟨fun i => l+i,fun _ _ => Nat.add_left_cancel⟩
    ⟨fun i => o+i,fun _ _ => Nat.add_left_cancel⟩

def inRowTail (l o : ℕ) : ℕ ⊕ ℕ → Prop := Sum.elim (fun i => l ≤ i) (fun i => o ≤ i)

theorem tailIndex_range (l o : ℕ) (i : ℕ ⊕ ℕ) :
    i ∈ range (tailIndex l o) ↔ inRowTail l o i := by
  constructor
  · rintro ⟨n,rfl⟩
    cases n <;> exact Nat.le_add_right _ _
  · cases i with
    | inl n =>
      rintro (h : l ≤ n)
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
      exact ⟨.inl k,rfl⟩
    | inr n =>
      rintro (h : o ≤ n)
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
      exact ⟨.inr k,rfl⟩

noncomputable def rowTail (tag cut l o : ℕ) : Clopens (TagRow tag cut) :=
  arrayClopen true (fun i => if inRowTail l o i then ⊤ else ⊥) (by
    refine ⟨(Finset.range l).disjSum (Finset.range o),?_⟩
    intro i hi x
    have yes : inRowTail l o i := by
      cases i <;> simpa [inRowTail] using hi
    rw [ite_eq_left yes]
    exact iff_of_true (Set.mem_univ _) rfl)

theorem rowTail_fiber (tag cut l o : ℕ) (i : ℕ ⊕ ℕ) (x : RowPacket tag cut i) :
    packetInclusion (RowPacket tag cut) i x ∈ rowTail tag cut l o ↔ inRowTail l o i := by
  change x ∈ (if inRowTail l o i then ⊤ else ⊥ : Clopens (RowPacket tag cut i)) ↔ _
  split
  · rename_i h; exact iff_of_true (Set.mem_univ _) h
  · rename_i h; exact iff_of_false id h

noncomputable def mixedDegreeCongr {d k : ℕ} (h : d=k) : Mixed d ≃ₜ Mixed k := h ▸ Homeomorph.refl _

noncomputable def tailPacket (tag cut l o : ℕ) (i : ℕ ⊕ ℕ) :
    RowPacket tag (cut+l) i ≃ₜ RowPacket tag cut (tailIndex l o i) := by
  apply mixedDegreeCongr
  cases i with
  | inl n => exact congrArg (2*·) (Nat.add_assoc cut l n)
  | inr n => rfl

theorem rowTail_type (tag cut l o : ℕ) :
    spaceType (rowTail tag cut l o) = spaceType (TagRow tag (cut+l)) := by
  classical
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket tag cut i) := (mixed_stone _).1
  let e := tailIndex l o
  let h := tailPacket tag cut l o
  let C := rowTail tag cut l o
  have top : (∞ : TagRow tag cut) ∈ C := rfl
  have fibers (i : ℕ ⊕ ℕ) (x : RowPacket tag cut i) : packetInclusion (RowPacket tag cut) i x ∈ C ↔
      ∃ p, subarrayMap e (fun j => h j) p = packetInclusion (RowPacket tag cut) i x := by
    rw [rowTail_fiber,← tailIndex_range]
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨⟨j,(h j).symm x⟩,congrArg (packetInclusion _ _) ((h j).apply_symm_apply _)⟩
    · rintro ⟨⟨j,y⟩,eq⟩
      exact ⟨j,congrArg Sigma.fst (OnePoint.coe_injective eq)⟩
  have eq := subarray_type C e (fun j => h j) (fun j => (h j).isOpenEmbedding) fibers
  rwa [show decide (∞ ∈ C) = true from decide_eq_true top] at eq

end BooleanScott
