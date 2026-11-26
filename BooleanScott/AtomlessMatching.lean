module
public import BooleanScott.ClopenSigns

/-! Back-and-forth on clopen algebras of spaces where every nonempty clopen
splits. Matching the realized signs is sufficient. To extend one tuple,
split each of the finitely many target signs according to the two pieces
actually realized in the source. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace
open scoped Classical

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}

def SplitsClopens (X : Type) [TopologicalSpace X] : Prop :=
  ∀ U : Clopens X, (U : Set X).Nonempty → ∃ D : Clopens X,
    ((U : Set X) ∩ D).Nonempty ∧ ((U : Set X) \ D).Nonempty

def SamePatterns (v : Fin n → Clopens X) (w : Fin n → Clopens Y) : Prop :=
  ∀ p : Pattern n, (signCell v p : Set X).Nonempty ↔ (signCell w p : Set Y).Nonempty

theorem SamePatterns.symm {v : Fin n → Clopens X} {w : Fin n → Clopens Y} (h : SamePatterns v w) :
    SamePatterns w v := fun p => (h p).symm

noncomputable def joinSlices (w : Fin n → Clopens Y) (s : Pattern n → Clopens Y) : Clopens Y :=
  ⟨⋃ p, ((signCell w p : Set Y) ∩ s p), isClopen_iUnion_of_finite (fun p =>
    (signCell w p).isClopen.inter (s p).isClopen)⟩

theorem mem_joinSlices (w : Fin n → Clopens Y) (s : Pattern n → Clopens Y) (y : Y) :
    y ∈ joinSlices w s ↔ y ∈ s (pointPattern w y) := by
  change (y ∈ ⋃ p, ((signCell w p : Set Y) ∩ s p)) ↔ _
  rw [mem_iUnion]
  exact ⟨fun ⟨p,hp,hy⟩ => (mem_signCell.mp hp).symm ▸ hy,
    fun hy => ⟨_,mem_signCell.mpr rfl,hy⟩⟩

private theorem slice_for {U a : Clopens X} {V : Clopens Y}
    (nonempty : (U : Set X).Nonempty ↔ (V : Set Y).Nonempty) (split : SplitsClopens Y) :
    ∃ D : Clopens Y,
      (((U : Set X) ∩ a).Nonempty ↔ ((V : Set Y) ∩ D).Nonempty) ∧
      (((U : Set X) \ a).Nonempty ↔ ((V : Set Y) \ D).Nonempty) := by
  classical
  by_cases yes : ((U : Set X) ∩ a).Nonempty
  · by_cases no : ((U : Set X) \ a).Nonempty
    · obtain ⟨D,hp,hn⟩ := split V (nonempty.mp (yes.mono inter_subset_left))
      exact ⟨D,iff_of_true yes hp,iff_of_true no hn⟩
    · refine ⟨⊤,iff_of_true yes ?_,iff_of_false no ?_⟩
      · obtain ⟨y,hy⟩ := nonempty.mp (yes.mono inter_subset_left)
        exact ⟨y,hy,trivial⟩
      · rintro ⟨y,_,h⟩
        exact h trivial
  · refine ⟨⊥,iff_of_false yes (fun ⟨_,_,hn⟩ => hn),?_⟩
    constructor
    · rintro ⟨x,hx,_⟩
      obtain ⟨y,hy⟩ := nonempty.mp ⟨x,hx⟩
      exact ⟨y,hy,fun h => h⟩
    · rintro ⟨y,hy,_⟩
      obtain ⟨x,hx⟩ := nonempty.mpr ⟨y,hy⟩
      exact ⟨x,hx,fun h => yes ⟨x,hx,h⟩⟩

theorem pattern_prepend (v : Fin n → Clopens X) (a : Clopens X) (x : X) :
    pointPattern (prepend a v) x = prepend (decide (x ∈ a)) (pointPattern v x) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [prepend,pointPattern]

theorem pattern_decompose (p : Pattern (1+n)) :
    prepend (p (Fin.castAdd n 0)) (p ∘ Fin.natAdd 1) = p := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Subsingleton.elim i 0]
    simp [prepend]
  · simp [prepend]

private theorem slice_nonempty (v : Fin n → Clopens X) (a : Clopens X) (b : Bool) (p : Pattern n) :
    (signCell (prepend a v) (prepend b p) : Set X).Nonempty ↔
      (if b then ((signCell v p : Set X) ∩ a) else ((signCell v p : Set X) \ a)).Nonempty := by
  have eq (x : X) : x ∈ signCell (prepend a v) (prepend b p) ↔
      pointPattern v x = p ∧ decide (x ∈ a) = b := by
    rw [mem_signCell,pattern_prepend]
    constructor
    · intro h
      refine ⟨funext (fun i => ?_), ?_⟩
      · simpa only [prepend,Fin.append_right] using congrFun h (Fin.natAdd 1 i)
      · simpa only [prepend,Fin.append_left] using congrFun h (Fin.castAdd n (0 : Fin 1))
    · rintro ⟨h1,h2⟩
      rw [h1,h2]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Set.Nonempty,SetLike.mem_coe,eq,
    decide_eq_true_eq,decide_eq_false_iff_not,Set.mem_sdiff,Set.mem_inter_iff,mem_signCell]

theorem SamePatterns.extend {v : Fin n → Clopens X} {w : Fin n → Clopens Y}
    (h : SamePatterns v w) (split : SplitsClopens Y) (a : Clopens X) :
    ∃ b : Clopens Y, SamePatterns (prepend a v) (prepend b w) := by
  classical
  choose slices matchPos matchNeg using fun p => slice_for (a := a) (h p) split
  let b := joinSlices w slices
  have restrict (p : Pattern n) {y : Y} (hy : y ∈ signCell w p) : y ∈ b ↔ y ∈ slices p := by
    exact (mem_joinSlices w slices y).trans (mem_signCell.mp hy ▸ Iff.rfl)
  refine ⟨b,fun q => ?_⟩
  let p := q ∘ Fin.natAdd 1
  let bit := q (Fin.castAdd n 0)
  have hq : prepend bit p = q := pattern_decompose q
  rw [← hq,slice_nonempty,slice_nonempty]
  cases hb : bit
  · simp only [Bool.false_eq_true,ite_false]
    apply (matchNeg p).trans
    exact exists_congr (fun y => and_congr_right (fun hy => not_congr (restrict p hy).symm))
  · simp only [ite_true]
    apply (matchPos p).trans
    exact exists_congr (fun y => and_congr_right (fun hy => (restrict p hy).symm))

theorem SamePatterns.preserves_order {v : Fin n → Clopens X} {w : Fin n → Clopens Y}
    (h : SamePatterns v w) (i j : Fin n) : v i ≤ v j ↔ w i ≤ w j := by
  have forward {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      {v : Fin n → Clopens X} {w : Fin n → Clopens Y} (ok : SamePatterns v w) (le : v i ≤ v j) :
      w i ≤ w j := by
    intro y hy
    obtain ⟨x,hx⟩ := (ok (pointPattern w y)).mpr ⟨y,mem_signCell.mpr rfl⟩
    have same := mem_signCell.mp hx
    have eq (k : Fin n) : x ∈ v k ↔ y ∈ w k := by
      have bit := congrFun same k
      by_cases hv : x ∈ v k <;> by_cases hw : y ∈ w k <;> simp_all [pointPattern]
    exact (eq j).mp (le ((eq i).mpr hy))
  exact ⟨forward h,forward h.symm⟩

theorem splitting_clopens_iso [Nonempty X] [Nonempty Y]
    [Countable (Clopens X)] [Countable (Clopens Y)] (sx : SplitsClopens X) (sy : SplitsClopens Y) :
    Nonempty (Clopens X ≃o Clopens Y) := by
  apply countable_back_and_forth (@SamePatterns X Y _ _)
  · intro p
    have witness (Z : Type) [TopologicalSpace Z] [Nonempty Z] :
        (signCell (Fin.elim0 : Fin 0 → Clopens Z) p : Set Z).Nonempty :=
      ⟨Classical.arbitrary Z,mem_signCell.mpr (Subsingleton.elim _ _)⟩
    exact iff_of_true (witness X) (witness Y)
  · exact fun h => h.preserves_order
  · exact fun h a => h.extend sy a
  · intro n v w h b
    obtain ⟨a,h'⟩ := h.symm.extend sx b
    exact ⟨a,h'.symm⟩

end BooleanScott
