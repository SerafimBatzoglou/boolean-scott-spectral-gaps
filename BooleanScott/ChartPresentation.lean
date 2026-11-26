module
public import BooleanScott.TreeWitness
public import BooleanScott.CoverComparison

/-! Every varying chart has a surjective presentation by the same countable
algebra of clopens of a universal chart. Its restriction map simply drops
all rows of missing tags and keeps the vertex bit. Equality of two traces
is a countable conjunction of Borel membership tests in the tree. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace MeasureTheory
open scoped Classical OnePoint

abbrev AllRow (r : ℕ × ℕ) := TagRow r.1 (r.1+r.2)
abbrev AllChart := PacketSum AllRow
abbrev ChartCodes := Clopens AllChart

theorem chartCodes_countable : Countable ChartCodes := by
  let hi (r : ℕ × ℕ) : Countable (Clopens (AllRow r)) := (row_stone _ _).2.2
  exact countable_array_clopens

def rowIndex {S : Set ℕ} (r : ChartIndex S) : ℕ × ℕ := (r.1.val,r.2)
theorem rowIndex_injective (S : Set ℕ) : Function.Injective (rowIndex (S := S)) := by
  rintro ⟨⟨a,ha⟩,n⟩ ⟨⟨b,hb⟩,m⟩ eq
  simpa [rowIndex] using eq

def chartPoint (S : Set ℕ) (x : VertexChart S) : AllChart :=
  x.elim ∞ fun p => packetInclusion AllRow (rowIndex p.1) p.2

noncomputable def chartRestrict (S : Set ℕ) (C : ChartCodes) : Clopens (VertexChart S) := by
  let U := chartPoint S ⁻¹' (C : Set AllChart)
  refine ⟨U,(clopen_array_iff _).mpr ?_⟩
  obtain ⟨h,F,tail⟩ := (clopen_array_iff _).mp C.isClopen
  refine ⟨fun r => h (rowIndex r),?_,?_⟩
  · exact F.preimage rowIndex (rowIndex_injective S).injOn
  · intro r hr x
    exact tail _ (fun mem => hr (Finset.mem_preimage.mpr mem)) x

noncomputable def expandPoint (S : Set ℕ) (x : AllChart) : VertexChart S :=
  x.elim ∞ fun p => if h : p.1.1 ∈ S then packetInclusion ChartRow (⟨p.1.1,h⟩,p.1.2) p.2 else ∞

noncomputable def chartExtend (S : Set ℕ) (C : Clopens (VertexChart S)) : ChartCodes := by
  let U := expandPoint S ⁻¹' (C : Set _)
  refine ⟨U,(clopen_array_iff _).mpr ?_⟩
  obtain ⟨h,F,tail⟩ := (clopen_array_iff _).mp C.isClopen
  constructor
  · rintro ⟨e,n⟩
    by_cases he : e ∈ S
    · simpa only [U,expandPoint,mem_preimage,OnePoint.elim_some,dite_eq_left he,packetInclusion] using h (⟨e,he⟩,n)
    · change IsClopen {x : TagRow e (e+n) | (if hx : e ∈ S then packetInclusion ChartRow (⟨e,hx⟩,n) x else ∞) ∈ C}
      by_cases root : ∞ ∈ C <;> simp [he,root]
      · exact isClopen_univ
      · exact isClopen_empty
  · refine ⟨F.image rowIndex,?_⟩
    rintro ⟨e,n⟩ out x
    change ((if hx : e ∈ S then packetInclusion ChartRow (⟨e,hx⟩,n) x else ∞) ∈ C) ↔ ∞ ∈ C
    by_cases he : e ∈ S
    · rw [dite_eq_left he]
      exact tail (⟨e,he⟩,n) (fun mem => out (Finset.mem_image.mpr ⟨_,mem,rfl⟩)) x
    · rw [dite_eq_right he]

theorem chartRestrict_surjective (S : Set ℕ) : Function.Surjective (chartRestrict S) := by
  intro C
  refine ⟨chartExtend S C,?_⟩
  ext x
  change expandPoint S (chartPoint S x) ∈ C ↔ x ∈ C
  induction x using OnePoint.rec with
  | infty => rfl
  | coe p =>
    rcases p with ⟨⟨⟨e,he⟩,n⟩,x⟩
    change (if h : e ∈ S then packetInclusion ChartRow (⟨e,h⟩,n) x else ∞) ∈ C ↔ _
    rw [dite_eq_left he]
    rfl

theorem chartRestrict_eq_iff (S : Set ℕ) (C E : ChartCodes) : chartRestrict S C = chartRestrict S E ↔
    ((∞ : AllChart) ∈ C ↔ ∞ ∈ E) ∧ ∀ e n : ℕ, e ∈ S → packetRestriction C (e,n) = packetRestriction E (e,n) := by
  constructor
  · intro eq
    have same (x : VertexChart S) : chartPoint S x ∈ C ↔ chartPoint S x ∈ E :=
      SetLike.ext_iff.mp eq x
    exact ⟨same ∞,fun e n he => SetLike.ext (fun x => same (packetInclusion ChartRow (⟨e,he⟩,n) x))⟩
  · rintro ⟨root,rows⟩
    ext x
    induction x using OnePoint.rec with
    | infty => exact root
    | coe p =>
      rcases p with ⟨⟨⟨e,he⟩,n⟩,x⟩
      exact SetLike.ext_iff.mp (rows e n he) x

theorem chartRestrict_term (S : Set ℕ) {n : ℕ} (v : Fin n → ChartCodes) (t : Term n) :
    chartRestrict S (t.eval (BoolOps.ofAlgebra _) v) = t.eval (BoolOps.ofAlgebra _) (chartRestrict S ∘ v) := by
  induction t with
  | var | zero | one => rfl
  | compl t ih => rw [Term.eval,Term.eval,← ih]; rfl
  | meet a b ha hb | join a b ha hb => rw [Term.eval,Term.eval,← ha,← hb]; rfl

def chartDiagram (S : Set ℕ) : CodeDiagram ChartCodes :=
  fun {_} v s t => chartRestrict S (s.eval (BoolOps.ofAlgebra _) v) = chartRestrict S (t.eval (BoolOps.ofAlgebra _) v)

theorem chart_presentsDiagram (S : Set ℕ) :
    PresentsDiagram (chartDiagram S) (BoolOps.ofAlgebra _) (chartRestrict S) := by
  intro n v s t
  simp only [chartDiagram,chartRestrict_term]

theorem sectorTags_measurable (v : Vertex) (e : ℕ) :
    Measurable fun c : Baire => e ∈ sectorTags (diagonalTree c) v := by
  change Measurable fun c : Baire => ∃ t : TagName, tagNumber t=e ∧ v ∈ tagSupport (diagonalTree c) t
  apply Measurable.exists; intro t
  apply Measurable.and measurable_const
  rcases t with w|⟨w,i⟩
  · exact measurable_const
  · have mem : Measurable fun c : Baire => w++[i] ∈ diagonalTree c :=
      measurableSet_setOfPred.mp (clopen_tree_membership (w++[i])).isOpen.measurableSet
    have same (c : Baire) : v ∈ tagSupport (diagonalTree c) (.inr (w,i)) ↔
        w++[i] ∈ diagonalTree c ∧ v ∈ ({w,w++[i]} : Finset Vertex) := by
      by_cases h : w++[i] ∈ diagonalTree c <;> simp [tagSupport,h]
    simp_rw [same]
    exact mem.and measurable_const

theorem chartDiagram_measurable (v : Vertex) {n : ℕ} (u : Fin n → ChartCodes) (s t : Term n) :
    Measurable fun c : Baire => chartDiagram (sectorTags (diagonalTree c) v) u s t := by
  simp only [chartDiagram,chartRestrict_eq_iff]
  exact measurable_const.and (Measurable.forall fun e => Measurable.forall fun _ : ℕ =>
    (sectorTags_measurable v e).imp measurable_const)

end BooleanScott
