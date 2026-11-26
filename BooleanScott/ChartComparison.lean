module
public import BooleanScott.ChartPresentation
public import BooleanScott.TreeReduction

/-! A uniform Borel test for the variable chart clause. A code for a clopen
in an interval is any ambient element, interpreted by intersecting it with
the interval top. Both the chart and interval presentations admit repeated
codes and cover every actual element. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory Ordinal Set TopologicalSpace
open scoped Ordinal

def intervalDiagram {A : Type} (M : BoolOps A) (d : A) : CodeDiagram A :=
  fun {n} v s t =>
    let slot := Fin.castAdd n (0 : Fin 1)
    let w := Fin.append (fun _ : Fin 1 => d) v
    (s.relative slot (Fin.natAdd 1)).eval M w = (t.relative slot (Fin.natAdd 1)).eval M w

theorem intervalDiagram_presents {A B : Type} {M : BoolOps A} [BooleanAlgebra B]
    (e : OpsIso M (BoolOps.ofAlgebra B)) (d : A) :
    PresentsDiagram (intervalDiagram M d) (intervalOps (e.toEquiv d)) (fun a => restrictTo (e.toEquiv d) (e.toEquiv a)) := by
  intro n v s t
  dsimp only [intervalDiagram]
  rw [← e.toEquiv.injective.eq_iff,e.term,e.term,OpsIso.comp_append,Term.eval_relative,Term.eval_relative]
  simp only [Fin.append_right,Subtype.val_inj,Function.comp_apply]
  let predicate (b : B) := s.eval (intervalOps b) (fun i => restrictTo b (e.toEquiv (v i))) =
    t.eval (intervalOps b) (fun i => restrictTo b (e.toEquiv (v i)))
  exact iff_of_eq (congrArg predicate (Fin.append_left (e.toEquiv ∘ (fun _ : Fin 1 => d)) (e.toEquiv ∘ v) 0))

theorem intervalDiagram_surjective {A B : Type} {M : BoolOps A} [BooleanAlgebra B]
    (e : OpsIso M (BoolOps.ofAlgebra B)) (d : A) :
    Function.Surjective (fun a => restrictTo (e.toEquiv d) (e.toEquiv a)) := by
  intro x
  refine ⟨e.toEquiv.symm x.val,?_⟩
  dsimp only
  rw [e.toEquiv.apply_symm_apply,restrictTo_coe]

def codedChartMatch (c : Baire) (t : Tables) (v : Vertex) (d : ℕ) : Prop :=
  DiagramBF (chartDiagram (sectorTags (diagonalTree c) v)) (intervalDiagram (readTables t) d)
    (ω+2) Fin.elim0 Fin.elim0

theorem measurable_chart_match (v : Vertex) (d : ℕ) :
    Measurable fun p : Baire × Tables => codedChartMatch p.1 p.2 v d := by
  let := chartCodes_countable
  apply measurable_diagramBF (D := fun p : Baire × Tables => chartDiagram (sectorTags (diagonalTree p.1) v))
    (E := fun p => intervalDiagram (readTables p.2) d)
  · intro n u s t
    exact (chartDiagram_measurable v u s t).comp measurable_fst
  · intro n u s t
    exact ((measurable_tables.term _ _).eq (measurable_tables.term _ _)).comp measurable_snd
  · have lim := Cardinal.isSuccLimit_omega 1
    have ho : (ω : Ordinal.{0}) < ω₁ := Ordinal.omega0_lt_omega_one
    have h : ω+1+1 < ω₁ := lim.succ_lt (lim.succ_lt ho)
    simpa only [add_assoc,one_add_one_eq_two] using h

theorem codedChartMatch_iff {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X]
    [Countable (Clopens X)] {c : Baire} (isolation : ChartIsolation (diagonalTree c))
    (t : Tables) (e : OpsIso (readTables t) (BoolOps.ofAlgebra (Clopens X))) (v : Vertex) (d : ℕ) :
    codedChartMatch c t v d ↔ Nonempty (VertexChart (sectorTags (diagonalTree c) v) ≃ₜ (e.toEquiv d : Clopens X)) := by
  let S := sectorTags (diagonalTree c) v
  let C := e.toEquiv d
  let := intervalAlgebra C
  obtain ⟨ht,hz,hc⟩ := chart_stone S
  let := clopen_compactSpace C
  obtain ⟨σ,lev,iso⟩ := isolation v
  have self : Models (BoolOps.ofAlgebra (Clopens (VertexChart S))) σ := (iso _).mpr ⟨OrderIso.refl _⟩
  have pre := diagramBF_iff (chartRestrict_surjective S) (intervalDiagram_surjective e d)
    (chart_presentsDiagram S) (intervalDiagram_presents e d) (ω+2)
    (Fin.elim0 : Fin 0 → ChartCodes) (Fin.elim0 : Fin 0 → ℕ)
  have ltup : chartRestrict S ∘ (Fin.elim0 : Fin 0 → ChartCodes) = Fin.elim0 := Subsingleton.elim _ _
  have rtup : (fun a => restrictTo C (e.toEquiv a)) ∘ (Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 := Subsingleton.elim _ _
  rw [ltup,rtup] at pre
  apply pre.trans
  change BF (BoolOps.ofAlgebra (Clopens (VertexChart S))) (BoolOps.ofAlgebra (Iic C)) (ω+2) Fin.elim0 Fin.elim0 ↔ _
  constructor
  · intro bf
    obtain ⟨g⟩ := (iso (Iic C)).mp ((lev.transfer bf).mp self)
    exact ⟨homeomorphOfClopens (g.trans (clopenRestriction C))⟩
  · rintro ⟨g⟩
    let iso := OpsIso.ofOrder ((clopensOfHomeomorph g).trans (clopenRestriction C).symm)
    have bf := iso.bf (ω+2) (Fin.elim0 : Fin 0 → Clopens (VertexChart S))
    exact (Subsingleton.elim (iso.toEquiv ∘ (Fin.elim0 : Fin 0 → Clopens (VertexChart S))) Fin.elim0) ▸ bf

end BooleanScott
