module
public import BooleanScott.ChartComparison
public import BooleanScott.BooleanTables

/-! Joint Borel truth of the geometric guard follows from chart isolation.
Only the retained-edge tests and the comparison with a variable reference
chart depend on the tree. All syntax used in the other tests is fixed.
No measurable choice of chart Scott sentences is required. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory Ordinal Set TopologicalSpace Descriptive
open scoped Ordinal

def fixedConditions : StonePredicate 0 := fun X _ u =>
  (∀ v, ∃ z, (vertexLocus v).points X = {z}) ∧
  (∀ p : DistinctPair, (vertexLocus p.val.1).points X ∩ (vertexLocus p.val.2).points X = ∅) ∧
  cutClause X u ∧ ∀ j, reserveClause j X u

theorem fixedConditions_test : StoneDef .pi (ω+2) fixedConditions := by
  let α : Ordinal.{0} := ω+2
  have pos : 0 < α := by dsimp [α]; positivity
  have le : ω ≤ α := le_self_add ..
  have one := StoneDef.allOf pos (fun v : Vertex => (singleton_test (.inl v)).piOmega.raise le)
  have apart := StoneDef.allOf pos (fun p : DistinctPair => (different_test p.val.1 p.val.2).piOmega.raise le)
  exact one.and (apart.and (cutClause_test.and (StoneDef.allOf pos reserveClause_test) pos) pos) pos

theorem geometric_borel_of_chart_isolation (charts : ∀ c, ChartIsolation (diagonalTree c)) : TreeGuardBorel := by
  classical
  obtain ⟨φ,hφ,truth⟩ := fixedConditions_test
  choose edge he te using fun v i => (endpoint_test v i).piOmega
  have tagdef (v : Vertex) : StoneDef .pi ω (Hits (vertexLocus v)) := (tagAnchor_finiteHit _).incidence.piOmega
  choose tag ht tt using tagdef
  let tests (c : Baire) (t : Tables) := Models (readTables t) φ ∧
    (∀ (v : Vertex) (i : ℕ), v++[i] ∈ diagonalTree c → Models (readTables t) (edge v i)) ∧
    ∀ v : Vertex, ∃ d : ℕ, (tag v).Holds (readTables t) (fun _ => d) ∧ codedChartMatch c t v d
  have borel : Measurable fun p : Baire × Tables => tests p.1 p.2 := by
    apply Measurable.and ((measurable_tables.formula φ Fin.elim0).comp measurable_snd)
    apply Measurable.and
    · apply Measurable.forall; intro v
      apply Measurable.forall; intro i
      have member := measurableSet_setOfPred.mp (clopen_tree_membership (v++[i])).isOpen.measurableSet
      exact (member.comp measurable_fst).imp ((measurable_tables.formula (edge v i) Fin.elim0).comp measurable_snd)
    · exact Measurable.forall fun v => Measurable.exists fun d =>
        ((measurable_tables.formula (tag v) (fun _ => d)).comp measurable_snd).and (measurable_chart_match v d)
  have interpret (c : Baire) (t : Tables) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
      [ZeroDimensionalSpace X] [Countable (Clopens X)] (e : OpsIso (readTables t) (BoolOps.ofAlgebra (Clopens X))) :
      tests c t ↔ Nonempty (GuardData (diagonalTree c) X) := by
    apply Iff.trans _ (guardClauses_iff _ X Fin.elim0)
    have fixed := (OpsIso.models hφ e).trans (truth X Fin.elim0)
    have ends (v : Vertex) (i : ℕ) := (OpsIso.models (he v i) e).trans (te v i X Fin.elim0)
    have hit (v : Vertex) (d : ℕ) : (tag v).Holds (readTables t) (fun _ => d) ↔
        Hits (vertexLocus v) X (fun _ => e.toEquiv d) :=
      ((ht v).transfer (e.bf ω (fun _ => d))).trans (tt v X _)
    have chart (v : Vertex) : (∃ d : ℕ, (tag v).Holds (readTables t) (fun _ => d) ∧ codedChartMatch c t v d) ↔
        chartClause (diagonalTree c) v X Fin.elim0 := by
      constructor
      · rintro ⟨d,h,m⟩
        exact ⟨e.toEquiv d,(hit v d).mp h,(codedChartMatch_iff (charts c) t e v d).mp m⟩
      · rintro ⟨C,h,m⟩
        obtain ⟨d,rfl⟩ := e.toEquiv.surjective C
        exact ⟨d,(hit v d).mpr h,(codedChartMatch_iff (charts c) t e v d).mpr m⟩
    constructor
    · rintro ⟨base,active,matchAll⟩
      obtain ⟨one,dis,cut,res⟩ := fixed.mp base
      exact ⟨one,dis,fun ⟨⟨v,i⟩,hi⟩ => (ends v i).mp (active v i hi),
        fun v => (chart v).mp (matchAll v),cut,res⟩
    · rintro ⟨one,dis,active,matchAll,cut,res⟩
      exact ⟨fixed.mpr ⟨one,dis,cut,res⟩,fun v i hi => (ends v i).mpr (active ⟨(v,i),hi⟩),
        fun v => (chart v).mpr (matchAll v)⟩
  have onAlgebra (c : Baire) (t : Tables) (A : Type) [BooleanAlgebra A]
      (e : OpsIso (BoolOps.ofAlgebra A) (readTables t)) :
      tests c t ↔ Nonempty (GuardData (diagonalTree c) (StoneModel A)) := by
    let : Countable A := e.toEquiv.injective.countable
    let := stone_hausdorff A
    let := stone_zeroDimensional A
    let := (stoneRepresentation A).surjective.countable
    exact interpret c t (StoneModel A) (e.symmIso.transIso (OpsIso.ofOrder (stoneRepresentation A)))
  have eq : {p : Baire × Tables | GeometricTableGuard p.1 p.2} =
      {p | PresentsBoolean p.2 ∧ tests p.1 p.2} := by
    ext ⟨c,t⟩
    constructor
    · rintro ⟨A,inst,⟨e⟩,h⟩
      exact ⟨⟨A,inst,⟨e⟩⟩,(onAlgebra c t A e).mpr h⟩
    · rintro ⟨⟨A,inst,⟨e⟩⟩,h⟩
      exact ⟨A,inst,⟨e⟩,(onAlgebra c t A e).mp h⟩
  unfold TreeGuardBorel
  rw [eq]
  exact ((measurableSet_setOfPred.mp borel_presentsBoolean).comp measurable_snd).and borel |>.setOf

theorem negativeResolution_of_chart_isolation_and_absorption
    (charts : ∀ c, ChartIsolation (diagonalTree c)) (criterion : GuardAbsorbsIffBranch) : NegativeResolution :=
  negativeResolution_of_tree_geometry charts (geometric_borel_of_chart_isolation charts) criterion

end BooleanScott
