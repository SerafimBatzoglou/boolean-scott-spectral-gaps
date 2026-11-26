module
public import BooleanScott.GuardAtoms

/-! Compiling the geometric guard costs exactly the asserted upper bound.
The sole input here is Scott isolation for the vertex charts. Every other
clause has its own explicitly checked finite or limit-level test. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal Descriptive
open scoped Ordinal Classical

abbrev DistinctPair := {p : Vertex × Vertex // p.1 ≠ p.2}
abbrev ActiveEdge (T : tree ℕ) := {p : Vertex × ℕ // p.1 ++ [p.2] ∈ T}
def chartClause (T : tree ℕ) (v : Vertex) : StonePredicate 0 := fun X _ _ =>
  ∃ C : Clopens X, Hits (vertexLocus v) X (fun _ => C) ∧ Nonempty (VertexChart (sectorTags T v) ≃ₜ C)
def cutClause : StonePredicate 0 := fun X _ _ => ∀ C : Clopens X,
  FiniteAnchors X (fun _ => C) ∨ FiniteAnchors X (fun _ => Cᶜ)
def reserveClause (j : ℕ) : StonePredicate 0 := fun X _ _ => ∀ C : Clopens X,
  FiniteAnchors X (fun _ => C) ∨ ReserveCopy j X (fun _ => C)

def guardClauses (T : tree ℕ) : StonePredicate 0 := fun X _ u =>
  (∀ v, ∃ z, (vertexLocus v).points X = {z}) ∧
  (∀ p : DistinctPair, (vertexLocus p.val.1).points X ∩ (vertexLocus p.val.2).points X = ∅) ∧
  (∀ p : ActiveEdge T, (anchorOf (.inr p.val)).points X ⊆ (vertexLocus p.val.1).points X ∪
    (vertexLocus (p.val.1++[p.val.2])).points X) ∧ (∀ v, chartClause T v X u) ∧
  cutClause X u ∧ ∀ j, reserveClause j X u

theorem hits_singleton {X : Type} [TopologicalSpace X] (C : Clopens X) {P : LocalLocus} {z : X}
    (hz : P.points X = {z}) : Hits P X (fun _ => C) ↔ z ∈ C := by
  change ((C : Set X) ∩ P.points X).Nonempty ↔ _
  rw [hz,inter_singleton_nonempty]
  rfl

theorem finiteAnchors_vertices {X : Type} [TopologicalSpace X] (C : Clopens X) (z : Vertex → X)
    (hz : ∀ v, (vertexLocus v).points X = {z v}) :
    FiniteAnchors X (fun _ => C) ↔ {v | z v ∈ C}.Finite := by
  have eq : {v | Hits (vertexLocus v) X (fun _ => C)} = {v | z v ∈ C} := Set.ext (fun v => hits_singleton C (hz v))
  exact iff_of_eq (congrArg Set.Finite eq)

theorem guardClauses_iff (T : tree ℕ) (X : Type) [TopologicalSpace X] (u : Fin 0 → Clopens X) :
    guardClauses T X u ↔ Nonempty (GuardData T X) := by
  classical
  constructor
  · rintro ⟨one,apart,edge,chart,cut,res⟩
    choose z hz using one
    refine ⟨⟨z,?_,hz,?_,?_,?_,?_⟩⟩
    · intro v w eq
      by_contra neq
      have h := apart ⟨(v,w),neq⟩
      change (vertexLocus v).points X ∩ (vertexLocus w).points X = ∅ at h
      rw [hz,hz,eq,inter_self] at h
      exact singleton_ne_empty _ h
    · intro v i hi
      have h := edge ⟨(v,i),hi⟩
      change _ ⊆ (vertexLocus v).points X ∪ (vertexLocus (v++[i])).points X at h
      simpa only [hz,singleton_union,anchorOf] using h
    · intro v
      obtain ⟨C,hC,iso⟩ := chart v
      exact ⟨C,(hits_singleton C (hz v)).mp hC,iso⟩
    · intro C
      exact (cut C).imp (finiteAnchors_vertices C z hz).mp (finiteAnchors_vertices Cᶜ z hz).mp
    · intro C j inf
      exact (res j C).resolve_left (fun h => inf ((finiteAnchors_vertices C z hz).mp h))
  · rintro ⟨G⟩
    have hz (v : Vertex) : (vertexLocus v).points X = {G.vertex v} := G.private_anchor v
    refine ⟨fun v => ⟨_,hz v⟩,?_,?_,?_,?_,?_⟩
    · rintro ⟨⟨v,w⟩,hn⟩
      change (vertexLocus v).points X ∩ (vertexLocus w).points X = ∅
      rw [hz,hz]
      exact disjoint_iff_inter_eq_empty.mp (disjoint_singleton.mpr (G.distinct.ne hn))
    · rintro ⟨⟨v,i⟩,hi⟩
      change _ ⊆ (vertexLocus v).points X ∪ (vertexLocus (v++[i])).points X
      rw [hz,hz,singleton_union]
      exact G.edge_anchor v i hi
    · intro v
      obtain ⟨C,h,iso⟩ := G.chart v
      exact ⟨C,(hits_singleton C (hz v)).mpr h,iso⟩
    · intro C
      exact (G.finite_or_cofinite C).imp (finiteAnchors_vertices C G.vertex hz).mpr (finiteAnchors_vertices Cᶜ G.vertex hz).mpr
    · intro j C
      by_cases fin : {v | G.vertex v ∈ C}.Finite
      · exact Or.inl ((finiteAnchors_vertices C G.vertex hz).mpr fin)
      · exact Or.inr (G.reserve C j fin)

def ChartIsolation (T : tree ℕ) := ∀ v : Vertex, ∃ σ : Formula 0, AtLevel .pi (ω+2) σ ∧
  ∀ (B : Type) [Countable B] [BooleanAlgebra B], Models (BoolOps.ofAlgebra B) σ ↔
    Nonempty (Clopens (VertexChart (sectorTags T v)) ≃o B)

theorem chartClause_test {T : tree ℕ} (isolation : ChartIsolation T) (v : Vertex) :
    StoneDef .sigma (ω+3) (chartClause T v) := by
  obtain ⟨σ,lev,iso⟩ := isolation v
  obtain ⟨ht,hz,_⟩ := chart_stone (sectorTags T v)
  have named := namedClopen_test lev iso
  have hit : StoneDef .pi (ω+2) (Hits (vertexLocus v)) :=
    ((tagAnchor_finiteHit _).incidence.piOmega).raise (le_self_add ..)
  have h := (hit.and named (by positivity)).someClopen (n := 0)
  exact (show StoneDef .sigma (ω+2+1) (chartClause T v) from h).raise (by rw [add_assoc]; norm_num)

theorem cutClause_test : StoneDef .pi (ω+2) cutClause := by
  have comp := finiteAnchors_test.substitute (m := 1) (fun _ => .compl (.var 0))
  rw [← one_add_one_eq_two,← add_assoc]
  exact (finiteAnchors_test.or comp (by positivity)).everyClopen (n := 0)

theorem reserveClause_test (j : ℕ) : StoneDef .pi (ω+2) (reserveClause j) := by
  have cp := (reserveCopy_test j).piOmega.asSigma
  rw [← one_add_one_eq_two,← add_assoc]
  exact (finiteAnchors_test.or cp (by positivity)).everyClopen (n := 0)

theorem guardSentence {T : tree ℕ} (isolation : ChartIsolation T) :
    ∃ φ : Formula 0, AtLevel .pi (ω+4) φ ∧ ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
      [ZeroDimensionalSpace X] [Countable (Clopens X)],
      Models (BoolOps.ofAlgebra (Clopens X)) φ ↔ Nonempty (GuardData T X) := by
  let α : Ordinal.{0} := ω+4
  have pos : 0 < α := by dsimp [α]; positivity
  have om : ω ≤ α := le_self_add ..
  have smaller : ω+2 ≤ α := by dsimp [α]; gcongr; norm_num
  have h₁ := StoneDef.allOf pos (fun v : Vertex => ((singleton_test (.inl v)).piOmega).raise om)
  have h₂ := StoneDef.allOf pos (fun p : DistinctPair => ((different_test p.val.1 p.val.2).piOmega).raise om)
  have h₃ := StoneDef.allOf pos (fun p : ActiveEdge T => ((endpoint_test p.val.1 p.val.2).piOmega).raise om)
  have chart (v : Vertex) : StoneDef .pi α (chartClause T v) :=
    (chartClause_test isolation v).asPi.raise (by dsimp [α]; rw [add_assoc]; norm_num)
  have h₄ := StoneDef.allOf pos chart
  have h₅ := cutClause_test.raise smaller
  have h₆ := StoneDef.allOf pos (fun j => (reserveClause_test j).raise smaller)
  have whole : StoneDef .pi α (guardClauses T) :=
    h₁.and (h₂.and (h₃.and (h₄.and (h₅.and h₆ pos) pos) pos) pos) pos
  obtain ⟨φ,lev,t⟩ := whole
  exact ⟨φ,lev,fun X _ _ _ _ _ => (t X Fin.elim0).trans (guardClauses_iff T X _)⟩

end BooleanScott
