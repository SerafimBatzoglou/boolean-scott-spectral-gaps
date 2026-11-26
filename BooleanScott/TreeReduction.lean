module
public import BooleanScott.GuardSentence
public import BooleanScott.Reduction

/-! The fixed perturbation is the actual clopen algebra of the root row.
The original selection theorem follows from three independent outstanding
obligations about explicit spaces and their geometric guard. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory Set TopologicalSpace Descriptive Ordinal
open scoped Ordinal

abbrev RootRow := TagRow (tagNumber (.inl [])) 0

theorem GuardData.infinite_clopens {T : tree ℕ} {X : Type} [TopologicalSpace X] (G : GuardData T X) :
    Infinite (Clopens X) := by
  choose C hit only using G.isolated_vertex
  apply Infinite.of_injective C
  intro v w eq
  exact only w v (eq ▸ hit v)

def GeometricTableGuard (c : Baire) (t : Tables) : Prop :=
  ∃ (A : Type) (_ : BooleanAlgebra A), Nonempty (OpsIso (BoolOps.ofAlgebra A) (readTables t)) ∧
    Nonempty (GuardData (diagonalTree c) (StoneModel A))

def TreeGuardBorel := MeasurableSet {p : Baire × Tables | GeometricTableGuard p.1 p.2}

def GuardAbsorbsIffBranch := ∀ (c : Baire) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ZeroDimensionalSpace X] [Countable (Clopens X)], GuardData (diagonalTree c) X →
    (Nonempty ((X ⊕ RootRow) ≃ₜ X) ↔ HasBranch (diagonalTree c))

theorem tree_construction (charts : ∀ c, ChartIsolation (diagonalTree c))
    (joint : TreeGuardBorel) (criterion : GuardAbsorbsIffBranch) :
    Nonempty (AbsorptionConstruction (Clopens RootRow)) := by
  classical
  choose σ lev truth using fun c => guardSentence (charts c)
  have model (c : Baire) (A : Type) [Countable A] [BooleanAlgebra A] :
      Models (BoolOps.ofAlgebra A) (σ c) ↔ Nonempty (GuardData (diagonalTree c) (StoneModel A)) := by
    let := stone_zeroDimensional A
    let := stone_hausdorff A
    let := (stoneRepresentation A).surjective.countable
    exact (OpsIso.models (lev c) (OpsIso.ofOrder (stoneRepresentation A))).trans (truth c (StoneModel A))
  refine ⟨⟨σ,lev,?_,?_,?_,?_⟩⟩
  · intro c
    let T := diagonalTree c
    obtain ⟨ht,hz,hc⟩ := witness_stone T
    exact ⟨Clopens (WitnessSpace T),hc,inferInstance,(truth c _).mpr ⟨witness_guard T⟩⟩
  · intro c A _ _ h
    obtain ⟨G⟩ := (model c A).mp h
    let := G.infinite_clopens
    exact Infinite.of_injective _ (stoneRepresentation A).symm.injective
  · have eq : {p : Baire × Tables | PresentsBoolean p.2 ∧ Models (readTables p.2) (σ p.1)} =
        {p | GeometricTableGuard p.1 p.2} := by
      ext ⟨c,t⟩
      constructor
      · rintro ⟨⟨A,inst,⟨e⟩⟩,h⟩
        let : Countable A := e.toEquiv.injective.countable
        exact ⟨A,inst,⟨e⟩,(model c A).mp ((OpsIso.models (lev c) e).mpr h)⟩
      · rintro ⟨A,inst,⟨e⟩,h⟩
        let : Countable A := e.toEquiv.injective.countable
        exact ⟨⟨A,inst,⟨e⟩⟩,(OpsIso.models (lev c) e).mp ((model c A).mpr h)⟩
    rw [eq]
    exact joint
  · intro c A _ _ h
    let := stone_zeroDimensional A
    let := stone_hausdorff A
    let := (stoneRepresentation A).surjective.countable
    obtain ⟨ht,hz,_⟩ := row_stone (tagNumber (.inl [])) 0
    obtain ⟨G⟩ := (model c A).mp h
    exact (algebra_absorption_iff A RootRow).trans (criterion c _ G)

theorem negativeResolution_of_tree_geometry (charts : ∀ c, ChartIsolation (diagonalTree c))
    (joint : TreeGuardBorel) (criterion : GuardAbsorbsIffBranch) : NegativeResolution := by
  obtain ⟨G⟩ := tree_construction charts joint criterion
  let := (row_stone (tagNumber (.inl [])) 0).2.2
  let : MeasurableSpace (Clopens RootRow) := ⊤
  let : MeasurableSingletonClass (Clopens RootRow) := ⟨fun _ => trivial⟩
  exact negativeResolution_of_construction G

end BooleanScott
