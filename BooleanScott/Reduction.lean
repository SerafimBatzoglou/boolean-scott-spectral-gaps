module
public import BooleanScott.Coding
public import Mathlib.Order.BooleanAlgebra.Basic

/-! The endpoint reduction isolates the geometric obligations. It neither
asserts nor assumes globally that the required construction exists. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory Set Ordinal
open scoped Ordinal

def OpsIso.symmIso {A B : Type} {M : BoolOps A} {N : BoolOps B}
    (e : OpsIso M N) : OpsIso N M where
  toEquiv := e.toEquiv.symm
  zero_eq := e.toEquiv.symm_apply_eq.mpr e.zero_eq.symm
  one_eq := e.toEquiv.symm_apply_eq.mpr e.one_eq.symm
  compl_eq := fun b => by apply e.toEquiv.injective; simp [e.compl_eq]
  meet_eq := fun b c => by apply e.toEquiv.injective; simp [e.meet_eq]
  join_eq := fun b c => by apply e.toEquiv.injective; simp [e.join_eq]

def OpsIso.transIso {A B C : Type} {M : BoolOps A} {N : BoolOps B} {O : BoolOps C}
    (e : OpsIso M N) (f : OpsIso N O) : OpsIso M O where
  toEquiv := e.toEquiv.trans f.toEquiv
  zero_eq := (congrArg f.toEquiv e.zero_eq).trans f.zero_eq
  one_eq := (congrArg f.toEquiv e.one_eq).trans f.one_eq
  compl_eq := fun a => (congrArg f.toEquiv (e.compl_eq a)).trans (f.compl_eq _)
  meet_eq := fun a b => (congrArg f.toEquiv (e.meet_eq a b)).trans (f.meet_eq _ _)
  join_eq := fun a b => (congrArg f.toEquiv (e.join_eq a b)).trans (f.join_eq _ _)

/-- Legitimacy of a table has a semantic definition, including its enumeration.
Only countably infinite algebras can have an isomorphism onto such a table. -/
def PresentsBoolean (t : Tables) : Prop :=
  ∃ (A : Type) (_ : BooleanAlgebra A), Nonempty (OpsIso (BoolOps.ofAlgebra A) (readTables t))

structure AbsorptionConstruction (R : Type) [BooleanAlgebra R] where
  sentence : Baire → Formula 0
  level : ∀ c, AtLevel .pi (ω+4) (sentence c)
  satisfiable : ∀ c, ∃ (A : Type) (_ : Countable A) (_ : BooleanAlgebra A),
    Models (BoolOps.ofAlgebra A) (sentence c)
  infinite_models : ∀ c (A : Type) [Countable A] [BooleanAlgebra A],
    Models (BoolOps.ofAlgebra A) (sentence c) → Infinite A
  borel : MeasurableSet {p : Baire × Tables |
    PresentsBoolean p.2 ∧ Models (readTables p.2) (sentence p.1)}
  absorption : ∀ c (A : Type) [Countable A] [BooleanAlgebra A],
    Models (BoolOps.ofAlgebra A) (sentence c) →
      (Nonempty (A ≃o A × R) ↔ HasBranch (diagonalTree c))

theorem negativeResolution_of_construction {R : Type} [BooleanAlgebra R] [Countable R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (G : AbsorptionConstruction R) :
    NegativeResolution := by
  classical
  intro b hb
  have hsucc : b + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).succ_lt hb
  let RR := BoolOps.ofAlgebra R
  let bad (t : Tables) := ¬ BF (readTables t) ((readTables t).prod RR) (b+1) Fin.elim0 Fin.elim0
  have hbad : Measurable bad := (borel_bf measurable_tables (measurable_tables.prodRight RR)
    (b+1) hsucc Fin.elim0 Fin.elim0).not
  obtain ⟨c,branchless,escape⟩ := escape_comparison
    {p : Baire × Tables | PresentsBoolean p.2 ∧ Models (readTables p.2) (G.sentence p.1)}
    {p : Baire × Tables | bad p.2} G.borel (hbad.comp measurable_snd).setOf (by
      rintro c t ⟨⟨A,inst,⟨e⟩⟩,hφ⟩ hfail branch
      let : Countable A := e.toEquiv.injective.countable
      have hA := (OpsIso.models (G.level c) e).mpr hφ
      obtain ⟨f⟩ := (G.absorption c A hA).mpr branch
      let iso := (e.symmIso.transIso (OpsIso.ofOrder f)).transIso (e.prodRight RR)
      have hbf := iso.bf (b+1) (Fin.elim0 : Fin 0 → ℕ)
      have heq : iso.toEquiv ∘ (Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 := Subsingleton.elim _ _
      exact hfail (heq ▸ hbf))
  refine ⟨G.sentence c,G.level c,G.satisfiable c,?_⟩
  intro A hcnt inst hA low
  let : Infinite A := G.infinite_models c A hA
  let e : A ≃ ℕ := Classical.choice inferInstance
  let t := writeTables (BoolOps.ofAlgebra A) e
  let enum := enumerationIso (BoolOps.ofAlgebra A) e
  have hguard : PresentsBoolean t ∧ Models (readTables t) (G.sentence c) :=
    ⟨⟨A,inst,⟨enum⟩⟩,(OpsIso.models (G.level c) enum).mp hA⟩
  have matchAt : BF (readTables t) ((readTables t).prod RR) (b+1) Fin.elim0 Fin.elim0 :=
    Classical.not_not.mp (escape t hguard)
  obtain ⟨σ,hσ,hiso⟩ := low
  have ht := (OpsIso.models hσ enum).mp ((hiso A).mpr ⟨OrderIso.refl A⟩)
  have hprod := (OpsIso.models hσ (enum.prodRight RR)).mpr ((hσ.transfer matchAt).mp ht)
  exact branchless ((G.absorption c A hA).mp ((hiso (A × R)).mp hprod))

end BooleanScott
