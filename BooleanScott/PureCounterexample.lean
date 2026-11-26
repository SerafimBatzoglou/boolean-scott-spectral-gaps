module
public import BooleanScott.NegativeResolution

/-! A literal sentence extending the Boolean algebra axioms, interpreted
over arbitrary operation structures of the pure signature. The rank bound
even fails when Scott sentences range over all countable structures. -/
@[expose] public section
namespace BooleanScott
open Ordinal
open scoped Ordinal

noncomputable def booleanLawSentence : Formula 0 :=
  indexedPi (fun _ : Fin 11 => 3) (fun i => .qf (.eq (booleanEquation i).1 (booleanEquation i).2))

theorem booleanLawSentence_level : AtLevel .pi 1 booleanLawSentence :=
  indexedPi_level (fun _ => 0) (fun _ => zero_lt_one) (fun _ => .qf _ _ _)

theorem booleanLawSentence_models {A : Type} (M : BoolOps A) :
    Models M booleanLawSentence ↔ SatisfiesBooleanEquations M := by
  unfold Models booleanLawSentence
  rw [holds_indexedPi]
  have useVars (u : Fin 3 → A) : Fin.append u (Fin.elim0 : Fin 0 → A) = u := by
    funext j; exact Fin.append_left ..
  constructor
  · intro h v i
    simpa only [Formula.Holds,QF.Holds,useVars] using h i v
  · intro h i v
    simpa only [Formula.Holds,QF.Holds,useVars] using h v i

def OperationRankAtMost {A : Type} (b : Ordinal.{0}) (M : BoolOps A) : Prop :=
  ∃ σ : Formula 0, AtLevel .pi (b+1) σ ∧ ∀ (B : Type) [Countable B] (N : BoolOps B),
    Models N σ ↔ Nonempty (OpsIso M N)

theorem rankAtMost_of_operationRank {b : Ordinal.{0}} {A : Type} [BooleanAlgebra A]
    (h : OperationRankAtMost b (BoolOps.ofAlgebra A)) : RankAtMost b A := by
  obtain ⟨σ,lev,iso⟩ := h
  refine ⟨σ,lev,fun B _ _ => (iso B _).trans ?_⟩
  constructor
  · rintro ⟨e⟩
    exact ⟨{ toEquiv := e.toEquiv
             map_rel_iff' := by
               intro x y
               have meet : e.toEquiv (x ⊓ y) = e.toEquiv x ⊓ e.toEquiv y := e.meet_eq x y
               rw [← inf_eq_left,← inf_eq_left,← meet]
               exact e.toEquiv.injective.eq_iff }⟩
  · rintro ⟨e⟩; exact ⟨OpsIso.ofOrder e⟩

theorem trivial_rankAtMost (b : Ordinal.{0}) {A : Type} [BooleanAlgebra A] (eq : (⊥ : A) = ⊤) : RankAtMost b A := by
  let := subsingleton_of_bot_eq_top eq
  let := uniqueOfSubsingleton (⊥ : A)
  refine ⟨.qf (.eq .zero .one),.qf _ _ _,fun B _ _ => ?_⟩
  change (⊥ : B) = ⊤ ↔ Nonempty (A ≃o B)
  constructor
  · intro h
    let := subsingleton_of_bot_eq_top h
    let := uniqueOfSubsingleton (⊥ : B)
    exact ⟨OrderIso.ofUnique A B⟩
  · rintro ⟨f⟩
    simpa only [f.map_bot,f.map_top] using congrArg f eq

theorem pure_boolean_counterexample (b : Ordinal.{0}) (hb : b < ω₁) :
    ∃ φ : Formula 0, AtLevel .pi (ω+4) φ ∧
      (∀ (A : Type) (M : BoolOps A), Models M φ → SatisfiesBooleanEquations M ∧ M.zero ≠ M.one) ∧
      (∃ (A : Type) (_ : Countable A) (_ : BooleanAlgebra A), Models (BoolOps.ofAlgebra A) φ) ∧
      ∀ (A : Type) [Countable A] (M : BoolOps A), Models M φ → ¬ OperationRankAtMost b M := by
  obtain ⟨ψ,lev,⟨A,ca,ba,sat⟩,high⟩ := negativeResolution b hb
  let test (i : Bool) := if i then ψ else booleanLawSentence
  have levels (i : Bool) : AtLevel .pi (ω+4) (test i) := by
    cases i
    · exact booleanLawSentence_level.liftLevel (one_lt_omega0.le.trans (le_self_add ..))
    · exact lev
  obtain ⟨φ,level,truth⟩ := pi_conjunction test levels (by positivity)
  have models {B : Type} (M : BoolOps B) : Models M φ ↔ Models M ψ ∧ SatisfiesBooleanEquations M := by
    apply (truth B M Fin.elim0).trans
    constructor
    · intro h; exact ⟨h true,(booleanLawSentence_models M).mp (h false)⟩
    · intro h i; cases i
      · exact (booleanLawSentence_models M).mpr h.2
      · exact h.1
  have lawful {B : Type} (M : BoolOps B) (h : Models M φ) : SatisfiesBooleanEquations M ∧ M.zero ≠ M.one := by
    obtain ⟨accept,laws⟩ := (models M).mp h
    refine ⟨laws,fun eq => ?_⟩
    let := algebraOfEquations M laws
    let := subsingleton_of_bot_eq_top (show (⊥ : B)=⊤ from eq)
    exact high B accept (trivial_rankAtMost b eq)
  refine ⟨φ,level,fun _ => lawful,⟨A,ca,ba,(models _).mpr ⟨sat,satisfies_ofAlgebra A⟩⟩,?_⟩
  intro B cnt M hφ low
  obtain ⟨accept,laws⟩ := (models M).mp hφ
  let := algebraOfEquations M laws
  exact high B accept (rankAtMost_of_operationRank low)

end BooleanScott
