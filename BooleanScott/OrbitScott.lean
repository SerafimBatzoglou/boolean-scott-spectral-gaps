module
public import BooleanScott.ScottClauses
public import BooleanScott.Coding

/-! Internal Π_ω definitions of all finite-tuple orbits give an actual pure
Π_(ω+2) Scott sentence, isolating the reference from every countable
Boolean algebra. An arbitrary competing model is constrained by the clauses. -/
@[expose] public section
namespace BooleanScott
open Ordinal
open scoped Ordinal
variable {A : Type} [BooleanAlgebra A] [Countable A]

def DefinesOrbits (D : TupleTests A) : Prop := ∀ {n} (v w : Fin n → A),
  (D v).Holds (BoolOps.ofAlgebra A) w ↔ ∃ e : A ≃o A, ∀ i, e (v i) = w i

omit [Countable A] in
theorem reference_scottClauses (D : TupleTests A) (orb : DefinesOrbits D) :
    ∀ q w, ScottClause.truth D (BoolOps.ofAlgebra A) q w := by
  intro q w
  cases q with
  | initial =>
    exact (orb _ _).mpr ⟨OrderIso.refl A, fun i => i.elim0⟩
  | order n v i j =>
    intro h
    obtain ⟨e,he⟩ := (orb _ _).mp h
    change v i ≤ v j ↔ w i ⊓ w j = w i
    rw [inf_eq_left,← he i,← he j,e.le_iff_le]
  | forth n v a =>
    change Fin n → A at w
    intro h
    obtain ⟨e,he⟩ := (orb _ _).mp h
    refine ⟨e a, (orb _ _).mpr ⟨e,fun j => ?_⟩⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [prepend,he]
  | back n v =>
    change Fin (1+n) → A at w
    intro h
    obtain ⟨e,he⟩ := (orb _ _).mp h
    change ∀ i : Fin n, e (v i) = w (Fin.natAdd 1 i) at he
    refine ⟨e.symm (w (Fin.castAdd n (0 : Fin 1))), (orb _ _).mpr ⟨e,fun j => ?_⟩⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Subsingleton.elim i 0]
      simp [prepend]
    · simp only [prepend,Fin.append_right]
      exact he i

theorem iso_of_scottClauses (D : TupleTests A) {B : Type} [BooleanAlgebra B] [Countable B]
    (h : ∀ q w, ScottClause.truth D (BoolOps.ofAlgebra B) q w) : Nonempty (A ≃o B) := by
  let R {n : ℕ} (v : Fin n → A) (w : Fin n → B) := (D v).Holds (BoolOps.ofAlgebra B) w
  apply countable_back_and_forth R (h .initial Fin.elim0)
  · intro n v w hr i j
    exact (h (.order n v i j) w hr).trans inf_eq_left
  · intro n v w hr a
    exact h (.forth n v a) w hr
  · intro n v w hr b
    have tail : prepend b w ∘ Fin.natAdd 1 = w := funext (fun i => Fin.append_right _ _ i)
    exact h (.back n v) (prepend b w) (tail.symm ▸ hr)

theorem chartScott_of_orbits {α : Ordinal.{0}} (D : TupleTests A) (level : ∀ {n} (v : Fin n → A), AtLevel .pi α (D v))
    (orb : DefinesOrbits D) :
    ∃ σ : Formula 0, AtLevel .pi (α+2) σ ∧ ∀ (B : Type) [Countable B] [BooleanAlgebra B],
      Models (BoolOps.ofAlgebra B) σ ↔ Nonempty (A ≃o B) := by
  obtain ⟨σ,hσ,truth⟩ := scottSentenceOfTests D level
  have self := (truth A (BoolOps.ofAlgebra A)).mpr (reference_scottClauses D orb)
  refine ⟨σ,hσ,fun B _ _ => ⟨fun hb => iso_of_scottClauses D ((truth B _).mp hb),?_⟩⟩
  rintro ⟨e⟩
  exact (OpsIso.models hσ (OpsIso.ofOrder e)).mp self

end BooleanScott
