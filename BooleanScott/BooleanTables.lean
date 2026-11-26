module
public import BooleanScott.Reduction

/-! Legitimacy of a table on ℕ is Borel, including the proof that passing
the equations constructs an actual Boolean algebra with these exact operations. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory

/-- Commutativity, associativity, the two absorptions, distributivity,
least and greatest elements, and the two complement identities. -/
def booleanEquation : Fin 11 → Term 3 × Term 3 :=
  let x : Term 3 := .var 0
  let y : Term 3 := .var 1
  let z : Term 3 := .var 2
  ![(.join x y, .join y x), (.join (.join x y) z, .join x (.join y z)),
    (.meet x y, .meet y x), (.meet (.meet x y) z, .meet x (.meet y z)),
    (.join x (.meet x y), x), (.meet x (.join x y), x),
    (.join x (.meet y z), .meet (.join x y) (.join x z)),
    (.join .zero x, x), (.join x .one, .one),
    (.meet x (.compl x), .zero), (.join x (.compl x), .one)]

def SatisfiesBooleanEquations {A : Type} (M : BoolOps A) : Prop :=
  ∀ (v : Fin 3 → A) (i : Fin 11),
    (booleanEquation i).1.eval M v = (booleanEquation i).2.eval M v

theorem satisfies_ofAlgebra (A : Type) [BooleanAlgebra A] :
    SatisfiesBooleanEquations (BoolOps.ofAlgebra A) := by
  intro v i
  fin_cases i
  · exact sup_comm _ _
  · exact sup_assoc _ _ _
  · exact inf_comm _ _
  · exact inf_assoc _ _ _
  · exact sup_inf_self
  · exact inf_sup_self
  · exact sup_inf_left _ _ _
  · exact bot_sup_eq _
  · exact sup_top_eq _
  · exact inf_compl_eq_bot
  · exact sup_compl_eq_top

@[instance_reducible] def algebraOfEquations {A : Type} (M : BoolOps A)
    (h : SatisfiesBooleanEquations M) : BooleanAlgebra A := by
  let h3 (i : Fin 11) (a b c : A) := h ![a,b,c] i
  let := (⟨M.join⟩ : Max A)
  let := (⟨M.meet⟩ : Min A)
  let := Lattice.mk' (fun a b => h3 0 a b a) (h3 1)
    (fun a b => h3 2 a b a) (h3 3) (fun a b => h3 4 a b a) (fun a b => h3 5 a b a)
  let : DistribLattice A := { (inferInstance : Lattice A) with
    le_sup_inf := fun a b c => (show a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) from h3 6 a b c).ge }
  exact {
    compl := M.compl, top := M.one, bot := M.zero
    le_top := fun a => sup_eq_right.mp (h3 8 a a a)
    bot_le := fun a => sup_eq_right.mp (h3 7 a a a)
    inf_compl_le_bot := fun a => (show a ⊓ M.compl a = M.zero from h3 9 a a a).le
    top_le_sup_compl := fun a => (show a ⊔ M.compl a = M.one from h3 10 a a a).ge }

theorem presentsBoolean_iff_equations (t : Tables) :
    PresentsBoolean t ↔ SatisfiesBooleanEquations (readTables t) := by
  constructor
  · rintro ⟨A,ba,⟨e⟩⟩ v i
    let u := e.toEquiv.symm ∘ v
    have hu : e.toEquiv ∘ u = v := by funext j; simp [u]
    have hv := congrArg e.toEquiv (satisfies_ofAlgebra A u i)
    simpa only [e.term,hu] using hv
  · intro h
    let ba := algebraOfEquations (readTables t) h
    refine ⟨ℕ,ba,⟨?_⟩⟩
    exact
      { toEquiv := Equiv.refl ℕ
        zero_eq := rfl
        one_eq := rfl
        compl_eq := fun _ => rfl
        meet_eq := fun _ _ => rfl
        join_eq := fun _ _ => rfl }

theorem borel_presentsBoolean : MeasurableSet {t : Tables | PresentsBoolean t} := by
  simp_rw [presentsBoolean_iff_equations]
  apply Measurable.setOf
  exact Measurable.forall fun v => Measurable.forall fun i =>
    (measurable_tables.term v (booleanEquation i).1).eq (measurable_tables.term v (booleanEquation i).2)

end BooleanScott
