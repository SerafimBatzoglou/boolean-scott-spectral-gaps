module
public import BooleanScott.OrbitScott

/-! A countable reference algebra needs only countably many separating
finite-level tests, even though the set of infinitary formulas at a given
finite level need not be countable. The levels may increase with the
competitor; their conjunction is a genuine Π_ω tuple formula. -/
@[expose] public section
namespace BooleanScott
open Ordinal
open scoped Ordinal

def FiniteAgreement {A : Type} (M : BoolOps A) {n : ℕ} (v w : Fin n → A) : Prop :=
  ∀ (k : ℕ) (p : Polarity) (φ : Formula n), AtLevel p (k : Ordinal.{0}) φ →
    (φ.Holds M v ↔ φ.Holds M w)

private theorem asFiniteSigma {n k : ℕ} {p : Polarity} {φ : Formula n} (h : AtLevel p (k : Ordinal.{0}) φ) :
    ∃ (m : ℕ) (ψ : Formula n), AtLevel .sigma (m : Ordinal.{0}) ψ ∧
      ∀ (A : Type) (M : BoolOps A) (v : Fin n → A), ψ.Holds M v ↔ φ.Holds M v := by
  cases p with
  | sigma => exact ⟨k,φ,h,fun _ _ _ => Iff.rfl⟩
  | pi =>
    let f (_ : Unit) := φ
    exact ⟨k+1,disjoinPi f,by simpa using disjoinPi_level (fun _ : Unit => h),
      fun _ M v => (holds_disjoinPi f M v).trans ⟨fun ⟨_,h⟩ => h,fun h => ⟨(),h⟩⟩⟩

theorem finite_separator {A : Type} (M : BoolOps A) {n : ℕ} {v w : Fin n → A}
    (h : ¬ FiniteAgreement M v w) : ∃ (k : ℕ) (φ : Formula n),
    AtLevel .sigma (k : Ordinal.{0}) φ ∧ φ.Holds M v ∧ ¬ φ.Holds M w := by
  classical
  obtain ⟨k,hk⟩ := Classical.not_forall.mp h
  obtain ⟨p,hp⟩ := Classical.not_forall.mp hk
  obtain ⟨φ,hφ⟩ := Classical.not_forall.mp hp
  obtain ⟨lev,diff⟩ := Classical.not_imp.mp hφ
  by_cases yes : φ.Holds M v
  · have no : ¬ φ.Holds M w := fun hw => diff (iff_of_true yes hw)
    obtain ⟨m,ψ,hs,truth⟩ := asFiniteSigma lev
    exact ⟨m,ψ,hs,(truth _ M v).mpr yes,fun hw => no ((truth _ M w).mp hw)⟩
  · have no : φ.Holds M w := by by_contra hn; exact diff (iff_of_false yes hn)
    obtain ⟨m,ψ,hs,truth⟩ := asFiniteSigma lev.negate
    exact ⟨m,ψ,hs,(truth _ M v).mpr ((φ.holds_negate M v).mpr yes),
      fun hw => ((φ.holds_negate M w).mp ((truth _ M w).mp hw)) no⟩

variable {A : Type} [BooleanAlgebra A] [Countable A]

theorem orbit_test_of_finite {n : ℕ} (v : Fin n → A)
    (sufficesForOrbit : ∀ w, FiniteAgreement (BoolOps.ofAlgebra A) v w →
      ∃ e : A ≃o A, ∀ i, e (v i) = w i) :
    ∃ ψ : Formula n, AtLevel .pi ω ψ ∧ ∀ w, ψ.Holds (BoolOps.ofAlgebra A) w ↔
      ∃ e : A ≃o A, ∀ i, e (v i) = w i := by
  classical
  let M := BoolOps.ofAlgebra A
  have sep (w : Fin n → A) : ∃ (k : ℕ) (φ : Formula n), AtLevel .sigma (k : Ordinal.{0}) φ ∧
      φ.Holds M v ∧ (φ.Holds M w → ∃ e : A ≃o A, ∀ i, e (v i) = w i) := by
    by_cases eq : FiniteAgreement M v w
    · exact ⟨0,.qf (.eq .zero .zero),.qf _ _ _,rfl,fun _ => sufficesForOrbit w eq⟩
    · obtain ⟨k,φ,hφ,hv,hw⟩ := finite_separator M eq
      exact ⟨k,φ,hφ,hv,fun h => (hw h).elim⟩
  choose k φ hφ hv hw using sep
  let f (w : Fin n → A) := (φ w).pad
  refine ⟨indexedPi (fun _ : Fin n → A => 0) f,
    indexedPi_level (fun w => (k w : Ordinal.{0})) (fun w => natCast_lt_omega0 (k w))
      (fun w => (hφ w).rename _),fun w => ?_⟩
  rw [holds_indexedPi]
  constructor
  · intro all
    exact hw w (((φ w).holds_pad M Fin.elim0 w).mp (all w Fin.elim0))
  · rintro ⟨e,he⟩ z u
    apply ((φ z).holds_pad M u w).mpr
    let iso := OpsIso.ofOrder e
    have same : iso.toEquiv ∘ v = w := funext he
    exact same ▸ ((hφ z).transfer (iso.bf (k z) v)).mp (hv z)

theorem chartScott_of_finite_types
    (complete : ∀ {n : ℕ} (v w : Fin n → A), FiniteAgreement (BoolOps.ofAlgebra A) v w →
      ∃ e : A ≃o A, ∀ i, e (v i) = w i) :
    ∃ σ : Formula 0, AtLevel .pi (ω+2) σ ∧ ∀ (B : Type) [Countable B] [BooleanAlgebra B],
      Models (BoolOps.ofAlgebra B) σ ↔ Nonempty (A ≃o B) := by
  classical
  have each (n : ℕ) (v : Fin n → A) := orbit_test_of_finite v (complete v)
  choose D lev truth using each
  exact chartScott_of_orbits (fun {n} v => D n v) (fun {n} v => lev n v) (fun {n} v => truth n v)

end BooleanScott
