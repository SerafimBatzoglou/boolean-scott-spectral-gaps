module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

/-! The pure Boolean signature. Indices in a finite block are placed before
the old variables. Countably many branches are indexed by naturals; dummy
false/true branches encode finite and empty disjunctions/conjunctions. -/
@[expose] public section
namespace BooleanScott
open Ordinal
open scoped Ordinal

structure BoolOps (A : Type) where
  zero : A
  one : A
  compl : A → A
  meet : A → A → A
  join : A → A → A

def BoolOps.ofAlgebra (A : Type) [BooleanAlgebra A] : BoolOps A :=
  ⟨⊥, ⊤, (·ᶜ), (· ⊓ ·), (· ⊔ ·)⟩

inductive Term (n : ℕ)
  | var (i : Fin n)
  | zero | one
  | compl (t : Term n)
  | meet (s t : Term n)
  | join (s t : Term n)
  deriving Countable

def Term.eval {n : ℕ} {A : Type} (M : BoolOps A) (v : Fin n → A) : Term n → A
  | .var i => v i
  | .zero => M.zero
  | .one => M.one
  | .compl t => M.compl (t.eval M v)
  | .meet s t => M.meet (s.eval M v) (t.eval M v)
  | .join s t => M.join (s.eval M v) (t.eval M v)

inductive QF (n : ℕ)
  | eq (s t : Term n)
  | neg (q : QF n)
  | and (p q : QF n)

def QF.Holds {n : ℕ} {A : Type} (M : BoolOps A) (v : Fin n → A) : QF n → Prop
  | .eq s t => s.eval M v = t.eval M v
  | .neg p => ¬ p.Holds M v
  | .and p q => p.Holds M v ∧ q.Holds M v

inductive Formula : ℕ → Type
  | qf {n} (p : QF n) : Formula n
  | sigma {n} (k : ℕ → ℕ) (p : (i : ℕ) → Formula (k i + n)) : Formula n
  | pi {n} (k : ℕ → ℕ) (p : (i : ℕ) → Formula (k i + n)) : Formula n

def Formula.Holds {A : Type} (M : BoolOps A) : {n : ℕ} → Formula n → (Fin n → A) → Prop
  | _, .qf q, v => q.Holds M v
  | _, .sigma k p, v => ∃ (i : ℕ) (u : Fin (k i) → A), (p i).Holds M (Fin.append u v)
  | _, .pi k p, v => ∀ (i : ℕ) (u : Fin (k i) → A), (p i).Holds M (Fin.append u v)

inductive Polarity | sigma | pi

/-- The non-effective infinitary hierarchy, allowing arbitrary finite blocks. -/
inductive AtLevel : {n : ℕ} → Polarity → Ordinal.{0} → Formula n → Prop
  | qf {n} (q : QF n) (pol : Polarity) (α : Ordinal) : AtLevel pol α (.qf q)
  | sigma {n} {α : Ordinal} {k : ℕ → ℕ} {p : (i : ℕ) → Formula (k i + n)}
      (β : ℕ → Ordinal) (lt : ∀ i, β i < α) (h : ∀ i, AtLevel .pi (β i) (p i)) :
      AtLevel .sigma α (.sigma k p)
  | pi {n} {α : Ordinal} {k : ℕ → ℕ} {p : (i : ℕ) → Formula (k i + n)}
      (β : ℕ → Ordinal) (lt : ∀ i, β i < α) (h : ∀ i, AtLevel .sigma (β i) (p i)) :
      AtLevel .pi α (.pi k p)

def Models {A : Type} (M : BoolOps A) (φ : Formula 0) := φ.Holds M Fin.elim0

/-- Scott isolation among countable Boolean algebras. An order isomorphism
between Boolean algebras preserves their Boolean operations. -/
def RankAtMost (b : Ordinal.{0}) (A : Type) [BooleanAlgebra A] : Prop :=
  ∃ σ : Formula 0, AtLevel .pi (b + 1) σ ∧
    ∀ (B : Type) [Countable B] [BooleanAlgebra B],
      Models (BoolOps.ofAlgebra B) σ ↔ Nonempty (A ≃o B)

/-- Precise target of the project, including satisfiability and all finite
or countably infinite candidate Boolean algebras. -/
def NegativeResolution : Prop :=
  ∀ b : Ordinal.{0}, b < ω₁ → ∃ φ : Formula 0, AtLevel .pi (ω + 4) φ ∧
    (∃ (A : Type) (_ : Countable A) (_ : BooleanAlgebra A), Models (BoolOps.ofAlgebra A) φ) ∧
    ∀ (A : Type) [Countable A] [BooleanAlgebra A],
      Models (BoolOps.ofAlgebra A) φ → ¬ RankAtMost b A

def AtomMatch {A B : Type} (M : BoolOps A) (N : BoolOps B) {n : ℕ}
    (v : Fin n → A) (w : Fin n → B) : Prop :=
  ∀ s t : Term n, (s.eval M v = t.eval M v ↔ s.eval N w = t.eval N w)

theorem AtomMatch.qf_iff {A B : Type} {M : BoolOps A} {N : BoolOps B}
    {n : ℕ} {v : Fin n → A} {w : Fin n → B} (h : AtomMatch M N v w) (q : QF n) :
    q.Holds M v ↔ q.Holds N w := by
  induction q with
  | eq s t => exact h s t
  | neg _ ih => exact not_congr ih
  | and _ _ ih jh => exact and_congr ih jh

/-- Symmetric back-and-forth, comparing finite tuple extensions in each
direction at each strictly smaller ordinal. -/
def BF {A B : Type} (M : BoolOps A) (N : BoolOps B) (α : Ordinal.{0})
    {n : ℕ} (v : Fin n → A) (w : Fin n → B) : Prop :=
  AtomMatch M N v w ∧ ∀ β : Set.Iio α, ∀ k : ℕ,
    (∀ u : Fin k → A, ∃ z : Fin k → B, BF M N β.val (Fin.append u v) (Fin.append z w)) ∧
    (∀ z : Fin k → B, ∃ u : Fin k → A, BF M N β.val (Fin.append u v) (Fin.append z w))
termination_by α
decreasing_by all_goals exact β.property

theorem AtLevel.transfer {A B : Type} {M : BoolOps A} {N : BoolOps B}
    {n : ℕ} {φ : Formula n} {pol : Polarity} {α : Ordinal.{0}}
    (lev : AtLevel pol α φ) {v : Fin n → A} {w : Fin n → B}
    (matchAt : BF M N α v w) : φ.Holds M v ↔ φ.Holds N w := by
  induction lev with
  | qf q pol α =>
    rw [BF] at matchAt
    exact matchAt.1.qf_iff q
  | sigma β lt h ih =>
    rw [BF] at matchAt
    constructor
    · rintro ⟨i,u,hu⟩
      obtain ⟨z,hz⟩ := (matchAt.2 ⟨β i, lt i⟩ _).1 u
      exact ⟨i,z,(ih i hz).1 hu⟩
    · rintro ⟨i,z,hz⟩
      obtain ⟨u,hu⟩ := (matchAt.2 ⟨β i, lt i⟩ _).2 z
      exact ⟨i,u,(ih i hu).2 hz⟩
  | pi β lt h ih =>
    rw [BF] at matchAt
    constructor
    · intro old i z
      obtain ⟨u,hu⟩ := (matchAt.2 ⟨β i, lt i⟩ _).2 z
      exact (ih i hu).1 (old i u)
    · intro old i u
      obtain ⟨z,hz⟩ := (matchAt.2 ⟨β i, lt i⟩ _).1 u
      exact (ih i hz).2 (old i z)

theorem not_bf_of_low_rank_noniso {A B : Type} [Countable A] [Countable B]
    [BooleanAlgebra A] [BooleanAlgebra B] {b : Ordinal.{0}}
    (low : RankAtMost b A) (hne : ¬ Nonempty (A ≃o B)) :
    ¬ BF (BoolOps.ofAlgebra A) (BoolOps.ofAlgebra B) (b+1) Fin.elim0 Fin.elim0 := by
  intro hb
  obtain ⟨σ, hσ, isolates⟩ := low
  exact hne ((isolates B).mp ((hσ.transfer hb).mp ((isolates A).mpr ⟨OrderIso.refl A⟩)))

end BooleanScott
