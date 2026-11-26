module
public import BooleanScott.Relativization

/-! Negation, variable substitution by indices, and indexed quantifier
blocks in the fixed pure Boolean syntax. Each operation carries its truth
and hierarchy statements. -/
@[expose] public section
namespace BooleanScott
open Ordinal

def Polarity.flip : Polarity → Polarity | .sigma => .pi | .pi => .sigma

def Formula.negate {n : ℕ} : Formula n → Formula n
  | .qf q => .qf (.neg q)
  | .sigma k p => .pi k (fun i => (p i).negate)
  | .pi k p => .sigma k (fun i => (p i).negate)

theorem Formula.holds_negate {A : Type} (M : BoolOps A) {n : ℕ} (φ : Formula n) (v : Fin n → A) :
    φ.negate.Holds M v ↔ ¬ φ.Holds M v := by
  classical
  induction φ with
  | qf q => rfl
  | sigma k p ih => simp only [negate,Holds,ih,not_exists]
  | pi k p ih => simp only [negate,Holds,ih,Classical.not_forall]

theorem AtLevel.negate {n : ℕ} {p : Polarity} {α : Ordinal.{0}} {φ : Formula n} (h : AtLevel p α φ) :
    AtLevel p.flip α φ.negate := by
  induction h with
  | qf => exact .qf _ _ _
  | sigma β lt _ ih => exact .pi β lt ih
  | pi β lt _ ih => exact .sigma β lt ih

theorem AtLevel.liftLevel {n : ℕ} {p : Polarity} {α β : Ordinal.{0}} {φ : Formula n}
    (h : AtLevel p α φ) (le : α ≤ β) : AtLevel p β φ := by
  cases h with
  | qf => exact .qf _ _ _
  | sigma γ lt h => exact .sigma γ (fun i => (lt i).trans_le le) h
  | pi γ lt h => exact .pi γ (fun i => (lt i).trans_le le) h

def Term.rename {n m : ℕ} (ρ : Fin n → Fin m) : Term n → Term m
  | .var i => .var (ρ i)
  | .zero => .zero
  | .one => .one
  | .compl t => .compl (t.rename ρ)
  | .meet s t => .meet (s.rename ρ) (t.rename ρ)
  | .join s t => .join (s.rename ρ) (t.rename ρ)

theorem Term.eval_rename {A : Type} (M : BoolOps A) {n m : ℕ} (ρ : Fin n → Fin m)
    (t : Term n) (v : Fin m → A) : (t.rename ρ).eval M v = t.eval M (v ∘ ρ) := by
  induction t <;> simp_all [rename,eval]

def QF.rename {n m : ℕ} (ρ : Fin n → Fin m) : QF n → QF m
  | .eq s t => .eq (s.rename ρ) (t.rename ρ)
  | .neg p => .neg (p.rename ρ)
  | .and p q => .and (p.rename ρ) (q.rename ρ)

theorem QF.holds_rename {A : Type} (M : BoolOps A) {n m : ℕ} (ρ : Fin n → Fin m)
    (q : QF n) (v : Fin m → A) : (q.rename ρ).Holds M v ↔ q.Holds M (v ∘ ρ) := by
  induction q <;> simp_all [rename,Holds,Term.eval_rename]

def Formula.rename {n : ℕ} (φ : Formula n) {m : ℕ} (ρ : Fin n → Fin m) : Formula m :=
  match φ with
  | .qf q => .qf (q.rename ρ)
  | .sigma k f => .sigma k (fun i => (f i).rename (extendVars (k i) ρ))
  | .pi k f => .pi k (fun i => (f i).rename (extendVars (k i) ρ))

theorem AtLevel.rename {n : ℕ} {φ : Formula n} {pol : Polarity} {α : Ordinal.{0}}
    (h : AtLevel pol α φ) {m : ℕ} (ρ : Fin n → Fin m) : AtLevel pol α (φ.rename ρ) := by
  induction h generalizing m with
  | qf => exact .qf _ _ _
  | sigma β lt _ ih => exact .sigma β lt (fun i => ih i _)
  | pi β lt _ ih => exact .pi β lt (fun i => ih i _)

theorem append_comp_extend {A : Type} {n m k : ℕ} (ρ : Fin n → Fin m) (u : Fin k → A) (v : Fin m → A) :
    Fin.append u v ∘ extendVars k ρ = Fin.append u (v ∘ ρ) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [extendVars]

theorem Formula.holds_rename {A : Type} (M : BoolOps A) {n m : ℕ} (φ : Formula n)
    (ρ : Fin n → Fin m) (v : Fin m → A) :
    (φ.rename ρ).Holds M v ↔ φ.Holds M (v ∘ ρ) := by
  induction φ generalizing m with
  | qf q => exact q.holds_rename M ρ v
  | sigma k f ih => simp only [rename,Holds,ih,append_comp_extend]
  | pi k f ih => simp only [rename,Holds,ih,append_comp_extend]

noncomputable def enumerate (I : Type) [Nonempty I] [Countable I] : ℕ → I :=
  (exists_surjective_nat I).choose

theorem enumerate_surj (I : Type) [Nonempty I] [Countable I] : Function.Surjective (enumerate I) :=
  (exists_surjective_nat I).choose_spec

noncomputable def indexedPi {I : Type} [Nonempty I] [Countable I] {n : ℕ}
    (k : I → ℕ) (f : ∀ i, Formula (k i + n)) : Formula n :=
  .pi (fun j => k (enumerate I j)) (fun j => f (enumerate I j))

theorem indexedPi_level {I : Type} [Nonempty I] [Countable I] {n : ℕ} {k : I → ℕ}
    {f : ∀ i, Formula (k i + n)} {α : Ordinal.{0}} (β : I → Ordinal.{0})
    (lt : ∀ i, β i < α) (h : ∀ i, AtLevel .sigma (β i) (f i)) : AtLevel .pi α (indexedPi k f) :=
  .pi _ (fun j => lt (enumerate I j)) (fun j => h (enumerate I j))

theorem holds_indexedPi {A I : Type} [Nonempty I] [Countable I] (M : BoolOps A) {n : ℕ}
    (k : I → ℕ) (f : ∀ i, Formula (k i+n)) (v : Fin n → A) :
    (indexedPi k f).Holds M v ↔ ∀ i u, (f i).Holds M (Fin.append u v) := by
  constructor
  · intro h i
    obtain ⟨j,rfl⟩ := enumerate_surj I i
    exact h j
  · intro h j
    exact h _

noncomputable def indexedSigma {I : Type} [Nonempty I] [Countable I] {n : ℕ}
    (k : I → ℕ) (f : ∀ i, Formula (k i+n)) : Formula n :=
  .sigma (fun j => k (enumerate I j)) (fun j => f (enumerate I j))

theorem indexedSigma_level {I : Type} [Nonempty I] [Countable I] {n : ℕ} {k : I → ℕ}
    {f : ∀ i, Formula (k i+n)} {α : Ordinal.{0}} (β : I → Ordinal.{0})
    (lt : ∀ i, β i < α) (h : ∀ i, AtLevel .pi (β i) (f i)) : AtLevel .sigma α (indexedSigma k f) :=
  .sigma _ (fun j => lt (enumerate I j)) (fun j => h (enumerate I j))

theorem holds_indexedSigma {A I : Type} [Nonempty I] [Countable I] (M : BoolOps A) {n : ℕ}
    (k : I → ℕ) (f : ∀ i, Formula (k i+n)) (v : Fin n → A) :
    (indexedSigma k f).Holds M v ↔ ∃ i u, (f i).Holds M (Fin.append u v) := by
  constructor
  · rintro ⟨j,u,h⟩
    exact ⟨_,u,h⟩
  · rintro ⟨i,u,h⟩
    obtain ⟨j,rfl⟩ := enumerate_surj I i
    exact ⟨j,u,h⟩

end BooleanScott
