module
public import BooleanScott.NormalForms
public import BooleanScott.TupleSystem

/-! Write one actual Π_(ω+2) sentence from a countable reference algebra and
a Π_ω formula for each tuple orbit. The displayed clauses force the candidate
model to admit a full countable back-and-forth system. -/
@[expose] public section
namespace BooleanScott
open Ordinal
open scoped Ordinal

variable {A : Type} [BooleanAlgebra A] [Countable A]

abbrev TupleTests (A : Type) := ∀ {n : ℕ}, (Fin n → A) → Formula n

inductive ScottClause (A : Type)
  | initial
  | order (n : ℕ) (v : Fin n → A) (i j : Fin n)
  | forth (n : ℕ) (v : Fin n → A) (a : A)
  | back (n : ℕ) (v : Fin n → A)
  deriving Countable, Inhabited

def ScottClause.arity {A : Type} : ScottClause A → ℕ
  | .initial => 0
  | .order n .. | .forth n .. => n
  | .back n _ => 1+n

def ScottClause.truth (D : TupleTests A) {B : Type} (M : BoolOps B) :
    (q : ScottClause A) → (Fin q.arity → B) → Prop
  | .initial, w => (D (n := 0) Fin.elim0).Holds M w
  | .order _ v i j, w => (D v).Holds M w →
      (v i ≤ v j ↔ M.meet (w i) (w j) = w i)
  | .forth _ v a, w => (D v).Holds M w → ∃ b, (D (prepend a v)).Holds M (prepend b w)
  | .back _ v, w => (D v).Holds M (w ∘ Fin.natAdd 1) → ∃ a, (D (prepend a v)).Holds M w

noncomputable def disjoinPi {I : Type} [Nonempty I] [Countable I] {n : ℕ} (f : I → Formula n) : Formula n :=
  indexedSigma (fun _ : I => 0) (fun i => (f i).pad)

theorem disjoinPi_level {I : Type} [Nonempty I] [Countable I] {n : ℕ} {f : I → Formula n}
    {α : Ordinal.{0}} (hf : ∀ i, AtLevel .pi α (f i)) : AtLevel .sigma (α+1) (disjoinPi f) :=
  indexedSigma_level (fun _ => α) (fun _ => lt_add_one _) (fun i => (hf i).rename _)

theorem holds_disjoinPi {I B : Type} [Nonempty I] [Countable I] {n : ℕ} (f : I → Formula n)
    (M : BoolOps B) (w : Fin n → B) : (disjoinPi f).Holds M w ↔ ∃ i, (f i).Holds M w := by
  rw [disjoinPi,holds_indexedSigma]
  constructor
  · rintro ⟨i,u,h⟩
    exact ⟨i,((f i).holds_pad M u w).mp h⟩
  · rintro ⟨i,h⟩
    exact ⟨i,Fin.elim0,((f i).holds_pad M _ w).mpr h⟩

private theorem implication {α : Ordinal.{0}} {n : ℕ} {φ ψ : Formula n} (hφ : AtLevel .pi α φ)
    (hψ : AtLevel .sigma (α+1) ψ) : ∃ θ : Formula n, AtLevel .sigma (α+1) θ ∧
    ∀ (B : Type) (M : BoolOps B) (w : Fin n → B), θ.Holds M w ↔ (φ.Holds M w → ψ.Holds M w) := by
  have hn : AtLevel .sigma (α+1) φ.negate := (hφ.negate).liftLevel (lt_add_one _).le
  obtain ⟨θ,hθ,h⟩ := sigma_or hn hψ (by positivity)
  exact ⟨θ,hθ,fun B M w => (h B M w).trans (by rw [Formula.holds_negate]; tauto)⟩

theorem scottClauseBody {α : Ordinal.{0}} (D : TupleTests A) (level : ∀ {n} (v : Fin n → A), AtLevel .pi α (D v))
    (q : ScottClause A) : ∃ φ : Formula q.arity, AtLevel .sigma (α+1) φ ∧
    ∀ (B : Type) (M : BoolOps B) (w : Fin q.arity → B), φ.Holds M w ↔ q.truth D M w := by
  classical
  cases q with
  | initial =>
    let f (_ : Unit) := D (n := 0) Fin.elim0
    refine ⟨disjoinPi f,disjoinPi_level (fun _ => level _),fun B M w => ?_⟩
    exact (holds_disjoinPi f M w).trans ⟨fun ⟨_,h⟩ => h,fun h => ⟨(),h⟩⟩
  | order n v i j =>
    let eqn : QF n := .eq (.meet (.var i) (.var j)) (.var i)
    let test := if v i ≤ v j then eqn else QF.neg eqn
    obtain ⟨θ,hθ,h⟩ := implication (level v) (AtLevel.qf test .sigma (α+1))
    refine ⟨θ,hθ,fun B M w => (h B M w).trans ?_⟩
    change (_ → test.Holds M w) ↔ (_ → (v i ≤ v j ↔ _))
    by_cases hv : v i ≤ v j <;> simp only [test,hv,ite_true,ite_false,true_iff,false_iff]
    all_goals rfl
  | forth n v a =>
    let f := D (prepend a v)
    let rhs : Formula n := .sigma (fun _ => 1) (fun _ => f)
    have lev : AtLevel .sigma (α+1) rhs := .sigma (fun _ => α) (fun _ => lt_add_one _) (fun _ => level _)
    obtain ⟨θ,hθ,h⟩ := implication (level v) lev
    refine ⟨θ,hθ,fun B M w => (h B M w).trans (imp_congr_right fun _ => ?_)⟩
    constructor
    · rintro ⟨_,u,hu⟩
      have same : (fun _ : Fin 1 => u 0) = u := by funext j; rw [Subsingleton.elim j 0]
      exact ⟨u 0,by simpa only [prepend,same] using hu⟩
    · rintro ⟨b,hb⟩
      exact ⟨0,fun _ => b,hb⟩
  | back n v =>
    let f (a : A) := D (prepend a v)
    obtain ⟨θ,hθ,h⟩ := implication ((level v).rename (Fin.natAdd 1)) (disjoinPi_level (fun a => level (prepend a v)))
    refine ⟨θ,hθ,fun B M w => (h B M w).trans ?_⟩
    exact imp_congr ((D v).holds_rename M (Fin.natAdd 1) w) (holds_disjoinPi f M w)

theorem scottSentenceOfTests {α : Ordinal.{0}} (D : TupleTests A) (level : ∀ {n} (v : Fin n → A), AtLevel .pi α (D v)) :
    ∃ σ : Formula 0, AtLevel .pi (α+2) σ ∧
    ∀ (B : Type) (M : BoolOps B), Models M σ ↔ ∀ q w, ScottClause.truth D M q w := by
  classical
  choose f hf truth using scottClauseBody D level
  let k (q : ScottClause A) := q.arity
  refine ⟨indexedPi (n := 0) k f,indexedPi_level (fun _ => α+1)
    (fun _ => by simpa only [add_assoc,one_add_one_eq_two] using lt_add_one (α+1)) hf,fun B M => ?_⟩
  unfold Models
  rw [holds_indexedPi]
  have same {n : ℕ} (w : Fin n → B) : Fin.append w (Fin.elim0 : Fin 0 → B) = w := by
    funext i
    exact Fin.append_left w Fin.elim0 i
  simp only [same,truth]
  rfl

end BooleanScott
