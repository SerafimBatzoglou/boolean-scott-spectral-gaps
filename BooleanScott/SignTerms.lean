module
public import BooleanScott.ClopenSigns
public import BooleanScott.FormulaTools
public import Mathlib.Data.List.FinRange

/-! Capture-free substitution of Boolean terms preserves truth and level.
It lets a unary test for a clopen interval inspect any Boolean sign of a
finite tuple with no charge depending on the length of the tuple. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace

def Term.substitute {n m : ℕ} (ρ : Fin n → Term m) : Term n → Term m
  | .var i => ρ i
  | .zero => .zero
  | .one => .one
  | .compl s => .compl (s.substitute ρ)
  | .meet s t => .meet (s.substitute ρ) (t.substitute ρ)
  | .join s t => .join (s.substitute ρ) (t.substitute ρ)

theorem Term.eval_substitute {n m : ℕ} {A : Type} (ρ : Fin n → Term m) (t : Term n)
    (M : BoolOps A) (v : Fin m → A) :
    (t.substitute ρ).eval M v = t.eval M (fun i => (ρ i).eval M v) := by
  induction t <;> simp_all [substitute,eval]

def QF.substitute {n m : ℕ} (ρ : Fin n → Term m) : QF n → QF m
  | .eq s t => .eq (s.substitute ρ) (t.substitute ρ)
  | .neg p => .neg (p.substitute ρ)
  | .and p q => .and (p.substitute ρ) (q.substitute ρ)

theorem QF.holds_substitute {n m : ℕ} {A : Type} (ρ : Fin n → Term m) (q : QF n)
    (M : BoolOps A) (v : Fin m → A) :
    (q.substitute ρ).Holds M v ↔ q.Holds M (fun i => (ρ i).eval M v) := by
  induction q <;> simp_all [substitute,Holds,Term.eval_substitute]

def extendTerms {n m : ℕ} (k : ℕ) (ρ : Fin n → Term m) : Fin (k+n) → Term (k+m) :=
  Fin.addCases (fun i => .var (Fin.castAdd m i)) (fun i => (ρ i).rename (Fin.natAdd k))

theorem eval_extendTerms {n m k : ℕ} {A : Type} (ρ : Fin n → Term m) (M : BoolOps A)
    (u : Fin k → A) (v : Fin m → A) :
    (fun j => (extendTerms k ρ j).eval M (Fin.append u v)) = Fin.append u (fun i => (ρ i).eval M v) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [extendTerms,Term.eval]
  · simp only [extendTerms,Fin.addCases_right,Fin.append_right,Term.eval_rename]
    exact congrArg ((ρ i).eval M) (funext (fun _ => Fin.append_right ..))

def Formula.substitute {n : ℕ} (φ : Formula n) {m : ℕ} (ρ : Fin n → Term m) : Formula m :=
  match φ with
  | .qf q => .qf (q.substitute ρ)
  | .sigma k f => .sigma k (fun i => (f i).substitute (extendTerms (k i) ρ))
  | .pi k f => .pi k (fun i => (f i).substitute (extendTerms (k i) ρ))

theorem AtLevel.substitute {n : ℕ} {φ : Formula n} {p : Polarity} {α : Ordinal.{0}}
    (h : AtLevel p α φ) {m : ℕ} (ρ : Fin n → Term m) : AtLevel p α (φ.substitute ρ) := by
  induction h generalizing m with
  | qf => exact .qf _ _ _
  | sigma β lt _ ih => exact .sigma β lt (fun i => ih i _)
  | pi β lt _ ih => exact .pi β lt (fun i => ih i _)

theorem Formula.holds_substitute {n m : ℕ} {A : Type} (φ : Formula n) (ρ : Fin n → Term m)
    (M : BoolOps A) (v : Fin m → A) :
    (φ.substitute ρ).Holds M v ↔ φ.Holds M (fun i => (ρ i).eval M v) := by
  induction φ generalizing m with
  | qf q => exact q.holds_substitute ρ M v
  | sigma k f ih => simp only [substitute,Holds,ih,eval_extendTerms]
  | pi k f ih => simp only [substitute,Holds,ih,eval_extendTerms]

def signProduct {n : ℕ} (p : Pattern n) : List (Fin n) → Term n
  | [] => .one
  | i :: l => .meet (if p i then .var i else .compl (.var i)) (signProduct p l)

def signTerm {n : ℕ} (p : Pattern n) := signProduct p (List.finRange n)

theorem signTerm_eval {X : Type} [TopologicalSpace X] {n : ℕ} (p : Pattern n) (v : Fin n → Clopens X) :
    (signTerm p).eval (BoolOps.ofAlgebra (Clopens X)) v = signCell v p := by
  classical
  ext x
  have each (l : List (Fin n)) : x ∈ (signProduct p l).eval (BoolOps.ofAlgebra (Clopens X)) v ↔
      ∀ i ∈ l, pointPattern v x i = p i := by
    induction l with
    | nil => exact iff_of_true trivial (by simp)
    | cons i l ih =>
      change (x ∈ (if p i then Term.var i else Term.compl (.var i)).eval (BoolOps.ofAlgebra (Clopens X)) v ∧ _) ↔ _
      rw [List.forall_mem_cons]
      apply and_congr _ ih
      cases p i
      · change (x ∉ v i) ↔ decide (x ∈ v i) = false
        simp
      · change (x ∈ v i) ↔ decide (x ∈ v i) = true
        simp
  apply (each (List.finRange n)).trans
  exact (by simp [funext_iff] : (∀ i ∈ List.finRange n, pointPattern v x i = p i) ↔ pointPattern v x = p) |>.trans mem_signCell.symm

end BooleanScott
