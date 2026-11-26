module
public import BooleanScott.Infinitary
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.BooleanAlgebra.Basic

/-! Relativization to a named Boolean element at exactly the same level.
A quantified ambient element is intersected with the named element.
Every member of the principal ideal is obtained this way, in both
quantifier directions and also when the named element is zero. -/
@[expose] public section
namespace BooleanScott
open Set

def intervalOps {A : Type} [BooleanAlgebra A] (c : A) : BoolOps (Iic c) where
  zero := ⟨⊥,bot_le⟩
  one := ⟨c,le_rfl⟩
  compl x := ⟨x.valᶜ ⊓ c,inf_le_right⟩
  meet x y := ⟨x.val ⊓ y.val,inf_le_left.trans x.property⟩
  join x y := ⟨x.val ⊔ y.val,sup_le x.property y.property⟩

/-- The operations used by the interpretation are those of an actual
Boolean algebra on the interval, with top c and relative complement. -/
@[instance_reducible] def intervalAlgebra {A : Type} [BooleanAlgebra A] (c : A) : BooleanAlgebra (Iic c) where
  compl x := ⟨x.valᶜ ⊓ c,inf_le_right⟩
  le_top := fun _ => le_top
  bot_le := fun _ => bot_le
  inf_compl_le_bot x := by
    change x.val ⊓ (x.valᶜ ⊓ c) ≤ ⊥
    simp [← inf_assoc]
  top_le_sup_compl x := by
    change c ≤ x.val ⊔ (x.valᶜ ⊓ c)
    simp [sup_inf_left, sup_eq_right.mpr x.property]

theorem intervalOps_eq {A : Type} [BooleanAlgebra A] (c : A) :
    intervalOps c = @BoolOps.ofAlgebra (Iic c) (intervalAlgebra c) := rfl

def restrictTo {A : Type} [BooleanAlgebra A] (c a : A) : Iic c := ⟨a ⊓ c,inf_le_right⟩

theorem restrictTo_coe {A : Type} [BooleanAlgebra A] {c : A} (x : Iic c) :
    restrictTo c x.val = x := Subtype.ext (inf_eq_left.mpr x.property)

def Term.relative {n m : ℕ} (c : Fin m) (ρ : Fin n → Fin m) : Term n → Term m
  | .var i => .meet (.var (ρ i)) (.var c)
  | .zero => .zero
  | .one => .var c
  | .compl t => .meet (.compl (t.relative c ρ)) (.var c)
  | .meet s t => .meet (s.relative c ρ) (t.relative c ρ)
  | .join s t => .join (s.relative c ρ) (t.relative c ρ)

theorem Term.eval_relative {A : Type} [BooleanAlgebra A] {n m : ℕ} (c : Fin m)
    (ρ : Fin n → Fin m) (t : Term n) (v : Fin m → A) :
    (t.relative c ρ).eval (BoolOps.ofAlgebra A) v =
    (t.eval (intervalOps (v c)) (fun i => restrictTo (v c) (v (ρ i)))).val := by
  induction t with
  | var | zero | one => rfl
  | compl _ ih => exact congrArg (fun a : A => aᶜ ⊓ v c) ih
  | meet _ _ ih jh => exact congrArg₂ (· ⊓ ·) ih jh
  | join _ _ ih jh => exact congrArg₂ (· ⊔ ·) ih jh

def QF.relative {n m : ℕ} (c : Fin m) (ρ : Fin n → Fin m) : QF n → QF m
  | .eq s t => .eq (s.relative c ρ) (t.relative c ρ)
  | .neg p => .neg (p.relative c ρ)
  | .and p q => .and (p.relative c ρ) (q.relative c ρ)

theorem QF.holds_relative {A : Type} [BooleanAlgebra A] {n m : ℕ} (c : Fin m)
    (ρ : Fin n → Fin m) (q : QF n) (v : Fin m → A) :
    (q.relative c ρ).Holds (BoolOps.ofAlgebra A) v ↔
    q.Holds (intervalOps (v c)) (fun i => restrictTo (v c) (v (ρ i))) := by
  induction q with
  | eq s t => exact (by simp only [relative,Holds,Term.eval_relative,Subtype.val_inj])
  | neg _ ih => exact not_congr ih
  | and _ _ ih jh => exact and_congr ih jh

def extendVars {n m : ℕ} (k : ℕ) (ρ : Fin n → Fin m) : Fin (k+n) → Fin (k+m) :=
  Fin.addCases (Fin.castAdd m) (fun i => Fin.natAdd k (ρ i))

def Formula.relative {n : ℕ} (φ : Formula n) {m : ℕ} (c : Fin m) (ρ : Fin n → Fin m) : Formula m :=
  match φ with
  | .qf q => .qf (q.relative c ρ)
  | .sigma k f => .sigma k (fun i => (f i).relative (Fin.natAdd (k i) c) (extendVars (k i) ρ))
  | .pi k f => .pi k (fun i => (f i).relative (Fin.natAdd (k i) c) (extendVars (k i) ρ))

theorem AtLevel.relative {n : ℕ} {φ : Formula n} {p : Polarity} {α : Ordinal.{0}}
    (h : AtLevel p α φ) {m : ℕ} (c : Fin m) (ρ : Fin n → Fin m) :
    AtLevel p α (φ.relative c ρ) := by
  induction h generalizing m with
  | qf => apply AtLevel.qf
  | sigma β lt _ ih => exact .sigma β lt (fun i => ih i _ _)
  | pi β lt _ ih => exact .pi β lt (fun i => ih i _ _)

private theorem append_relative {A : Type} [BooleanAlgebra A] {k n m : ℕ} (c : Fin m)
    (ρ : Fin n → Fin m) (u : Fin k → A) (v : Fin m → A) :
    (fun j => restrictTo (v c) (Fin.append u v (extendVars k ρ j))) =
    Fin.append (fun i => restrictTo (v c) (u i)) (fun i => restrictTo (v c) (v (ρ i))) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [extendVars]

private theorem shifted_holds {A : Type} [BooleanAlgebra A] {k n m : ℕ} (f : Formula (k+n))
    (c : Fin m) (ρ : Fin n → Fin m) (u : Fin k → A) (v : Fin m → A) :
    f.Holds (intervalOps (Fin.append u v (Fin.natAdd k c))) (fun i =>
      restrictTo (Fin.append u v (Fin.natAdd k c)) (Fin.append u v (extendVars k ρ i))) ↔
    f.Holds (intervalOps (v c)) (Fin.append (fun i => restrictTo (v c) (u i))
      (fun i => restrictTo (v c) (v (ρ i)))) := by
  let P (z : A) := f.Holds (intervalOps z) (fun i => restrictTo z (Fin.append u v (extendVars k ρ i)))
  change P _ ↔ _
  rw [Fin.append_right]
  unfold P
  rw [append_relative]

theorem Formula.holds_relative {A : Type} [BooleanAlgebra A] {n m : ℕ} (φ : Formula n)
    (c : Fin m) (ρ : Fin n → Fin m) (v : Fin m → A) :
    (φ.relative c ρ).Holds (BoolOps.ofAlgebra A) v ↔
    φ.Holds (intervalOps (v c)) (fun i => restrictTo (v c) (v (ρ i))) := by
  induction φ generalizing m with
  | qf q => exact q.holds_relative _ _ _
  | sigma k f ih =>
    change (∃ i u, ((f i).relative _ _).Holds _ (Fin.append u v)) ↔ _
    simp only [ih, shifted_holds]
    constructor
    · rintro ⟨i,u,h⟩
      exact ⟨i,_,h⟩
    · rintro ⟨i,z,h⟩
      exact ⟨i,fun j => (z j).val,by simpa only [restrictTo_coe] using h⟩
  | pi k f ih =>
    change (∀ i u, ((f i).relative _ _).Holds _ (Fin.append u v)) ↔ _
    simp only [ih, shifted_holds]
    constructor
    · intro h i z
      simpa only [restrictTo_coe] using h i (fun j => (z j).val)
    · intro h i u
      exact h i _

end BooleanScott
