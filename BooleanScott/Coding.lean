module
public import BooleanScott.Presentation
public import BooleanScott.Diagonal
public import Mathlib.Basic.Denumerable
public import Mathlib.Order.Hom.BoundedLattice

/-! Universal countable operation tables and invariance under re-enumeration. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory

structure OpsIso {A B : Type} (M : BoolOps A) (N : BoolOps B) extends A ≃ B where
  zero_eq : toEquiv M.zero = N.zero
  one_eq : toEquiv M.one = N.one
  compl_eq : ∀ a, toEquiv (M.compl a) = N.compl (toEquiv a)
  meet_eq : ∀ a b, toEquiv (M.meet a b) = N.meet (toEquiv a) (toEquiv b)
  join_eq : ∀ a b, toEquiv (M.join a b) = N.join (toEquiv a) (toEquiv b)

namespace OpsIso
variable {A B : Type} {M : BoolOps A} {N : BoolOps B}

theorem term (e : OpsIso M N) {n : ℕ} (v : Fin n → A) (t : Term n) :
    e.toEquiv (t.eval M v) = t.eval N (e.toEquiv ∘ v) := by
  induction t with
  | var => rfl
  | zero => exact e.zero_eq
  | one => exact e.one_eq
  | compl t ih => exact (e.compl_eq _).trans (congrArg _ ih)
  | meet s t ih jh => exact (e.meet_eq _ _).trans (congrArg₂ _ ih jh)
  | join s t ih jh => exact (e.join_eq _ _).trans (congrArg₂ _ ih jh)

theorem comp_append {α β : Type} {k n : ℕ} (f : α → β) (u : Fin k → α) (v : Fin n → α) :
    f ∘ Fin.append u v = Fin.append (f ∘ u) (f ∘ v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- All stages, including those beyond the individual rank, hold for an actual isomorphism. -/
theorem bf (e : OpsIso M N) (α : Ordinal.{0}) {n : ℕ} (v : Fin n → A) :
    BF M N α v (e.toEquiv ∘ v) := by
  induction α using WellFoundedLT.induction generalizing n with
  | ind α ih =>
    rw [BF]
    constructor
    · intro s t
      rw [← e.term v s, ← e.term v t, e.toEquiv.injective.eq_iff]
    · intro β k
      constructor
      · intro u
        exact ⟨e.toEquiv ∘ u, by simpa only [comp_append] using ih β.val β.property (Fin.append u v)⟩
      · intro z
        refine ⟨e.toEquiv.symm ∘ z, ?_⟩
        have cancel : e.toEquiv ∘ (e.toEquiv.symm ∘ z) = z := by funext j; simp
        simpa only [comp_append, cancel] using
          ih β.val β.property (Fin.append (e.toEquiv.symm ∘ z) v)

theorem models {α : Ordinal.{0}} {σ : Formula 0} {pol : Polarity} (h : AtLevel pol α σ)
    (e : OpsIso M N) : Models M σ ↔ Models N σ := by
  have hv : (e.toEquiv ∘ (Fin.elim0 : Fin 0 → A)) = Fin.elim0 := Subsingleton.elim _ _
  simpa only [Models, hv] using h.transfer (e.bf α Fin.elim0)

def ofOrder [BooleanAlgebra A] [BooleanAlgebra B] (e : A ≃o B) :
    OpsIso (BoolOps.ofAlgebra A) (BoolOps.ofAlgebra B) where
  toEquiv := e.toEquiv
  zero_eq := e.map_bot
  one_eq := e.map_top
  compl_eq := fun a => map_compl' e a
  meet_eq := e.map_inf
  join_eq := e.map_sup

end OpsIso

def BoolOps.prod {A B : Type} (M : BoolOps A) (N : BoolOps B) : BoolOps (A × B) :=
  ⟨(M.zero,N.zero),(M.one,N.one),fun (x,y) => (M.compl x,N.compl y),
   fun (x,y) (z,w) => (M.meet x z,N.meet y w), fun (x,y) (z,w) => (M.join x z,N.join y w)⟩

def OpsIso.prodRight {A B D : Type} {M : BoolOps A} {N : BoolOps B}
    (e : OpsIso M N) (R : BoolOps D) : OpsIso (M.prod R) (N.prod R) where
  toEquiv := e.toEquiv.prodCongr (Equiv.refl D)
  zero_eq := Prod.ext e.zero_eq rfl
  one_eq := Prod.ext e.one_eq rfl
  compl_eq := fun a => Prod.ext (e.compl_eq a.1) rfl
  meet_eq := fun a b => Prod.ext (e.meet_eq a.1 b.1) rfl
  join_eq := fun a b => Prod.ext (e.join_eq a.1 b.1) rfl

inductive TableSlot
  | bot | top | compl (a : ℕ) | meet (a b : ℕ) | join (a b : ℕ)
  deriving Countable, DecidableEq

/-- The whole product of tables is standard Borel. The guard is responsible
for excluding assignments that violate the Boolean algebra identities. -/
abbrev Tables := TableSlot → ℕ

def readTables (t : Tables) : BoolOps ℕ :=
  ⟨t .bot,t .top,fun a => t (.compl a), fun a b => t (.meet a b), fun a b => t (.join a b)⟩

def writeTables {A : Type} (M : BoolOps A) (e : A ≃ ℕ) : Tables
  | .bot => e M.zero
  | .top => e M.one
  | .compl i => e (M.compl (e.symm i))
  | .meet i j => e (M.meet (e.symm i) (e.symm j))
  | .join i j => e (M.join (e.symm i) (e.symm j))

def enumerationIso {A : Type} (M : BoolOps A) (e : A ≃ ℕ) :
    OpsIso M (readTables (writeTables M e)) where
  toEquiv := e
  zero_eq := rfl
  one_eq := rfl
  compl_eq := by intro a; simp [readTables, writeTables]
  meet_eq := by intro a b; simp [readTables, writeTables]
  join_eq := by intro a b; simp [readTables, writeTables]

theorem measurable_tables : BorelOps readTables :=
  BorelOps.of_tables (measurable_pi_apply _) (measurable_pi_apply _)
    (fun _ => measurable_pi_apply _) (fun _ _ => measurable_pi_apply _) (fun _ _ => measurable_pi_apply _)

theorem BorelOps.prodRight {P A B : Type} [MeasurableSpace P] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable A] [MeasurableSpace B] [MeasurableSingletonClass B]
    [Countable B] {M : P → BoolOps A} (h : BorelOps M) (R : BoolOps B) :
    BorelOps fun p => (M p).prod R := by
  apply BorelOps.of_tables
  · exact h.zero.prodMk measurable_const
  · exact h.one.prodMk measurable_const
  · exact fun a => (h.compl.comp (measurable_id.prodMk (measurable_const (a := a.1)))).prodMk measurable_const
  · exact fun a b => (h.meet.comp (measurable_id.prodMk (measurable_const (a := (a.1,b.1))))).prodMk measurable_const
  · exact fun a b => (h.join.comp (measurable_id.prodMk (measurable_const (a := (a.1,b.1))))).prodMk measurable_const

end BooleanScott
