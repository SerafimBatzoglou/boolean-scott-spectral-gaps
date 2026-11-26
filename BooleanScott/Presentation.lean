module
public import BooleanScott.Infinitary
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Joint measurability for countable presentations and all countable stages
of finite-block back-and-forth. Both presentations may depend on the parameter. -/
@[expose] public section
namespace BooleanScott
open Ordinal MeasureTheory Set
open scoped Ordinal

structure BorelOps {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    (M : P → BoolOps A) : Prop where
  zero : Measurable fun p => (M p).zero
  one : Measurable fun p => (M p).one
  compl : Measurable fun z : P × A => (M z.1).compl z.2
  meet : Measurable fun z : P × (A × A) => (M z.1).meet z.2.1 z.2.2
  join : Measurable fun z : P × (A × A) => (M z.1).join z.2.1 z.2.2

theorem BorelOps.of_tables {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] {M : P → BoolOps A}
    (hz : Measurable fun p => (M p).zero) (ho : Measurable fun p => (M p).one)
    (hc : ∀ a, Measurable fun p => (M p).compl a)
    (hm : ∀ a b, Measurable fun p => (M p).meet a b)
    (hj : ∀ a b, Measurable fun p => (M p).join a b) : BorelOps M :=
  ⟨hz,ho,measurable_from_prod_countable_left hc,
    measurable_from_prod_countable_left fun ab => hm ab.1 ab.2,
    measurable_from_prod_countable_left fun ab => hj ab.1 ab.2⟩

theorem BorelOps.term {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    {M : P → BoolOps A} (h : BorelOps M) {n : ℕ} (v : Fin n → A) (t : Term n) :
    Measurable (fun p => t.eval (M p) v) := by
  induction t with
  | var => exact measurable_const
  | zero => exact h.zero
  | one => exact h.one
  | compl _ ih => exact h.compl.comp (measurable_id.prodMk ih)
  | meet _ _ ih jh => exact h.meet.comp (measurable_id.prodMk (ih.prodMk jh))
  | join _ _ ih jh => exact h.join.comp (measurable_id.prodMk (ih.prodMk jh))

theorem BorelOps.qf {P A : Type} [MeasurableSpace P] [MeasurableSpace A] [MeasurableEq A]
    {M : P → BoolOps A} (h : BorelOps M) {n : ℕ} (v : Fin n → A) (q : QF n) :
    Measurable fun p => q.Holds (M p) v := by
  induction q with
  | eq s t => exact (h.term v s).eq (h.term v t)
  | neg _ ih => exact ih.not
  | and _ _ ih jh => exact ih.and jh

theorem BorelOps.formula {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    [MeasurableEq A] [Countable A] {M : P → BoolOps A} (h : BorelOps M) {n : ℕ}
    (φ : Formula n) (v : Fin n → A) : Measurable fun p => φ.Holds (M p) v := by
  induction φ with
  | qf q => exact h.qf v q
  | sigma k f ih => exact Measurable.exists fun i => Measurable.exists fun u => ih i (Fin.append u v)
  | pi k f ih => exact Measurable.forall fun i => Measurable.forall fun u => ih i (Fin.append u v)

theorem borel_bf {P A B : Type} [MeasurableSpace P] [MeasurableSpace A] [MeasurableEq A]
    [MeasurableSpace B] [MeasurableEq B] [Countable A] [Countable B]
    {M : P → BoolOps A} {N : P → BoolOps B} (hm : BorelOps M) (hn : BorelOps N)
    (α : Ordinal.{0}) (hα : α < ω₁) {n : ℕ} (v : Fin n → A) (w : Fin n → B) :
    Measurable fun p => BF (M p) (N p) α v w := by
  induction α using WellFoundedLT.induction generalizing n with
  | ind α ih =>
    let : Countable (Iio α) := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype
    conv => arg 1; ext p; rw [BF]
    apply Measurable.and
    · exact Measurable.forall fun s => Measurable.forall fun t =>
        ((hm.term v s).eq (hm.term v t)).iff ((hn.term w s).eq (hn.term w t))
    · apply Measurable.forall
      intro β
      apply Measurable.forall
      intro k
      apply Measurable.and
      · exact Measurable.forall fun u => Measurable.exists fun z =>
          ih β.val β.property (β.property.trans hα) (Fin.append u v) (Fin.append z w)
      · exact Measurable.forall fun z => Measurable.exists fun u =>
          ih β.val β.property (β.property.trans hα) (Fin.append u v) (Fin.append z w)

end BooleanScott
