module
public import BooleanScott.Coding

/-! Back-and-forth on surjective countable presentations. Codes may repeat
the same element. All quantified extensions range over a fixed countable
space, and only atomic truth needs to vary measurably with the parameter. -/
@[expose] public section
namespace BooleanScott
open MeasureTheory Ordinal
open scoped Ordinal

abbrev CodeDiagram (A : Type) := ∀ {n : ℕ}, (Fin n → A) → Term n → Term n → Prop

def DiagramBF {A B : Type} (D : CodeDiagram A) (E : CodeDiagram B) (α : Ordinal.{0}) {n : ℕ}
    (v : Fin n → A) (w : Fin n → B) : Prop :=
  (∀ s t, D v s t ↔ E w s t) ∧ ∀ β : Set.Iio α, ∀ k : ℕ,
    (∀ u : Fin k → A, ∃ z : Fin k → B, DiagramBF D E β.val (Fin.append u v) (Fin.append z w)) ∧
    (∀ z : Fin k → B, ∃ u : Fin k → A, DiagramBF D E β.val (Fin.append u v) (Fin.append z w))
termination_by α
decreasing_by all_goals exact β.property

def PresentsDiagram {A Y : Type} (D : CodeDiagram A) (M : BoolOps Y) (f : A → Y) :=
  ∀ {n : ℕ} (v : Fin n → A) (s t : Term n), D v s t ↔ s.eval M (f ∘ v) = t.eval M (f ∘ v)

theorem diagramBF_iff {A B X Y : Type} {D : CodeDiagram A} {E : CodeDiagram B}
    {M : BoolOps X} {N : BoolOps Y} {f : A → X} {g : B → Y}
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (pres : PresentsDiagram D M f) (qres : PresentsDiagram E N g)
    (α : Ordinal.{0}) {n : ℕ} (v : Fin n → A) (w : Fin n → B) :
    DiagramBF D E α v w ↔ BF M N α (f ∘ v) (g ∘ w) := by
  classical
  induction α using WellFoundedLT.induction generalizing n with
  | ind α ih =>
    rw [DiagramBF,BF]
    apply and_congr
    · exact forall_congr' fun s => forall_congr' fun t => iff_congr (pres v s t) (qres w s t)
    · apply forall_congr'; intro β
      apply forall_congr'; intro k
      have ext (u : Fin k → A) (z : Fin k → B) := ih β.val β.property (Fin.append u v) (Fin.append z w)
      simp only [OpsIso.comp_append] at ext
      constructor
      · rintro ⟨forth,back⟩
        constructor
        · intro x
          choose u hu using fun i => hf (x i)
          obtain ⟨z,hz⟩ := forth u
          exact ⟨g ∘ z,(show f ∘ u=x from funext hu) ▸ (ext u z).mp hz⟩
        · intro y
          choose z hz using fun i => hg (y i)
          obtain ⟨u,hu⟩ := back z
          exact ⟨f ∘ u,(show g ∘ z=y from funext hz) ▸ (ext u z).mp hu⟩
      · rintro ⟨forth,back⟩
        constructor
        · intro u
          obtain ⟨y,hy⟩ := forth (f ∘ u)
          choose z hz using fun i => hg (y i)
          exact ⟨z,(ext u z).mpr ((show g ∘ z=y from funext hz).symm ▸ hy)⟩
        · intro z
          obtain ⟨x,hx⟩ := back (g ∘ z)
          choose u hu using fun i => hf (x i)
          exact ⟨u,(ext u z).mpr ((show f ∘ u=x from funext hu).symm ▸ hx)⟩

theorem measurable_diagramBF {P A B : Type} [MeasurableSpace P] [Countable A] [Countable B]
    (D : P → CodeDiagram A) (E : P → CodeDiagram B)
    (hd : ∀ {n} (v : Fin n → A) (s t : Term n), Measurable fun p => D p v s t)
    (he : ∀ {n} (w : Fin n → B) (s t : Term n), Measurable fun p => E p w s t)
    (α : Ordinal.{0}) (hα : α < ω₁) {n : ℕ} (v : Fin n → A) (w : Fin n → B) :
    Measurable fun p => DiagramBF (D p) (E p) α v w := by
  induction α using WellFoundedLT.induction generalizing n with
  | ind α ih =>
    let : Countable (Set.Iio α) := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype
    conv => arg 1; ext p; rw [DiagramBF]
    apply Measurable.and
    · exact Measurable.forall fun s => Measurable.forall fun t => (hd v s t).iff (he w s t)
    · apply Measurable.forall; intro β
      apply Measurable.forall; intro k
      apply Measurable.and
      · exact Measurable.forall fun u => Measurable.exists fun z =>
          ih β.val β.property (β.property.trans hα) (Fin.append u v) (Fin.append z w)
      · exact Measurable.forall fun z => Measurable.exists fun u =>
          ih β.val β.property (β.property.trans hα) (Fin.append u v) (Fin.append z w)

end BooleanScott
