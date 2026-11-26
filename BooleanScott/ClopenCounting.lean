module
public import BooleanScott.NormalForms
public import BooleanScott.TagTopology

/-! All finite thresholds for one mark have a uniform level independent of
the threshold. Taking their conjunction defines incidence with its derived
set on all compact zero-dimensional Hausdorff spaces. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal
open scoped Ordinal

theorem pi_conjunction {I : Type} [Countable I] {n : ℕ} {α : Ordinal.{0}} (f : I → Formula n)
    (lev : ∀ i, AtLevel .pi α (f i)) (pos : 0 < α) :
    ∃ ψ : Formula n, AtLevel .pi α ψ ∧ ∀ (B : Type) (M : BoolOps B) (w : Fin n → B),
      ψ.Holds M w ↔ ∀ i, (f i).Holds M w := by
  classical
  by_cases hi : Nonempty I
  · let := hi
    obtain ⟨θ,hθ,truth⟩ := sigma_disjunction (fun i => (f i).negate) (fun i => (lev i).negate) pos
    refine ⟨θ.negate,hθ.negate,fun B M w => ?_⟩
    simp only [Formula.holds_negate,truth,not_exists,not_not]
  · refine ⟨.qf (.eq .zero .zero),.qf _ _ _,fun B M w => ?_⟩
    exact ⟨fun _ i => (hi ⟨i⟩).elim,fun _ => rfl⟩

private inductive CountClause (h : ℕ)
  | inside (i : Fin h)
  | hit (i : Fin h)
  | apart (i j : Fin h)
  deriving Countable

/-- The h quantified subclopens are simultaneously chosen in one block.
Their intersections, relative order and evaluations are all pure Boolean
tests. The empty block for h = 0 is included. -/
theorem threshold_formula {φ : Formula 1} {α : Ordinal.{0}} (lev : AtLevel .pi α φ)
    (pos : 0 < α) (h : ℕ) : ∃ ψ : Formula 1, AtLevel .sigma (α+1) ψ ∧
    ∀ (B : Type) [BooleanAlgebra B] (c : B), ψ.Holds (BoolOps.ofAlgebra B) (fun _ => c) ↔
    ∃ u : Fin h → B, (∀ i, u i ≤ c ∧ φ.Holds (BoolOps.ofAlgebra B) (fun _ => u i)) ∧
      Pairwise (fun i j => Disjoint (u i) (u j)) := by
  classical
  let slot (i : Fin h) := Fin.castAdd 1 i
  let parent := Fin.natAdd h (0 : Fin 1)
  let sub (i : Fin h) : QF (h+1) := .eq (.meet (.var (slot i)) (.var parent)) (.var (slot i))
  let apart (i j : Fin h) : QF (h+1) := if i = j then .eq .zero .zero
    else .eq (.meet (.var (slot i)) (.var (slot j))) .zero
  let body : CountClause h → Formula (h+1)
    | .inside i => .qf (sub i)
    | .hit i => φ.rename (fun _ => slot i)
    | .apart i j => .qf (apart i j)
  have hb (q : CountClause h) : AtLevel .pi α (body q) := by
    cases q with
    | inside | apart => apply AtLevel.qf
    | hit i => exact lev.rename _
  obtain ⟨χ,hχ,meaning⟩ := pi_conjunction body hb pos
  let ψ : Formula 1 := .sigma (fun _ => h) (fun _ => χ)
  refine ⟨ψ,.sigma (fun _ => α) (fun _ => lt_add_one _) (fun _ => hχ),fun B _ c => ?_⟩
  let M := BoolOps.ofAlgebra B
  let w (u : Fin h → B) := Fin.append u (fun _ : Fin 1 => c)
  have hs (u : Fin h → B) (i : Fin h) : (sub i).Holds M (w u) ↔ u i ≤ c := by
    change w u (slot i) ⊓ w u parent = w u (slot i) ↔ _
    simp only [w,slot,parent,Fin.append_left,Fin.append_right,inf_eq_left]
  have hh (u : Fin h → B) (i : Fin h) : (body (.hit i)).Holds M (w u) ↔ φ.Holds M (fun _ => u i) := by
    apply (φ.holds_rename M _ _).trans
    have eq : w u ∘ (fun _ : Fin 1 => slot i) = (fun _ => u i) := funext (fun _ => Fin.append_left ..)
    rw [eq]
  have hd (u : Fin h → B) (i j : Fin h) (neq : i ≠ j) :
      (apart i j).Holds M (w u) ↔ Disjoint (u i) (u j) := by
    simp only [apart,ite_eq_right neq]
    change w u (slot i) ⊓ w u (slot j) = ⊥ ↔ _
    simp only [w,slot,Fin.append_left,disjoint_iff]
  constructor
  · rintro ⟨_,u,hu⟩
    have all := (meaning B M (w u)).mp hu
    exact ⟨u,fun i => ⟨(hs u i).mp (all (.inside i)),(hh u i).mp (all (.hit i))⟩,
      fun i j neq => (hd u i j neq).mp (all (.apart i j))⟩
  · rintro ⟨u,hu,hdj⟩
    refine ⟨0,u,(meaning B M (w u)).mpr ?_⟩
    intro q
    cases q with
    | inside i => exact (hs u i).mpr (hu i).1
    | hit i => exact (hh u i).mpr (hu i).2
    | apart i j =>
      by_cases eq : i = j
      · change (apart i j).Holds M (w u)
        simp only [apart,ite_eq_left eq]
        rfl
      · exact (hd u i j eq).mpr (hdj eq)

end BooleanScott
