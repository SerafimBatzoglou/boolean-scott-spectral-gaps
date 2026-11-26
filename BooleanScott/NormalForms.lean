module
public import BooleanScott.FormulaTools

/-! Closure of non-effective normal forms at the same positive level under
countable disjunction on the existential side. Flattening is essential to
avoid charging an extra successor to each implication in a Scott sentence. -/
@[expose] public section
namespace BooleanScott
open Ordinal

def Formula.pad {n : ℕ} (φ : Formula n) : Formula (0+n) := φ.rename (Fin.natAdd 0)

theorem Formula.holds_pad {A : Type} (M : BoolOps A) {n : ℕ} (φ : Formula n)
    (u : Fin 0 → A) (v : Fin n → A) :
    φ.pad.Holds M (Fin.append u v) ↔ φ.Holds M v := by
  rw [pad,holds_rename]
  have same : Fin.append u v ∘ Fin.natAdd 0 = v := funext (fun j => Fin.append_right u v j)
  rw [same]

structure SigmaPiece (n : ℕ) (α : Ordinal.{0}) where
  arity : ℕ
  leaf : Formula (arity+n)
  rank : Ordinal.{0}
  lower : rank < α
  level : AtLevel .pi rank leaf

def SigmaPiece.holds {n : ℕ} {α : Ordinal.{0}} (s : SigmaPiece n α)
    {A : Type} (M : BoolOps A) (v : Fin n → A) :=
  ∃ u, s.leaf.Holds M (Fin.append u v)

theorem sigma_pieces {n : ℕ} {α : Ordinal.{0}} {φ : Formula n}
    (h : AtLevel .sigma α φ) (pos : 0 < α) :
    ∃ d : ℕ → SigmaPiece n α, ∀ (A : Type) (M : BoolOps A) (v : Fin n → A),
      φ.Holds M v ↔ ∃ j, (d j).holds M v := by
  cases h with
  | qf q =>
    let φ : Formula n := .qf q
    let p : SigmaPiece n α := ⟨0,φ.pad,0,pos,(AtLevel.qf q .pi 0).rename _⟩
    refine ⟨fun _ => p,fun A M v => ?_⟩
    constructor
    · intro h
      exact ⟨0,Fin.elim0,(φ.holds_pad M Fin.elim0 v).mpr h⟩
    · rintro ⟨_,u,h⟩
      exact (φ.holds_pad M u v).mp h
  | sigma β lt lev =>
    exact ⟨fun j => ⟨_,_,β j,lt j,lev j⟩,fun _ _ _ => Iff.rfl⟩

theorem sigma_disjunction {I : Type} [Nonempty I] [Countable I] {n : ℕ} {α : Ordinal.{0}}
    (φ : I → Formula n) (h : ∀ i, AtLevel .sigma α (φ i)) (pos : 0 < α) :
    ∃ ψ : Formula n, AtLevel .sigma α ψ ∧ ∀ (A : Type) (M : BoolOps A) (v : Fin n → A),
      ψ.Holds M v ↔ ∃ i, (φ i).Holds M v := by
  classical
  choose d hd using fun i => sigma_pieces (h i) pos
  let get (p : I × ℕ) := d p.1 p.2
  let k (p : I × ℕ) := (get p).arity
  let f (p : I × ℕ) := (get p).leaf
  refine ⟨indexedSigma k f,indexedSigma_level (fun p => (get p).rank)
    (fun p => (get p).lower) (fun p => (get p).level),fun A M v => ?_⟩
  rw [holds_indexedSigma]
  constructor
  · rintro ⟨⟨i,j⟩,u,hu⟩
    exact ⟨i,(hd i A M v).mpr ⟨j,u,hu⟩⟩
  · rintro ⟨i,hi⟩
    obtain ⟨j,u,hu⟩ := (hd i A M v).mp hi
    exact ⟨(i,j),u,hu⟩

theorem sigma_or {n : ℕ} {α : Ordinal.{0}} {φ ψ : Formula n}
    (hφ : AtLevel .sigma α φ) (hψ : AtLevel .sigma α ψ) (pos : 0 < α) :
    ∃ θ : Formula n, AtLevel .sigma α θ ∧ ∀ (A : Type) (M : BoolOps A) (v : Fin n → A),
      θ.Holds M v ↔ φ.Holds M v ∨ ψ.Holds M v := by
  let branch (b : Bool) := if b then φ else ψ
  have lev (b : Bool) : AtLevel .sigma α (branch b) := by cases b <;> first | exact hφ | exact hψ
  obtain ⟨θ,hθ,truth⟩ := sigma_disjunction branch lev pos
  refine ⟨θ,hθ,fun A M v => (truth A M v).trans ?_⟩
  constructor
  · rintro ⟨b,hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩

end BooleanScott
