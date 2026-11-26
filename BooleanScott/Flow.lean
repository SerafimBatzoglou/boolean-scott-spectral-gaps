module
public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.Data.Finsupp.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-! At each vertex only the nonzero child currents must have finite support.
A tree itself may have infinitely many children at a vertex. -/
@[expose] public section
namespace BooleanScott
open Descriptive

def initialSeg (a : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => initialSeg a n ++ [a n]

def HasBranch (T : tree ℕ) : Prop := ∃ a : ℕ → ℕ, ∀ n, initialSeg a n ∈ T

/-- The incoming current is one at the root. At every other vertex it is
the signed current received on its edge from its parent. -/
structure UnitFlow (T : tree ℕ) where
  incoming : List ℕ → ℤ
  children : List ℕ → ℕ →₀ ℤ
  root : incoming [] = 1
  edge : ∀ v i, (children v) i = incoming (v ++ [i])
  retained : ∀ v i, (children v) i ≠ 0 → v ++ [i] ∈ T
  balance : ∀ v, ∑ i ∈ (children v).support, (children v) i = incoming v

theorem UnitFlow.positive_child {T : tree ℕ} (F : UnitFlow T) (v : List ℕ)
    (hv : 0 < F.incoming v) : ∃ i, 0 < (F.children v) i := by
  by_contra! h
  have hsum := Finset.sum_nonpos (s := (F.children v).support) (fun i _ => h i)
  rw [F.balance] at hsum
  omega

theorem UnitFlow.hasBranch {T : tree ℕ} (F : UnitFlow T) : HasBranch T := by
  classical
  let next (v : List ℕ) := if h : ∃ i, 0 < F.children v i then h.choose else 0
  have next_pos (v : List ℕ) (hv : 0 < F.incoming v) : 0 < F.children v (next v) := by
    simp only [next, dite_eq_left (F.positive_child v hv)]
    exact (F.positive_child v hv).choose_spec
  let node : ℕ → List ℕ := Nat.rec [] (fun _ v => v ++ [next v])
  let a (n : ℕ) := next (node n)
  have coords (n : ℕ) : initialSeg a n = node n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [initialSeg, ih]; rfl
  have pos (n : ℕ) : 0 < F.incoming (node n) := by
    induction n with
    | zero => change 0 < F.incoming []; rw [F.root]; decide
    | succ n ih => exact F.edge (node n) (next (node n)) ▸ next_pos (node n) ih
  refine ⟨a, fun n => ?_⟩
  rw [coords]
  exact T.prop (F.retained (node n) (next (node n)) (ne_of_gt (next_pos _ (pos n))))

/-- Conversely a genuine infinite branch carries a unit current, zero elsewhere. -/
noncomputable def flowOfBranch {T : tree ℕ} (a : ℕ → ℕ) (ha : ∀ n, initialSeg a n ∈ T) :
    UnitFlow T := by
  classical
  let amt (v : List ℕ) : ℤ := if v = initialSeg a v.length then 1 else 0
  let out (v : List ℕ) : ℕ →₀ ℤ := Finsupp.single (a v.length) (amt v)
  refine ⟨amt, out, by simp [amt, initialSeg], ?_, ?_, ?_⟩
  · intro v i
    have split : v ++ [i] = initialSeg a v.length ++ [a v.length] ↔
        v = initialSeg a v.length ∧ a v.length = i := by
      constructor
      · intro h
        exact ⟨List.append_inj_left' h rfl, (List.cons.inj (List.append_inj_right' h rfl)).1.symm⟩
      · rintro ⟨h, e⟩; exact congrArg₂ List.append h (by rw [e])
    simp only [out, Finsupp.single_apply, amt, List.length_append, List.length_singleton, initialSeg, split]
    split_ifs <;> tauto
  · intro v i h
    have e : a v.length = i := by
      by_contra hn
      simp [out, hn] at h
    have hv : v = initialSeg a v.length := by
      by_contra hn
      simp [out, amt, hn] at h
    have hh := ha (v.length + 1)
    simpa only [initialSeg, ← hv, e] using hh
  · intro v
    change (Finsupp.single (a v.length) (amt v)).sum (fun _ x => x) = amt v
    exact Finsupp.sum_single_index rfl

theorem unitFlow_iff_branch (T : tree ℕ) : Nonempty (UnitFlow T) ↔ HasBranch T :=
  ⟨fun ⟨F⟩ => F.hasBranch, fun ⟨a, ha⟩ => ⟨flowOfBranch a ha⟩⟩

end BooleanScott
