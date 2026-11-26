module
public import BooleanScott.Infinitary
public import Mathlib.Order.Ideal

/-! The countable back-and-forth existence step for Scott isolation. Positions
may repeat elements. It suffices to preserve and reflect the order between
all entries, since the final Boolean isomorphism is an order isomorphism. -/
@[expose] public section
namespace BooleanScott
open Set Order

abbrev prepend {A : Type} {n : ℕ} (a : A) (v : Fin n → A) : Fin (1+n) → A :=
  Fin.append (fun _ => a) v

def tupleGraph {A B : Type} {n : ℕ} (v : Fin n → A) (w : Fin n → B) : Set (A × B) :=
  range fun i => (v i,w i)

theorem tupleGraph_prepend {A B : Type} {n : ℕ} (v : Fin n → A) (w : Fin n → B) (a : A) (b : B) :
    (a,b) ∈ tupleGraph (prepend a v) (prepend b w) ∧
    tupleGraph v w ⊆ tupleGraph (prepend a v) (prepend b w) := by
  constructor
  · exact ⟨Fin.castAdd n (0 : Fin 1), by simp [prepend]⟩
  · rintro _ ⟨i,rfl⟩
    exact ⟨Fin.natAdd 1 i, by simp [prepend]⟩

theorem countable_back_and_forth {A B : Type} [PartialOrder A] [PartialOrder B] [Countable A] [Countable B]
    (R : ∀ {n : ℕ}, (Fin n → A) → (Fin n → B) → Prop)
    (start : R (n := 0) Fin.elim0 Fin.elim0)
    (ordered : ∀ {n} {v : Fin n → A} {w : Fin n → B}, R v w → ∀ i j, (v i ≤ v j ↔ w i ≤ w j))
    (forth : ∀ {n} {v : Fin n → A} {w : Fin n → B}, R v w → ∀ a, ∃ b, R (prepend a v) (prepend b w))
    (back : ∀ {n} {v : Fin n → A} {w : Fin n → B}, R v w → ∀ b, ∃ a, R (prepend a v) (prepend b w)) :
    Nonempty (A ≃o B) := by
  classical
  let P := {s : Set (A × B) // ∃ (n : ℕ) (v : Fin n → A) (w : Fin n → B), R v w ∧ s = tupleGraph v w}
  let pos {n : ℕ} (v : Fin n → A) (w : Fin n → B) (h : R v w) : P :=
    ⟨tupleGraph v w,n,v,w,h,rfl⟩
  let left (a : A) : Cofinal P :=
    { carrier := {p | ∃ b, (a,b) ∈ p.val}
      isCofinal := by
        rintro ⟨_,n,v,w,h,rfl⟩
        obtain ⟨b,hb⟩ := forth h a
        exact ⟨pos _ _ hb,⟨b,(tupleGraph_prepend v w a b).1⟩,(tupleGraph_prepend v w a b).2⟩ }
  let right (b : B) : Cofinal P :=
    { carrier := {p | ∃ a, (a,b) ∈ p.val}
      isCofinal := by
        rintro ⟨_,n,v,w,h,rfl⟩
        obtain ⟨a,ha⟩ := back h b
        exact ⟨pos _ _ ha,⟨a,(tupleGraph_prepend v w a b).1⟩,(tupleGraph_prepend v w a b).2⟩ }
  cases nonempty_encodable A
  cases nonempty_encodable B
  let cover := Sum.elim left right
  let origin := pos _ _ start
  let J := idealOfCofinals origin cover
  let graph (a : A) (b : B) := ∃ p ∈ J, (a,b) ∈ p.val
  have total (a : A) : ∃ b, graph a b := by
    obtain ⟨p,⟨b,hb⟩,hp⟩ := cofinal_meets_idealOfCofinals origin cover (Sum.inl a)
    exact ⟨b,p,hp,hb⟩
  have onto (b : B) : ∃ a, graph a b := by
    obtain ⟨p,⟨a,ha⟩,hp⟩ := cofinal_meets_idealOfCofinals origin cover (Sum.inr b)
    exact ⟨a,p,hp,ha⟩
  have compatible {a a' b b'} (h : graph a b) (h' : graph a' b') : a ≤ a' ↔ b ≤ b' := by
    obtain ⟨p,hp,hab⟩ := h
    obtain ⟨q,hq,hab'⟩ := h'
    obtain ⟨⟨_,n,v,w,hr,rfl⟩,_,h1,h2⟩ := J.directed p hp q hq
    obtain ⟨i,hi⟩ : (a,b) ∈ tupleGraph v w := h1 hab
    obtain ⟨j,hj⟩ : (a',b') ∈ tupleGraph v w := h2 hab'
    cases hi
    cases hj
    exact ordered hr i j
  let f (a : A) := (total a).choose
  let g (b : B) := (onto b).choose
  have hf (a : A) : graph a (f a) := (total a).choose_spec
  have hg (b : B) : graph (g b) b := (onto b).choose_spec
  exact ⟨{
    toFun := f, invFun := g
    left_inv := fun a => le_antisymm ((compatible (hg (f a)) (hf a)).mpr le_rfl)
      ((compatible (hf a) (hg (f a))).mpr le_rfl)
    right_inv := fun b => le_antisymm ((compatible (hf (g b)) (hg b)).mp le_rfl)
      ((compatible (hg b) (hf (g b))).mp le_rfl)
    map_rel_iff' := (compatible (hf _) (hf _)).symm }⟩

end BooleanScott
