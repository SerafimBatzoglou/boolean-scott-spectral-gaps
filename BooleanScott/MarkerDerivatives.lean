module
public import BooleanScott.ClopenCounting

/-! A uniform syntactic derivative operation on incidence predicates. Apply
it twice to the marker predicate of each tag to obtain the anchor test. The
semantics hold for arbitrarily chosen marks in any compact Stone space. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal
open scoped Ordinal

def Detects {X : Type} [TopologicalSpace X] (φ : Formula 1) (S : Set X) : Prop :=
  ∀ C : Clopens X, φ.Holds (BoolOps.ofAlgebra (Clopens X)) (fun _ => C) ↔ ((C : Set X) ∩ S).Nonempty

theorem infinite_iff_all_thresholds {X : Type} (S : Set X) :
    S.Infinite ↔ ∀ h, ∃ f : Fin h ↪ X, ∀ i, f i ∈ S := by
  classical
  constructor
  · intro inf h
    let e := inf.natEmbedding S
    exact ⟨((Fin.valEmbedding (n := h)).trans e).trans (Function.Embedding.subtype _),
      fun i => (e i.val).property⟩
  · intro all finite
    let := finite.fintype
    obtain ⟨f,hf⟩ := all (Fintype.card S + 1)
    let g (i : Fin (Fintype.card S+1)) : S := ⟨f i,hf i⟩
    have inj : Function.Injective g := fun _ _ h => f.injective (congrArg Subtype.val h)
    have bound := Fintype.card_le_of_injective g inj
    simp at bound

theorem count_clopen_marks {X : Type} [TopologicalSpace X] [T2Space X] [ZeroDimensionalSpace X]
    {φ : Formula 1} {S : Set X} (det : Detects φ S) (C : Clopens X) (h : ℕ) :
    (∃ u : Fin h → Clopens X,
      (∀ i, u i ≤ C ∧ φ.Holds (BoolOps.ofAlgebra (Clopens X)) (fun _ => u i)) ∧
      Pairwise (fun i j => Disjoint (u i) (u j))) ↔
    ∃ f : Fin h ↪ X, ∀ i, f i ∈ (C : Set X) ∩ S := by
  have comp (U V : Clopens X) : Disjoint U V ↔ Disjoint (U : Set X) (V : Set X) := by
    rw [disjoint_iff,disjoint_iff]
    exact SetLike.coe_injective.eq_iff.symm
  rw [clopen_threshold C.isClopen]
  constructor
  · rintro ⟨u,hu,hd⟩
    exact ⟨fun i => u i,fun i => ⟨(u i).isClopen,(hu i).1,(det _).mp (hu i).2⟩,
      fun i j neq => (comp _ _).mp (hd neq)⟩
  · rintro ⟨U,hU,hd⟩
    let u (i : Fin h) : Clopens X := ⟨U i,(hU i).1⟩
    exact ⟨u,fun i => ⟨(hU i).2.1,(det _).mpr (hU i).2.2⟩,
      fun i j neq => (comp _ _).mpr (hd neq)⟩

theorem derivative_formula {φ : Formula 1} {α : Ordinal.{0}} (lev : AtLevel .pi α φ) (pos : 0 < α) :
    ∃ ψ : Formula 1, AtLevel .pi (α+2) ψ ∧ ∀ (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X] (S : Set X), Detects φ S → Detects ψ (derivedSet S) := by
  classical
  choose θ hθ truth using threshold_formula lev pos
  let D := indexedPi (fun _ : ℕ => 0) (fun h => (θ h).pad)
  refine ⟨D,indexedPi_level (fun _ => α+1)
    (fun _ => by simpa only [add_assoc,one_add_one_eq_two] using lt_add_one (α+1))
    (fun h => (hθ h).rename _),?_⟩
  intro X _ _ _ _ S det C
  rw [clopen_hits_derived C.isClopen,infinite_iff_all_thresholds]
  change (indexedPi _ _).Holds _ _ ↔ _
  rw [holds_indexedPi]
  constructor
  · intro all h
    have hit := ((θ h).holds_pad _ Fin.elim0 _).mp (all h Fin.elim0)
    exact (count_clopen_marks det C h).mp ((truth h _ C).mp hit)
  · intro all h u
    exact ((θ h).holds_pad _ u _).mpr ((truth h _ C).mpr ((count_clopen_marks det C h).mpr (all h)))

theorem second_derivative_formula {φ : Formula 1} {α : Ordinal.{0}} (lev : AtLevel .pi α φ) (pos : 0 < α) :
    ∃ ψ : Formula 1, AtLevel .pi (α+4) ψ ∧ ∀ (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X] (S : Set X), Detects φ S →
      Detects ψ (derivedSet (derivedSet S)) := by
  obtain ⟨first,h1,t1⟩ := derivative_formula lev pos
  obtain ⟨second,h2,t2⟩ := derivative_formula h1 (by positivity)
  exact ⟨second,by simpa only [add_assoc,show (2:Ordinal.{0})+2=4 by norm_num] using h2,
    fun X _ _ _ _ S h => t2 X _ (t1 X S h)⟩

end BooleanScott
