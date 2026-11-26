module
public import BooleanScott.ArrayFragments
public import BooleanScott.FiniteTypes

/-! A finite tuple's full finite-level agreement transfers every single
finite clopen test to each sign. In particular it yields exact marked
counts, the vertex bit, and actual homeomorphisms for root-free signs. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace
open scoped OnePoint

def SameFiniteClopens {X : Type} [TopologicalSpace X] (C E : Clopens X) := ∀ P : StonePredicate 1,
  FiniteTest P → (P X (fun _ => C) ↔ P X (fun _ => E))

theorem sameFiniteClopens_of_tuple {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ZeroDimensionalSpace X] [Countable (Clopens X)] {n : ℕ} (v w : Fin n → Clopens X)
    (same : FiniteAgreement (BoolOps.ofAlgebra _) v w) (p : Pattern n) :
    SameFiniteClopens (signCell v p) (signCell w p) := by
  intro P h
  obtain ⟨k,_,φ,lev,truth⟩ := h
  let test := φ.substitute (fun _ => signTerm p)
  have eq (u : Fin n → Clopens X) : test.Holds (BoolOps.ofAlgebra _) u ↔ P X (fun _ => signCell u p) := by
    dsimp only [test]
    rw [Formula.holds_substitute,signTerm_eval]
    exact truth X _
  exact (eq v).symm.trans ((same k .pi test (lev.substitute _)).trans (eq w))

theorem SameFiniteClopens.count {X : Type} [TopologicalSpace X] {C E : Clopens X} (same : SameFiniteClopens C E)
    {P : LocalLocus} (h : FiniteHit P) : P.count (spaceType C) = P.count (spaceType E) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro a
  obtain ⟨k,t⟩ := count_thresholds h
  obtain ⟨φ,lev,truth⟩ := t a
  obtain ⟨ψ,hψ,s⟩ := sigma_as_pi lev
  let R : StonePredicate 1 := fun _ _ u => (a : ℕ∞) ≤ P.count (spaceType (u 0))
  have defR : FiniteTest R := by
    refine ⟨k+1,by omega,ψ,by simpa using hψ,fun Y _ _ _ _ _ u => ?_⟩
    have eq : u = fun _ => u 0 := funext fun i => congrArg u (Subsingleton.elim ..)
    exact (s _ _ u).trans (eq ▸ truth Y (u 0))
  exact same R defR

theorem SameFiniteClopens.homeomorph_of_finiteIso {X : Type} [TopologicalSpace X] {C E : Clopens X}
    (same : SameFiniteClopens C E) (h : FiniteIso (spaceType C)) : Nonempty (C ≃ₜ E) := by
  exact (spaceType_eq_iff _ _).mp (((same _ h.clopenTest).mp rfl).symm)

theorem row_root_free_finiteIso (a n : ℕ) (C : Clopens (TagRow a n)) (away : ∞ ∉ C) : FiniteIso (spaceType C) := by
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket a n i) := (mixed_stone _).1
  obtain ⟨F,eq⟩ := array_fragment_away (RowPacket a n) C away
  rw [eq]
  exact finiteIso_sum F _ (fun i _ => finiteIso_mixed_clopen (rowDegree a n i) _)

theorem chart_root_free_finiteIso {S : Set ℕ} (C : Clopens (VertexChart S)) (away : ∞ ∉ C)
    (noRoot : ∀ r : ChartIndex S, packetInclusion ChartRow r ∞ ∉ C) : FiniteIso (spaceType C) := by
  let ht (r : ChartIndex S) : T2Space (ChartRow r) := (row_stone _ _).1
  obtain ⟨F,eq⟩ := array_fragment_away ChartRow C away
  rw [eq]
  exact finiteIso_sum F _ (fun r _ => row_root_free_finiteIso _ _ _ (noRoot r))

theorem chart_vertex_bit {S : Set ℕ} (nonempty : S.Nonempty) (C E : Clopens (VertexChart S))
    (same : SameFiniteClopens C E) : ∞ ∈ C ↔ ∞ ∈ E := by
  obtain ⟨e,he⟩ := nonempty
  have h := same _ (tagAnchor_finiteHit e).incidence
  change ((C : Set (VertexChart S)) ∩ (tagAnchor e).points _).Nonempty ↔ ((E : Set (VertexChart S)) ∩ (tagAnchor e).points _).Nonempty at h
  rw [tagAnchor_chart,ite_eq_left he,inter_singleton_nonempty,inter_singleton_nonempty] at h
  exact h

theorem chart_root_free_comparison {S : Set ℕ} (C E : Clopens (VertexChart S))
    (same : SameFiniteClopens C E) (away : ∞ ∉ C)
    (noRoot : ∀ r : ChartIndex S, packetInclusion ChartRow r ∞ ∉ C) : Nonempty (C ≃ₜ E) :=
  same.homeomorph_of_finiteIso (chart_root_free_finiteIso C away noRoot)

end BooleanScott
