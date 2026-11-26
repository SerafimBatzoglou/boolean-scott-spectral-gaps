module
public import BooleanScott.ArrayHomeomorphism
public import BooleanScott.PacketTransport

/-! Finite equal column counts and eventual coverage of each row produce a
homeomorphism of the compactified arrays, even with arbitrary extra stationary
tag packets. Column names are retained by the chosen reindexing. -/
@[expose] public section
namespace BooleanScott
open Set Filter

abbrev Entries {I : Type} (s : ℕ → Finset I) := Σ j, s j

theorem ledgerDepartures {I : Type} (s t : ℕ → Finset I)
    (count : ∀ j, (s j).card = (t j).card)
    (src : ∀ i, ∀ᶠ j in atTop, i ∈ s j) (dst : ∀ i, ∀ᶠ j in atTop, i ∈ t j) :
    ∃ e : ∀ j, s j ≃ t j,
      FiniteDepartures (fun p : Entries s => p.2.val) (fun p => (e p.1 p.2).val) ∧
      FiniteDepartures (fun p : Entries s => (e p.1 p.2).val) (fun p => p.2.val) := by
  classical
  obtain ⟨e,he⟩ := protectedTransport s t count src dst
  refine ⟨e, ?_, ?_⟩
  · intro i
    obtain ⟨k,hk⟩ := he i
    let F := (Finset.range k).sigma (fun j => (Finset.univ : Finset (s j)))
    apply F.finite_toSet.subset
    rintro ⟨j,x⟩ ⟨same,moved⟩
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_range.mpr (lt_of_not_ge (fun h => moved ((hk j h).1 x same))),
      Finset.mem_univ _⟩
  · intro i
    obtain ⟨k,hk⟩ := he i
    let F := (Finset.range k).sigma (fun j => (Finset.univ : Finset (s j)))
    apply F.finite_toSet.subset
    rintro ⟨j,x⟩ ⟨same,moved⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_not_ge (fun h => moved ?_)), Finset.mem_univ _⟩
    simpa using (hk j h).2 (e j x) same

theorem FiniteDepartures.withStationary {I E K : Type} {a b : E → I}
    (h : FiniteDepartures a b) (owner : K → I) :
    FiniteDepartures (Sum.elim a owner) (Sum.elim b owner) := by
  intro i
  apply ((h i).image (Sum.inl : E → E ⊕ K)).subset
  rintro (e | k) ⟨ha,hb⟩
  · exact ⟨e,⟨ha,hb⟩,rfl⟩
  · exact (hb ha).elim

/-- Source entries index the physical packets. On the right each column is
identified with the actual target entries by its displayed bijection. -/
theorem ledgerArrayHomeomorph {I K : Type} (s t : ℕ → Finset I) (owner : K → I)
    (X : Entries s ⊕ K → Type) [∀ e, TopologicalSpace (X e)] [∀ e, CompactSpace (X e)]
    (count : ∀ j, (s j).card = (t j).card)
    (src : ∀ i, ∀ᶠ j in atTop, i ∈ s j) (dst : ∀ i, ∀ᶠ j in atTop, i ∈ t j) :
    ∃ e : ∀ j, s j ≃ t j, Nonempty
      (OnePoint (PuncturedArray X (Sum.elim (fun p : Entries s => p.2.val) owner)) ≃ₜ
       OnePoint (PuncturedArray X (Sum.elim (fun p : Entries s => (e p.1 p.2).val) owner))) := by
  obtain ⟨e,hf,hb⟩ := ledgerDepartures s t count src dst
  exact ⟨e, ⟨compactArrayHomeomorph X (hf.withStationary owner) (hb.withStationary owner)⟩⟩

end BooleanScott
