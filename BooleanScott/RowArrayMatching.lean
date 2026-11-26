module
public import BooleanScott.ChartLedger
public import BooleanScott.LedgerArrays

/-! Matching arrays of concrete rows by their tag and their exact finite
column counts. The two cutoff functions may differ at infinitely many rows. -/
@[expose] public section
namespace BooleanScott
open Filter Set Topology
open scoped Classical OnePoint

noncomputable def sigmaFamilyCongr {I J : Type} {X : I → Type} {Y : J → Type}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (e : I ≃ J) (h : ∀ i, X i ≃ₜ Y (e i)) : (Σ i, X i) ≃ₜ (Σ j, Y j) :=
  IsHomeomorph.homeomorph _ (IsHomeomorph.sigmaMap e.bijective (fun i => (h i).isHomeomorph))

variable {I : Type} {s : ℕ → Finset I}

abbrev PacketEntry (s : ℕ → Finset I) := Entries s ⊕ (I × ℕ)

def entryDegree (tag : I → ℕ) : PacketEntry s → ℕ :=
  Sum.elim (fun p => 2*p.1) (fun p => 2*tag p.1+1)

def entryOwner (atRow : ∀ j, s j → I) : PacketEntry s → I :=
  Sum.elim (fun p => atRow p.1 p.2) Prod.fst

variable (tag cut : I → ℕ) (label : ∀ j, s j ≃ {i // cut i ≤ j})

def rowSlot (i : I) (a : ℕ ⊕ ℕ) : {p : PacketEntry s // entryOwner (fun j z => (label j z).val) p = i} :=
  match a with
  | .inl n => ⟨.inl ⟨cut i+n,(label _).symm ⟨i,Nat.le_add_right _ _⟩⟩,
      congrArg Subtype.val ((label _).apply_symm_apply _)⟩
  | .inr n => ⟨.inr (i,n),rfl⟩

theorem rowSlot_bijective (i : I) : Function.Bijective (rowSlot cut label i) := by
  constructor
  · rintro (m|m) (n|n) eq
    · have h := congrArg Subtype.val eq
      exact congrArg Sum.inl (Nat.add_left_cancel (congrArg Sigma.fst (Sum.inl.inj h)))
    · have h := congrArg Subtype.val eq
      cases h
    · have h := congrArg Subtype.val eq
      cases h
    · have h := congrArg Subtype.val eq
      exact congrArg Sum.inr (congrArg Prod.snd (Sum.inr.inj h))
  · rintro ⟨⟨j,z⟩|⟨r,n⟩,h⟩
    · change (label j z).val = i at h
      subst i
      have key (i : I) (n : ℕ) (bound : cut i ≤ n) :
          (rowSlot cut label i (.inl (n-cut i))).val =
          .inl ⟨n,(label n).symm ⟨i,bound⟩⟩ := by
        obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le bound
        rw [show cut i + k - cut i = k by omega]
        rfl
      refine ⟨.inl (j-cut (label j z).val),Subtype.ext ?_⟩
      rw [key _ _ (label j z).property]
      simp
    · change r = i at h
      subst r
      exact ⟨.inr n,rfl⟩

noncomputable def tagRow_as_ownerRow (i : I) : TagRow (tag i) (cut i) ≃ₜ
    Row (fun p : PacketEntry s => Mixed (entryDegree tag p))
      (entryOwner (fun j z => (label j z).val)) i := by
  let e := Equiv.ofBijective (rowSlot cut label i) (rowSlot_bijective cut label i)
  apply Homeomorph.onePointCongr (sigmaFamilyCongr e ?_)
  intro a
  cases a <;> exact Homeomorph.refl _

def eligibleEquiv (s : Finset I) (cut : I → ℕ) (j : ℕ) (mem : ∀ i, i ∈ s ↔ cut i ≤ j) :
    s ≃ {i // cut i ≤ j} := Equiv.subtypeEquivRight mem

theorem match_row_arrays (tag a b : I → ℕ)
    (finiteA : ∀ j, {i | a i ≤ j}.Finite) (finiteB : ∀ j, {i | b i ≤ j}.Finite)
    (counts : ∀ j, {i | a i ≤ j}.ncard = {i | b i ≤ j}.ncard) :
    Nonempty ((Σ i, TagRow (tag i) (a i)) ≃ₜ (Σ i, TagRow (tag i) (b i))) := by
  classical
  let s j := (finiteA j).toFinset
  let t j := (finiteB j).toFinset
  let ls j : s j ≃ {i // a i ≤ j} := eligibleEquiv (s j) a j (fun i => (finiteA j).mem_toFinset)
  let lt j : t j ≃ {i // b i ≤ j} := eligibleEquiv (t j) b j (fun i => (finiteB j).mem_toFinset)
  have size (j : ℕ) : (s j).card = (t j).card := by
    simpa only [Set.ncard_eq_toFinset_card _ (finiteA j),Set.ncard_eq_toFinset_card _ (finiteB j)] using counts j
  obtain ⟨e,forward,backward⟩ := ledgerDepartures s t size
    (fun i => (eventually_ge_atTop (a i)).mono (fun j h => (finiteA j).mem_toFinset.mpr h))
    (fun i => (eventually_ge_atTop (b i)).mono (fun j h => (finiteB j).mem_toFinset.mpr h))
  let source := sigmaFamilyCongr (Equiv.refl I) (tagRow_as_ownerRow tag a ls)
  let target := sigmaFamilyCongr (Equiv.refl I) (tagRow_as_ownerRow tag b (fun j => (e j).trans (lt j)))
  let shifted := puncturedArrayHomeomorph (fun p : PacketEntry s => Mixed (entryDegree tag p))
    (forward.withStationary (Prod.fst : I × ℕ → I)) (backward.withStationary Prod.fst)
  exact ⟨(source.trans shifted).trans target.symm⟩

end BooleanScott
