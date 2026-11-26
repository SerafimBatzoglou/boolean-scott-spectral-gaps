module
public import BooleanScott.RowExchange

/-! Finite prefixes of even ledger packets convert a row of any cutoff
to a row starting at column zero. The guard supplies the entire prefix
in any neighborhood of the common limit, disjoint from every vertex. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace Descriptive
open scoped Classical OnePoint

noncomputable def ledgerPrefix (n : ℕ) : SpaceType := ∑ j ∈ Finset.range n, spaceType (Mixed (2*j))

theorem row_pop_ledger (e n : ℕ) :
    spaceType (TagRow e n) = spaceType (TagRow e (n+1)) + spaceType (Mixed (2*n)) := by
  let ht (i : ℕ ⊕ ℕ) : T2Space (RowPacket e n i) := (mixed_stone _).1
  let := (row_stone e n).1
  let A := rowTail e n 1 0
  let B := packetLift (RowPacket e n) (.inl 0) ⊤
  have complement : (⊤ \ A : Clopens (TagRow e n)) = B := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      apply iff_of_false (fun h => h.2 (show ∞ ∈ A from rfl))
      rintro ⟨y,_,eq⟩
      exact OnePoint.coe_ne_infty _ eq
    | coe p =>
      obtain ⟨i,y⟩ := p
      change (_ ∧ packetInclusion _ i y ∉ rowTail e n 1 0) ↔ _
      rw [rowTail_fiber]
      cases i with
      | inr i =>
        apply iff_of_false (fun h => h.2 (Nat.zero_le _))
        rintro ⟨z,_,eq⟩
        cases congrArg Sigma.fst (OnePoint.coe_injective eq)
      | inl i =>
        cases i with
        | zero => exact iff_of_true ⟨trivial,Nat.not_succ_le_zero 0⟩ ⟨y,trivial,rfl⟩
        | succ i =>
          apply iff_of_false (fun h => h.2 (Nat.succ_le_succ (Nat.zero_le _)))
          rintro ⟨z,_,eq⟩
          cases congrArg Sigma.fst (OnePoint.coe_injective eq)
  have eq := split_subclopen (show A ≤ ⊤ from le_top)
  rw [complement,univ_clopen_spaceType (C := (⊤ : Clopens (TagRow e n))) (fun _ => trivial)] at eq
  change spaceType (TagRow e n) = spaceType (rowTail e n 1 0) + spaceType (packetLift (RowPacket e n) (.inl 0) ⊤) at eq
  rw [rowTail_type,packetLift_type,univ_clopen_spaceType (fun _ => trivial)] at eq
  exact eq

theorem row_prefix (e n : ℕ) : spaceType (TagRow e n)+ledgerPrefix n=spaceType (TagRow e 0) := by
  induction n with
  | zero => simp [ledgerPrefix]
  | succ n ih =>
    rw [← ih,row_pop_ledger e n,ledgerPrefix,Finset.sum_range_succ]
    unfold ledgerPrefix
    ac_rfl

variable {T : tree ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : GuardData T X)

theorem GuardData.finite_site_misses_limit {t : X} (ht : t ∈ derivedSet (range G.vertex)) (C : Clopens X)
    (fin : {v | G.vertex v ∈ C}.Finite) : t ∉ C := by
  intro hit
  have inf := (clopen_hits_derived C.isClopen).mp ⟨t,hit,ht⟩
  exact inf ((fin.image G.vertex).subset (by rintro _ ⟨h,v,rfl⟩; exact ⟨v,h,rfl⟩))

omit [CompactSpace X] [T2Space X] in
theorem GuardData.reserve_avoids_vertices (j : ℕ) (C : Clopens X) (g : Mixed (2*j) ≃ₜ C) (v : Vertex) :
    G.vertex v ∉ C := by
  intro hit
  let e := tagNumber (.inl v)
  let x : C := ⟨G.vertex v,hit⟩
  have atV : G.vertex v ∈ (tagAnchor e).points X := by rw [G.private_anchor]; rfl
  have atCopy : x ∈ (tagAnchor e).points C := (Set.ext_iff.mp ((tagAnchor e).restricts C.isClopen.isOpen.isOpenEmbedding_subtypeVal) x).mp atV
  have point := (Set.ext_iff.mp ((tagAnchor e).restricts g.symm.isOpenEmbedding) x).mpr atCopy
  change g.symm x ∈ derivedSet ((tagFirst e).points (Mixed (2*j))) at point
  let := (mixed_stone (2*j)).1
  rw [reserve_no_first,finite_mark_derivative_empty finite_empty] at point
  exact point

theorem GuardData.reserve_prefix {t : X} (ht : t ∈ derivedSet (range G.vertex)) (U : Clopens X) (hu : t ∈ U)
    (n : ℕ) : ∃ D : Clopens X, D ≤ U ∧ t ∉ D ∧ (∀ v, G.vertex v ∉ D) ∧ spaceType D=ledgerPrefix n := by
  induction n with
  | zero => exact ⟨⊥,bot_le,id,fun _ => id,by rw [clopen_bot_type]; simp [ledgerPrefix]⟩
  | succ n ih =>
    obtain ⟨D,du,miss,no,form⟩ := ih
    obtain ⟨A,sub,⟨g⟩⟩ := G.near_limit_reserve ht (U \ D) ⟨hu,miss⟩ n
    have apart : Disjoint (D : Set X) (A : Set X) := Set.disjoint_left.mpr (fun _ hd ha => (sub ha).2 hd)
    have avoid := G.reserve_avoids_vertices n A g
    have atLimit := G.finite_site_misses_limit ht A (finite_empty.subset (fun v h => (avoid v h).elim))
    refine ⟨D⊔A,sup_le du (sub.trans sdiff_le),fun h => h.elim miss atLimit,fun v h => h.elim (no v) (avoid v),?_⟩
    rw [clopen_sup_type _ _ apart,form,(spaceType_eq_iff _ _).mpr ⟨g.symm⟩]
    exact (Finset.sum_range_succ _ _).symm

end BooleanScott
