module
public import BooleanScott.VertexSectors
public import BooleanScott.TreeReduction

/-! Compare a literal guard sector with its image under a putative absorbing
homeomorphism. Include the new row in precisely the root sector. Pulling a
clopen back to the two original summands preserves its actual type. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace Descriptive
open scoped OnePoint Classical

variable {X : Type} [TopologicalSpace X]

noncomputable def extraRow (v : Vertex) : Clopens RootRow := if v=[] then ⊤ else ⊥

noncomputable def imageCut (f : (X ⊕ RootRow) ≃ₜ X) (C : Clopens X) (D : Clopens RootRow) : Clopens X :=
  clopensOfHomeomorph f (sumClopen C D)

theorem imageCut_left (f : (X ⊕ RootRow) ≃ₜ X) (C : Clopens X) (D : Clopens RootRow) (x : X) :
    f (.inl x) ∈ imageCut f C D ↔ x ∈ C := by
  change f.symm (f (.inl x)) ∈ sumClopen C D ↔ _
  rw [f.symm_apply_apply]; rfl

theorem imageCut_right (f : (X ⊕ RootRow) ≃ₜ X) (C : Clopens X) (D : Clopens RootRow) (x : RootRow) :
    f (.inr x) ∈ imageCut f C D ↔ x ∈ D := by
  change f.symm (f (.inr x)) ∈ sumClopen C D ↔ _
  rw [f.symm_apply_apply]; rfl

theorem imageCut_compl (f : (X ⊕ RootRow) ≃ₜ X) (C : Clopens X) (D : Clopens RootRow) :
    (imageCut f C D)ᶜ = imageCut f Cᶜ Dᶜ := by
  ext x
  obtain ⟨x|x,rfl⟩ := f.surjective x
  · exact (not_congr (imageCut_left f C D x)).trans (imageCut_left f Cᶜ Dᶜ x).symm
  · exact (not_congr (imageCut_right f C D x)).trans (imageCut_right f Cᶜ Dᶜ x).symm

theorem imageCut_sup (f : (X ⊕ RootRow) ≃ₜ X) (C E : Clopens X) (D F : Clopens RootRow) :
    imageCut f C D ⊔ imageCut f E F = imageCut f (C ⊔ E) (D ⊔ F) := by
  ext x
  obtain ⟨x|x,rfl⟩ := f.surjective x
  · exact (or_congr (imageCut_left f C D x) (imageCut_left f E F x)).trans (imageCut_left f (C ⊔ E) (D ⊔ F) x).symm
  · exact (or_congr (imageCut_right f C D x) (imageCut_right f E F x)).trans (imageCut_right f (C ⊔ E) (D ⊔ F) x).symm

theorem imageCut_disjoint (f : (X ⊕ RootRow) ≃ₜ X) {C E : Clopens X} {D F : Clopens RootRow}
    (ce : Disjoint (C : Set X) (E : Set X)) (df : Disjoint (D : Set RootRow) (F : Set RootRow)) :
    Disjoint (imageCut f C D : Set X) (imageCut f E F : Set X) := by
  apply Set.disjoint_left.mpr
  intro z l r
  obtain ⟨x|x,rfl⟩ := f.surjective z
  · exact Set.disjoint_left.mp ce ((imageCut_left ..).mp l) ((imageCut_left ..).mp r)
  · exact Set.disjoint_left.mp df ((imageCut_right ..).mp l) ((imageCut_right ..).mp r)

theorem extraRow_disjoint {u v : Vertex} (ne : u≠v) :
    Disjoint (extraRow u : Set RootRow) (extraRow v : Set RootRow) := by
  by_cases hu : u=[] <;> by_cases hv : v=[] <;> simp_all [extraRow]

theorem extraRow_ledger (v : Vertex) (j : ℕ) :
    (privateLocus (2*j)).count (spaceType (extraRow v)) = if v=[] then 1 else 0 := by
  rw [LocalLocus.count_clopen]
  have eq : (privateLocus (2*j)).points RootRow = {ledgerMarker (tagNumber (.inl [])) 0 j} :=
    Set.ext (fun p => (row_ledger_points _ 0 j p).trans (and_iff_right (Nat.zero_le j)))
  rw [eq]
  by_cases hv : v=[] <;> simp [extraRow,hv]

theorem extraRow_absent {T : tree ℕ} {v : Vertex} {e : ℕ} (out : e ∉ sectorTags T v) :
    (tagRoot e).count (spaceType (extraRow v)) = 0 := by
  rw [LocalLocus.count_clopen,tagRoot_row]
  by_cases hv : v=[]
  · subst v
    have ne : tagNumber (.inl []) ≠ e := fun eq => out (eq ▸ (tagNumber_mem_sector T [] (.inl [])).mpr (Finset.mem_singleton_self _))
    simp [ne]
  · simp [extraRow,hv]

variable [CompactSpace X] [T2Space X]

theorem pulled_cut_sum (f : (X ⊕ RootRow) ≃ₜ X) (D : Clopens X) :
    spaceType D = spaceType (clopenPreimage (f.continuous.comp continuous_inl) D) +
      spaceType (clopenPreimage (f.continuous.comp continuous_inr) D) := by
  let := (row_stone (tagNumber (.inl [])) 0).1
  let U := clopenPreimage f.continuous D
  have h : spaceType U = spaceType D := pull_spaceType f.isOpenEmbedding D (by simp [f.surjective.range_eq])
  rw [← h]
  exact (spaceType_eq_iff _ _).mpr ⟨(splitSubspace U).symm⟩

theorem imageCut_type (f : (X ⊕ RootRow) ≃ₜ X) (C : Clopens X) (D : Clopens RootRow) :
    spaceType (imageCut f C D) = spaceType C + spaceType D := by
  rw [pulled_cut_sum f]
  have left : clopenPreimage (f.continuous.comp continuous_inl) (imageCut f C D) = C :=
    SetLike.ext (imageCut_left f C D)
  have right : clopenPreimage (f.continuous.comp continuous_inr) (imageCut f C D) = D :=
    SetLike.ext (imageCut_right f C D)
  rw [left,right]

omit [CompactSpace X] [T2Space X] in
theorem fixes_guard_vertex {T : tree ℕ} (G : GuardData T X) (f : (X ⊕ RootRow) ≃ₜ X) (v : Vertex) :
    f (.inl (G.vertex v)) = G.vertex v := by
  let e := tagNumber (.inl v)
  have emb : IsOpenEmbedding (f ∘ (Sum.inl : X → X ⊕ RootRow)) := f.isOpenEmbedding.comp .inl
  have mark : G.vertex v ∈ (tagAnchor e).points X := by rw [G.private_anchor]; rfl
  have inside := (Set.ext_iff.mp ((tagAnchor e).restricts emb) (G.vertex v)).mpr mark
  exact (Set.ext_iff.mp (G.private_anchor v) _).mp inside

noncomputable def shiftedCut {T : tree ℕ} {G : GuardData T X} {v : Vertex} (b : Sector G v) (f : (X ⊕ RootRow) ≃ₜ X) :=
  imageCut f b.region (extraRow v)

theorem shifted_sector {T : tree ℕ} {G : GuardData T X} {v : Vertex} (b : Sector G v) (f : (X ⊕ RootRow) ≃ₜ X) :
    ∃ a : Sector G v, a.region = shiftedCut b f := by
  have fixV := fixes_guard_vertex G f v
  refine ⟨⟨shiftedCut b f,?_,fun j => ?_,fun e out => ?_,fun D hd miss => ?_⟩,rfl⟩
  · rw [← fixV]
    exact (imageCut_left ..).mpr b.center
  · obtain ⟨m,hm⟩ := b.finite_ledger j
    refine ⟨m+(if v=[] then 1 else 0),?_⟩
    rw [shiftedCut,imageCut_type,map_add,hm,extraRow_ledger,Nat.cast_add]
    split <;> simp
  · rw [shiftedCut,imageCut_type,map_add,b.absent e out,extraRow_absent out,add_zero]
  · rw [pulled_cut_sum f D]
    apply ledgerBalance_add
    · apply b.balance
      · exact fun x hx => (imageCut_left ..).mp (hd (show f (.inl x) ∈ D from hx))
      · change f (.inl (G.vertex v)) ∉ D
        rw [fixV]
        exact miss
    · exact row_clopen_balance _ _ _

end BooleanScott
