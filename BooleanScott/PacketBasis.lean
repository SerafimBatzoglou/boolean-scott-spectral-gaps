module
public import BooleanScott.PacketAbsorption

/-! Deleting any finite initial segment of whole components gives an
actual clopen copy of the original repeated space, fixing the apex. These
copies refine every apex neighborhood. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology
open scoped OnePoint

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

noncomputable def repeatedAbsorb : (Repeated X ⊕ X) ≃ₜ Repeated X := by
  let := packetSum_hausdorff (fun _ : ℕ => X)
  exact (onePoint_withCompact (Copies X) X).symm.trans (absorbCopy X).onePointCongr

noncomputable def dropFirst (p : Repeated X) := repeatedAbsorb X (Sum.inl p)

theorem dropFirst_open : IsOpenEmbedding (dropFirst X) :=
  (repeatedAbsorb X).isOpenEmbedding.comp .inl

theorem dropFirst_infty : dropFirst X ∞ = ∞ := by
  let := packetSum_hausdorff (fun _ : ℕ => X)
  let h := onePoint_withCompact (Copies X) X
  have eq : h.symm (Sum.inl ∞) = ∞ := h.symm_apply_eq.mpr rfl
  change (absorbCopy X).onePointCongr (h.symm (Sum.inl ∞)) = ∞
  rw [eq]
  rfl

theorem dropFirst_coe (i : ℕ) (x : X) :
    dropFirst X (packetInclusion (fun _ : ℕ => X) i x) = packetInclusion (fun _ : ℕ => X) (i+1) x := by
  let := packetSum_hausdorff (fun _ : ℕ => X)
  let h := onePoint_withCompact (Copies X) X
  let p : Copies X := ⟨i,x⟩
  have eq : h.symm (Sum.inl (OnePoint.some p)) = OnePoint.some (Sum.inl p) := h.symm_apply_eq.mpr rfl
  change (absorbCopy X).onePointCongr (h.symm (Sum.inl (OnePoint.some p))) = _
  rw [eq]
  rfl

theorem tail_openEmbedding (k : ℕ) : IsOpenEmbedding ((dropFirst X)^[k]) := by
  induction k with
  | zero => exact .id
  | succ k ih => exact ih.comp (dropFirst_open X)

theorem tail_image (k i : ℕ) (x : X) :
    (dropFirst X)^[k] (packetInclusion (fun _ : ℕ => X) i x) =
    packetInclusion (fun _ : ℕ => X) (i+k) x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,dropFirst_coe]; rfl

theorem repeated_basis {U : Set (Repeated X)} (hU : U ∈ 𝓝 ∞) :
    ∃ (f : Repeated X → Repeated X), IsOpenEmbedding f ∧ f ∞ = ∞ ∧
      IsClopen (range f) ∧ range f ⊆ U := by
  classical
  let := packetSum_hausdorff (fun _ : ℕ => X)
  obtain ⟨F,hF⟩ := cofinite_components_of_nhds hU
  let k := F.sup id + 1
  let f := (dropFirst X)^[k]
  have e := tail_openEmbedding X k
  have root : f ∞ = ∞ := Function.IsFixedPt.iterate (dropFirst_infty X) k
  refine ⟨f,e,root,⟨(isCompact_range e.continuous).isClosed,e.isOpen_range⟩,?_⟩
  rintro _ ⟨p,rfl⟩
  induction p using OnePoint.rec with
  | infty => exact root.symm ▸ mem_of_mem_nhds hU
  | coe p =>
    rcases p with ⟨i,x⟩
    change (dropFirst X)^[k] (packetInclusion _ i x) ∈ U
    rw [tail_image]
    apply hF
    intro hi
    have bound : i+k ≤ F.sup id := Finset.le_sup (f := id) hi
    dsimp [k] at bound
    omega

end BooleanScott
