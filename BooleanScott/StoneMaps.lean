module
public import BooleanScott.StoneModel
public import Mathlib.Order.BooleanAlgebra.Basic

/-! Recover the homeomorphism of compact Stone spaces from an arbitrary
isomorphism of their clopen algebras. This permits passing from an
unpointed algebra isomorphism to the geometric necessity argument. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_image_point [CompactSpace Y] (e : Clopens X ≃o Clopens Y) (x : X) :
    ∃ y : Y, ∀ C : Clopens X, y ∈ e C ↔ x ∈ C := by
  classical
  let N := {C : Clopens X // x ∈ C}
  let : Nonempty N := ⟨⟨⊤,mem_univ x⟩⟩
  let K (i : N) : Set Y := e i.val
  have dir : Directed (· ⊇ ·) K := by
    intro i j
    refine ⟨⟨i.val ⊓ j.val, And.intro i.property j.property⟩, ?_, ?_⟩
    · exact e.monotone (show i.val ⊓ j.val ≤ i.val from inf_le_left)
    · exact e.monotone (show i.val ⊓ j.val ≤ j.val from inf_le_right)
  have pos (i : N) : (K i).Nonempty := by
    by_contra! he
    have hbot : e i.val = ⊥ := SetLike.coe_injective he
    have hb : i.val = ⊥ := e.injective (hbot.trans e.map_bot.symm)
    exact (show x ∉ (⊥ : Clopens X) from fun h => h) (hb ▸ i.property)
  have hc (i : N) : IsClosed (K i) := (e i.val).isClopen.isClosed
  obtain ⟨y,hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K dir pos
    (fun i => (hc i).isCompact) hc
  have keep (C : Clopens X) (h : x ∈ C) : y ∈ e C := mem_iInter.mp hy ⟨C,h⟩
  refine ⟨y,fun C => ⟨?_, keep C⟩⟩
  intro h
  by_contra hn
  have out := keep Cᶜ hn
  rw [map_compl' e C] at out
  exact out h

noncomputable def clopenImagePoint [CompactSpace Y] (e : Clopens X ≃o Clopens Y) (x : X) : Y :=
  (exists_image_point e x).choose

theorem clopenImagePoint_mem [CompactSpace Y] (e : Clopens X ≃o Clopens Y) (x : X)
    (C : Clopens X) : clopenImagePoint e x ∈ e C ↔ x ∈ C :=
  (exists_image_point e x).choose_spec C

theorem eq_of_clopen_mem [T1Space X] [ZeroDimensionalSpace X] {x z : X}
    (h : ∀ C : Clopens X, x ∈ C ↔ z ∈ C) : x = z := by
  by_contra hn
  obtain ⟨V,hV,hx,hz⟩ := exists_isClopen_mem_of_isOpen (isOpen_compl_singleton (x := z)) hn
  exact (hz ((h ⟨V,hV⟩).mp hx)) rfl

theorem continuous_clopenImagePoint [CompactSpace Y] [ZeroDimensionalSpace Y]
    (e : Clopens X ≃o Clopens Y) : Continuous (clopenImagePoint e) := by
  apply isTopologicalBasis_isClopen.continuous_iff.mpr
  intro V hV
  let D : Clopens Y := ⟨V,hV⟩
  have same : clopenImagePoint e ⁻¹' V = (e.symm D : Set X) := by
    ext x
    change clopenImagePoint e x ∈ D ↔ x ∈ e.symm D
    simpa only [e.apply_symm_apply] using clopenImagePoint_mem e x (e.symm D)
  exact same ▸ (e.symm D).isClopen.isOpen

theorem clopenImagePoint_leftInverse [CompactSpace X] [CompactSpace Y]
    [T1Space X] [ZeroDimensionalSpace X] (e : Clopens X ≃o Clopens Y) :
    Function.LeftInverse (clopenImagePoint e.symm) (clopenImagePoint e) := by
  intro x
  apply eq_of_clopen_mem
  intro C
  have back := clopenImagePoint_mem e.symm (clopenImagePoint e x) (e C)
  simpa only [e.symm_apply_apply] using back.trans (clopenImagePoint_mem e x C)

noncomputable def homeomorphOfClopens [CompactSpace X] [CompactSpace Y] [T1Space X] [T1Space Y]
    [ZeroDimensionalSpace X] [ZeroDimensionalSpace Y] (e : Clopens X ≃o Clopens Y) : X ≃ₜ Y where
  toFun := clopenImagePoint e
  invFun := clopenImagePoint e.symm
  left_inv := clopenImagePoint_leftInverse e
  right_inv := clopenImagePoint_leftInverse e.symm
  continuous_toFun := continuous_clopenImagePoint e
  continuous_invFun := continuous_clopenImagePoint e.symm

end BooleanScott
