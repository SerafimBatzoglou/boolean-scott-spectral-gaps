module
public import BooleanScott.ClopenCodes
public import BooleanScott.MixedPacket
public import BooleanScott.StoneAbsorption

/-! The packet candidates define countable Boolean algebras. In a sum of
compact Stone spaces, the tails of whole components and clopens contained
in individual components form a clopen basis. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology TopologicalSpace
open scoped OnePoint

theorem clopen_compactSpace {X : Type} [TopologicalSpace X] [CompactSpace X] (C : Clopens X) :
    CompactSpace C := isCompact_iff_compactSpace.mp C.isClopen.isClosed.isCompact

theorem packetSum_zeroDimensional {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] [∀ i, ZeroDimensionalSpace (X i)] :
    ZeroDimensionalSpace (PacketSum X) := by
  classical
  let := packetSum_hausdorff X
  apply zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.mpr
  apply isTopologicalBasis_of_isOpen_of_nhds (fun (s : Set _) (h : IsClopen s) => h.isOpen)
  intro z U hz op
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨F,hF⟩ := cofinite_components_of_nhds (op.mem_nhds hz)
    let V : Set (PacketSum X) := {p | p.elim True (fun y => y.1 ∉ F)}
    have cl : IsClopen V := by
      apply (clopen_array_iff V).mpr
      refine ⟨fun i => ?_,F,fun i hi _ => iff_of_true hi trivial⟩
      change IsClopen { _x : X i | i ∉ F }
      by_cases hi : i ∈ F <;> simp [hi]
      · exact isClopen_empty
      · exact isClopen_univ
    refine ⟨V,cl,trivial,?_⟩
    intro y hy
    induction y using OnePoint.rec with
    | infty => exact hz
    | coe p => exact hF p.1 hy p.2
  | coe p =>
    rcases p with ⟨i,x⟩
    let f := packetInclusion X i
    let e := open_packetInclusion X i
    obtain ⟨V,hV,hx,sub⟩ := exists_isClopen_mem_of_isOpen (op.preimage e.continuous) hz
    refine ⟨f '' V,⟨(hV.isClosed.isCompact.image e.continuous).isClosed,e.isOpenMap _ hV.isOpen⟩,
      ⟨x,hx,rfl⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact sub hx

theorem tower_zeroDimensional (d : ℕ) : ZeroDimensionalSpace (tower d) := by
  induction d with
  | zero => change ZeroDimensionalSpace Unit; infer_instance
  | succ d ih =>
    let := ih
    exact packetSum_zeroDimensional (fun _ : ℕ => (tower d : Type))

theorem tower_countable_clopens (d : ℕ) : Countable (Clopens (tower d)) := by
  induction d with
  | zero =>
    change Countable (Clopens Unit)
    exact SetLike.coe_injective.countable
  | succ d ih =>
    let := ih
    exact countable_array_clopens (X := fun _ : ℕ => (tower d : Type))

theorem cantor_countable_clopens : Countable (Clopens CantorBits) :=
  Clopens.countable_iff_secondCountable.mpr inferInstance

theorem sum_zeroDimensional (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ZeroDimensionalSpace X] [ZeroDimensionalSpace Y] : ZeroDimensionalSpace (X ⊕ Y) := by
  apply zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.mpr
  apply isTopologicalBasis_of_isOpen_of_nhds (fun (s : Set _) (h : IsClopen s) => h.isOpen)
  rintro (x|y) U hU hu
  · obtain ⟨V,hV,hx,sub⟩ := exists_isClopen_mem_of_isOpen (hu.preimage continuous_inl) hU
    exact ⟨Sum.inl '' V,⟨isClosedMap_inl _ hV.isClosed,isOpenMap_inl _ hV.isOpen⟩,
      ⟨x,hx,rfl⟩,image_subset_iff.mpr sub⟩
  · obtain ⟨V,hV,hy,sub⟩ := exists_isClopen_mem_of_isOpen (hu.preimage continuous_inr) hU
    exact ⟨Sum.inr '' V,⟨isClosedMap_inr _ hV.isClosed,isOpenMap_inr _ hV.isOpen⟩,
      ⟨y,hy,rfl⟩,image_subset_iff.mpr sub⟩

theorem mixed_stone (d : ℕ) :
    T2Space (Mixed d) ∧ ZeroDimensionalSpace (Mixed d) ∧ Countable (Clopens (Mixed d)) := by
  let := tower_zeroDimensional d
  let := tower_countable_clopens d
  let := cantor_countable_clopens
  let := sum_zeroDimensional CantorBits (tower d)
  let := (sumClopensIso (X := CantorBits) (Y := (tower d : Type))).injective.countable
  exact ⟨packetSum_hausdorff _,packetSum_zeroDimensional _,countable_array_clopens⟩

end BooleanScott
