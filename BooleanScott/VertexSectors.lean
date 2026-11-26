module
public import BooleanScott.LedgerBalance

/-! Each guarded vertex has a compact clopen sector inside a chart. The
sectors can be disjoint even with infinitely many neighbors. Every cut of a
sector missing its own vertex satisfies the finite root and ledger balance. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace Descriptive
open scoped OnePoint Classical

theorem pull_spaceType {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X] [CompactSpace Y] [T2Space X]
    {f : Y → X} (e : IsOpenEmbedding f) (C : Clopens X) (sub : (C : Set X) ⊆ range f) :
    spaceType (clopenPreimage e.continuous C) = spaceType C := by
  let D := clopenPreimage e.continuous C
  let g (x : D) : C := ⟨f x.val,x.property⟩
  have inj : Function.Injective g := fun a b h => Subtype.ext (e.injective (congrArg (fun z : C => (z : X)) h))
  have surj : Function.Surjective g := by
    rintro ⟨x,hx⟩
    obtain ⟨y,rfl⟩ := sub hx
    exact ⟨⟨y,hx⟩,rfl⟩
  let := clopen_compactSpace D
  exact (spaceType_eq_iff _ _).mpr ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨inj,surj⟩)
    ((e.continuous.comp continuous_subtype_val).subtype_mk _)⟩

structure Sector {T : tree ℕ} {X : Type} [TopologicalSpace X] (G : GuardData T X) (v : Vertex) where
  region : Clopens X
  center : G.vertex v ∈ region
  finite_ledger (j : ℕ) : ∃ m : ℕ, (privateLocus (2*j)).count (spaceType region) = (m : ℕ∞)
  absent (e : ℕ) : e ∉ sectorTags T v → (tagRoot e).count (spaceType region) = 0
  balance (D : Clopens X) : D ≤ region → G.vertex v ∉ D → HasLedgerBalance (spaceType D)

theorem sector_of_chart {T : tree ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (G : GuardData T X)
    (v : Vertex) (C : Clopens X) (g : VertexChart (sectorTags T v) ≃ₜ C)
    (B : Clopens X) (bv : G.vertex v ∈ B) (sub : B ≤ C) :
    ∃ b : Sector G v, b.region = B := by
  let S := sectorTags T v
  let f (p : VertexChart S) : X := (g p).val
  have embedding : IsOpenEmbedding f := C.isClopen.isOpen.isOpenEmbedding_subtypeVal.comp g.isOpenEmbedding
  have covers : (C : Set X) ⊆ range f := by
    intro x hx
    obtain ⟨p,eq⟩ := g.surjective ⟨x,hx⟩
    exact ⟨p,congrArg Subtype.val eq⟩
  have center : f ∞ = G.vertex v := by
    let e := tagNumber (.inl v)
    have mark : (∞ : VertexChart S) ∈ (tagAnchor e).points (VertexChart S) := by
      rw [tagAnchor_chart,ite_eq_left ((tagNumber_mem_sector T v (.inl v)).mpr (Finset.mem_singleton_self _))]
      rfl
    have hx := (Set.ext_iff.mp ((tagAnchor e).restricts embedding) ∞).mpr mark
    exact (Set.ext_iff.mp (G.private_anchor v) (f ∞)).mp hx
  let B' := clopenPreimage embedding.continuous B
  have eq := pull_spaceType embedding B (fun _ h => covers (sub h))
  refine ⟨⟨B,bv,fun j => ?_,fun e out => ?_,fun D hd miss => ?_⟩,rfl⟩
  · rw [← eq,LocalLocus.count_clopen]
    exact ⟨_,(chart_ledger_finite (sectorTags_nonempty T v) B' j).cast_ncard_eq.symm⟩
  · rw [← eq,chart_tag_count]
    apply encard_eq_zero.mpr
    exact eq_empty_iff_forall_notMem.mpr fun r h => out ((h.2 : r.1.val=e) ▸ r.1.property)
  · rw [← pull_spaceType embedding D (fun _ h => covers (sub (hd h)))]
    apply chart_clopen_balance (sectorTags_nonempty T v)
    change f ∞ ∉ D
    rw [center]
    exact miss

theorem disjoint_vertex_sectors {T : tree ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    (G : GuardData T X) : ∃ b : ∀ v : Vertex, Sector G v,
      Pairwise (fun v w => Disjoint ((b v).region : Set X) ((b w).region : Set X)) := by
  classical
  choose C hit homeo using G.chart
  let g (v : Vertex) := Classical.choice (homeo v)
  let before (v : Vertex) := (Finset.range (Encodable.encode v)).preimage (Encodable.encode (α := Vertex))
    Encodable.encode_injective.injOn
  have earlier {v w : Vertex} : w ∈ before v ↔ Encodable.encode w < Encodable.encode v := by simp [before]
  let B (v : Vertex) := C v ⊓ ((before v).sup C)ᶜ
  have bv (v : Vertex) : G.vertex v ∈ B v := by
    refine ⟨hit v,?_⟩
    intro h
    obtain ⟨w,hw,inc⟩ := (mem_clopen_finSup _ _ _).mp h
    have same := G.chart_contains_only (g w) inc
    exact ((earlier.mp hw).ne (congrArg Encodable.encode same.symm))
  choose b heq using fun v => sector_of_chart G v (C v) (g v) (B v) (bv v) inf_le_left
  refine ⟨b,fun v w ne => ?_⟩
  change Disjoint ((b v).region : Set X) ((b w).region : Set X)
  rw [heq,heq]
  apply Set.disjoint_left.mpr
  rintro x ⟨cv,beforeV⟩ ⟨cw,beforeW⟩
  rcases lt_or_gt_of_ne (Encodable.encode_injective.ne ne) with lt|gt
  · exact beforeW ((mem_clopen_finSup _ _ _).mpr ⟨v,earlier.mpr lt,cv⟩)
  · exact beforeV ((mem_clopen_finSup _ _ _).mpr ⟨w,earlier.mpr gt,cw⟩)

end BooleanScott
