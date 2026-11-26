module
public import BooleanScott.TreeWitness

/-! Geometric content of the infinitary guard. It refers only to the
named second-derivative loci, chart isomorphism and local reserve copies.
The explicit witness satisfies every condition. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Topology Filter Descriptive
open scoped Classical OnePoint

structure GuardData (T : tree ℕ) (X : Type) [TopologicalSpace X] where
  vertex : Vertex → X
  distinct : Function.Injective vertex
  private_anchor (v : Vertex) : (tagAnchor (tagNumber (.inl v))).points X = {vertex v}
  edge_anchor (v : Vertex) (i : ℕ) : v++[i] ∈ T →
    (tagAnchor (tagNumber (.inr (v,i)))).points X ⊆ {vertex v, vertex (v++[i])}
  chart (v : Vertex) : ∃ C : Clopens X, vertex v ∈ C ∧ Nonempty (VertexChart (sectorTags T v) ≃ₜ C)
  finite_or_cofinite (C : Clopens X) :
    {v | vertex v ∈ C}.Finite ∨ {v | vertex v ∉ C}.Finite
  reserve (C : Clopens X) (j : ℕ) : {v | vertex v ∈ C}.Infinite →
    ∃ D : Clopens X, D ≤ C ∧ Nonempty (Mixed (2*j) ≃ₜ D)

theorem copy_in_clopen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [CompactSpace X] {f : X → Y} (hf : IsOpenEmbedding f) :
    ∃ D : Clopens Y, (D : Set Y) = range f ∧ Nonempty (X ≃ₜ D) :=
  ⟨⟨range f,(isCompact_range hf.continuous).isClosed,hf.isOpen_range⟩,rfl,⟨hf.toIsEmbedding.toHomeomorph⟩⟩

theorem witness_vertex_side (T : tree ℕ) (C : Clopens (WitnessSpace T)) :
    {v | (witnessVertex T v ∈ C) ≠ (∞ ∈ C)}.Finite := by
  obtain ⟨_,F,tail⟩ := (clopen_array_iff _).mp C.isClopen
  apply (F.finite_toSet.preimage (Sum.inl_injective (α := Vertex) (β := ℕ × ℕ)).injOn).subset
  intro v h
  by_contra out
  apply h
  exact propext (tail (.inl v) out ∞)

noncomputable def witness_guard (T : tree ℕ) : GuardData T (WitnessSpace T) where
  vertex := witnessVertex T
  distinct := witnessVertex_injective T
  private_anchor v := by rw [witness_named_anchors]; simp [tagSupport]
  edge_anchor v i retained := by rw [witness_named_anchors]; simp [tagSupport,retained]
  chart v := by
    let := (witness_stone T).1
    have emb : IsOpenEmbedding (vertexIn T v) := open_packetInclusion _ _
    obtain ⟨D,eq,iso⟩ := copy_in_clopen emb
    exact ⟨D,show witnessVertex T v ∈ (D : Set _) from eq ▸ mem_range_self ∞,iso⟩
  finite_or_cofinite C := by
    by_cases h : ∞ ∈ C
    · right
      exact (witness_vertex_side T C).subset fun v hv e => hv (e.symm ▸ h)
    · left
      exact (witness_vertex_side T C).subset fun v hv e => h (e ▸ hv)
  reserve C j many := by
    have h : ∞ ∈ C := by
      by_contra out
      exact many ((witness_vertex_side T C).subset fun v hv e => out (e ▸ hv))
    obtain ⟨n,hn⟩ := witness_infinite_reserve T j C (C.isClopen.isOpen.mem_nhds h)
    let := (witness_stone T).1
    have emb : IsOpenEmbedding (reserveIn T j n) := open_packetInclusion _ _
    obtain ⟨D,eq,iso⟩ := copy_in_clopen emb
    refine ⟨D,?_,iso⟩
    change (D : Set (WitnessSpace T)) ⊆ C
    rw [eq]
    exact hn

variable {T : tree ℕ} {X : Type} [TopologicalSpace X] (G : GuardData T X)

theorem GuardData.chart_contains_only {v : Vertex} {C : Clopens X}
    (g : VertexChart (sectorTags T v) ≃ₜ C) {w : Vertex} (hw : G.vertex w ∈ C) : w=v := by
  let e := tagNumber (.inl w)
  have mark : G.vertex w ∈ (tagAnchor e).points X := by rw [G.private_anchor]; rfl
  have inc : IsOpenEmbedding (fun x : C => (x : X)) := C.isClopen.isOpen.isOpenEmbedding_subtypeVal
  let x : C := ⟨G.vertex w,hw⟩
  have rel := (Set.ext_iff.mp ((tagAnchor e).restricts inc) x).mp mark
  have inside := (Set.ext_iff.mp ((tagAnchor e).restricts g.symm.isOpenEmbedding) x).mpr rel
  by_contra neq
  have absent : e ∉ sectorTags T v := fun h => neq (Finset.mem_singleton.mp ((tagNumber_mem_sector ..).mp h)).symm
  rw [tagAnchor_chart,ite_eq_right absent] at inside
  exact inside

theorem GuardData.isolated_vertex (v : Vertex) :
    ∃ C : Clopens X, G.vertex v ∈ C ∧ ∀ w, G.vertex w ∈ C → w=v := by
  obtain ⟨C,h,⟨g⟩⟩ := G.chart v
  exact ⟨C,h,fun _ => G.chart_contains_only g⟩

theorem GuardData.vertex_limit [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X] :
    ∃! x, x ∈ derivedSet (range G.vertex) := by
  apply unique_anchor_limit _ (infinite_range_of_injective G.distinct)
  intro C hc
  rcases G.finite_or_cofinite ⟨C,hc⟩ with h|h
  · exact Or.inl ((h.image G.vertex).subset (by rintro _ ⟨cx,v,rfl⟩; exact ⟨v,cx,rfl⟩))
  · exact Or.inr ((h.image G.vertex).subset (by rintro _ ⟨cx,v,rfl⟩; exact ⟨v,cx,rfl⟩))

theorem GuardData.limit_not_vertex [CompactSpace X] [T2Space X] {x : X} (hx : x ∈ derivedSet (range G.vertex))
    (v : Vertex) : x ≠ G.vertex v := by
  rintro rfl
  obtain ⟨C,hc,only⟩ := G.isolated_vertex v
  have inf := (clopen_hits_derived C.isClopen).mp ⟨_,hc,hx⟩
  apply inf
  apply (finite_singleton (G.vertex v)).subset
  rintro z ⟨hz,w,rfl⟩
  exact congrArg G.vertex (only w hz)

theorem GuardData.near_limit_reserve [CompactSpace X] [T2Space X] {x : X}
    (hx : x ∈ derivedSet (range G.vertex)) (C : Clopens X) (hc : x ∈ C) (j : ℕ) :
    ∃ D : Clopens X, D ≤ C ∧ Nonempty (Mixed (2*j) ≃ₜ D) := by
  apply G.reserve
  intro finite
  have inf := (clopen_hits_derived C.isClopen).mp ⟨_,hc,hx⟩
  apply inf
  exact (finite.image G.vertex).subset (by rintro _ ⟨cy,v,rfl⟩; exact ⟨v,cy,rfl⟩)

end BooleanScott
