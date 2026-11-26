module
public import BooleanScott.BranchReserves

/-! Local branch surgery in an arbitrary guarded compact space. Reserve an
outgoing row in the literal chart, complete its finite prefix near the
limit, and retain a base neighborhood that exchanges the two row tags. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace Descriptive
open scoped Classical OnePoint

variable {T : tree ℕ} {X : Type} [TopologicalSpace X]

structure BranchBlock (G : GuardData T X) (t : X) (v : Vertex) (a b : ℕ) where
  base : Clopens X
  row : Clopens X
  apart : Disjoint (base : Set X) (row : Set X)
  limit_out : t ∉ base ⊔ row
  only (w : Vertex) : G.vertex w ∈ base ⊔ row → w=v
  row_type : spaceType row = spaceType (TagRow b 0)
  exchange : spaceType base + spaceType (TagRow a 0) = spaceType base + spaceType (TagRow b 0)

abbrev BranchBlock.site {G : GuardData T X} {t : X} {v : Vertex} {a b : ℕ} (p : BranchBlock G t v a b) :=
  p.base ⊔ p.row

variable [CompactSpace X] [T2Space X] (G : GuardData T X)

theorem GuardData.allocate_block {t : X} (ht : t ∈ derivedSet (range G.vertex)) (v : Vertex)
    {a b : ℕ} (ha : a ∈ sectorTags T v) (hb : b ∈ sectorTags T v) (U : Clopens X)
    (hu : t ∈ U) (hv : G.vertex v ∈ U) : ∃ P : BranchBlock G t v a b, P.site ≤ U := by
  let S := sectorTags T v
  obtain ⟨C,hvC,⟨g⟩⟩ := G.chart v
  let f (p : VertexChart S) := (g p).val
  have emb : IsOpenEmbedding f := C.isClopen.isOpen.isOpenEmbedding_subtypeVal.comp g.isOpenEmbedding
  have cover : (C : Set X) ⊆ range f := by
    intro x hx
    obtain ⟨p,eq⟩ := g.surjective ⟨x,hx⟩
    exact ⟨p,congrArg Subtype.val eq⟩
  have center : f ∞ = G.vertex v := by
    let e := tagNumber (.inl v)
    have mark : (∞ : VertexChart S) ∈ (tagAnchor e).points _ := by
      rw [tagAnchor_chart,ite_eq_left ((tagNumber_mem_sector T v (.inl v)).mpr (Finset.mem_singleton_self _))]
      rfl
    have inX := (Set.ext_iff.mp ((tagAnchor e).restricts emb) ∞).mpr mark
    exact (Set.ext_iff.mp (G.private_anchor v) (f ∞)).mp inX
  have miss : t ∉ C := G.finite_site_misses_limit ht C ((finite_singleton v).subset (fun _ h => G.chart_contains_only g h))
  let V := C ⊓ U
  have hit : f ∞ ∈ V := center ▸ (show G.vertex v ∈ V from ⟨hvC,hv⟩)
  have nh := emb.continuous.continuousAt (V.isClopen.isOpen.mem_nhds hit)
  obtain ⟨F,all⟩ := cofinite_components_of_nhds nh
  obtain ⟨r,tag,good⟩ := ((infinity_of_tag_rows S b).mpr hb).exists_notMem_finset F
  have component := emb.comp (open_packetInclusion ChartRow r)
  obtain ⟨R,rangeR,⟨gr⟩⟩ := copy_in_clopen component
  have rv : R ≤ V := by
    intro x hx
    obtain ⟨y,rfl⟩ := (Set.ext_iff.mp rangeR x).mp hx
    exact all r good y
  have noCenter : f ∞ ∉ R := by
    intro h
    obtain ⟨y,eq⟩ := (Set.ext_iff.mp rangeR (f ∞)).mp h
    exact OnePoint.coe_ne_infty _ (emb.injective eq)
  let B := V \ R
  have inBase : f ∞ ∈ B := ⟨hit,noCenter⟩
  have inC : (B : Set X) ⊆ C := fun _ h => h.1.1
  let D := clopenPreimage emb.continuous B
  have changeRow := vertex_row_exchange D inBase ha hb 0
  have typeB := pull_spaceType emb B (inC.trans cover)
  change spaceType D = spaceType B at typeB
  rw [typeB] at changeRow
  let k := rowStart r
  have rowType : spaceType R = spaceType (TagRow b k) := by
    have eq := (spaceType_eq_iff _ _).mpr ⟨gr.symm⟩
    exact eq.trans (congrArg (fun e => spaceType (TagRow e k)) tag)
  obtain ⟨Q,qu,qt,qv,qtype⟩ := G.reserve_prefix ht (U \ C) ⟨hu,miss⟩ k
  have qr : Disjoint (R : Set X) (Q : Set X) := Set.disjoint_left.mpr (fun _ r q => (qu q).2 (rv r).1)
  refine ⟨⟨B,R⊔Q,?_,?_,?_,?_,changeRow⟩,?_⟩
  · apply Set.disjoint_left.mpr
    rintro x h (r|q)
    · exact h.2 r
    · exact (qu q).2 h.1.1
  · rintro (b|r|q)
    · exact miss b.1.1
    · exact miss (rv r).1
    · exact qt q
  · rintro w (b|r|q)
    · exact G.chart_contains_only g b.1.1
    · exact G.chart_contains_only g (rv r).1
    · exact (qv w q).elim
  · rw [clopen_sup_type _ _ qr,rowType,qtype,row_prefix]
  · rintro x (b|r|q)
    · exact b.1.2
    · exact (rv r).2
    · exact (qu q).1

end BooleanScott
