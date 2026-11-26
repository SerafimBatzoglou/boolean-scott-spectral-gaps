module
public import BooleanScott.RowRecognition
public import BooleanScott.TreeParameters

/-! The tree witness and its actual finite tag supports. Vertex and edge
names are encoded once, independently of the input tree. The outer reserve
provides infinitely many entire ledger packets of every degree. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace Descriptive
open scoped OnePoint Classical

abbrev Vertex := List ℕ
abbrev TagName := Vertex ⊕ (Vertex × ℕ)

def tagNumber (t : TagName) : ℕ := Encodable.encode t
theorem tagNumber_injective : Function.Injective tagNumber := Encodable.encode_injective

noncomputable def tagSupport (T : tree ℕ) : TagName → Finset Vertex
  | .inl v => {v}
  | .inr (v,i) => if v++[i] ∈ T then {v,v++[i]} else ∅

def sectorTags (T : tree ℕ) (v : Vertex) : Set ℕ :=
  {e | ∃ t : TagName, tagNumber t=e ∧ v ∈ tagSupport T t}

theorem tagNumber_mem_sector (T : tree ℕ) (v : Vertex) (t : TagName) :
    tagNumber t ∈ sectorTags T v ↔ v ∈ tagSupport T t := by
  constructor
  · rintro ⟨u,eq,mem⟩
    exact tagNumber_injective eq ▸ mem
  · exact fun h => ⟨t,rfl,h⟩

theorem sectorTags_nonempty (T : tree ℕ) (v : Vertex) : (sectorTags T v).Nonempty :=
  ⟨tagNumber (.inl v),(tagNumber_mem_sector ..).mpr (Finset.mem_singleton_self _)⟩

theorem finite_tag_sectors (T : tree ℕ) (e : ℕ) : {v | e ∈ sectorTags T v}.Finite := by
  by_cases used : e ∈ range tagNumber
  · obtain ⟨t,rfl⟩ := used
    exact (tagSupport T t).finite_toSet.subset fun v hv => (tagNumber_mem_sector ..).mp hv
  · apply (finite_empty (α := Vertex)).subset
    rintro v ⟨t,eq,_⟩
    exact used ⟨t,eq⟩

abbrev WitnessIndex := Vertex ⊕ (ℕ × ℕ)

noncomputable def witnessComponent (T : tree ℕ) : WitnessIndex → CompHaus.{0}
  | .inl v => by
    let := (chart_stone (sectorTags T v)).1
    exact CompHaus.of (VertexChart (sectorTags T v))
  | .inr (j,_) => by
    let := (mixed_stone (2*j)).1
    exact CompHaus.of (Mixed (2*j))

abbrev WitnessSpace (T : tree ℕ) := PacketSum (fun i => (witnessComponent T i : Type))

theorem witness_stone (T : tree ℕ) :
    T2Space (WitnessSpace T) ∧ ZeroDimensionalSpace (WitnessSpace T) ∧ Countable (Clopens (WitnessSpace T)) := by
  let hz (i : WitnessIndex) : ZeroDimensionalSpace (witnessComponent T i) := by
    rcases i with v|⟨j,n⟩
    · exact (chart_stone _).2.1
    · exact (mixed_stone _).2.1
  let hc (i : WitnessIndex) : Countable (Clopens (witnessComponent T i)) := by
    rcases i with v|⟨j,n⟩
    · exact (chart_stone _).2.2
    · exact (mixed_stone _).2.2
  exact ⟨packetSum_hausdorff _,packetSum_zeroDimensional _,countable_array_clopens⟩

def vertexIn (T : tree ℕ) (v : Vertex) : VertexChart (sectorTags T v) → WitnessSpace T :=
  packetInclusion (fun i => (witnessComponent T i : Type)) (.inl v)

def witnessVertex (T : tree ℕ) (v : Vertex) := vertexIn T v ∞

theorem witnessVertex_injective (T : tree ℕ) : Function.Injective (witnessVertex T) := by
  intro u v eq
  exact Sum.inl.inj (congrArg Sigma.fst (OnePoint.coe_injective eq))

def reserveIn (T : tree ℕ) (j n : ℕ) : Mixed (2*j) → WitnessSpace T :=
  packetInclusion (fun i => (witnessComponent T i : Type)) (.inr (j,n))

theorem chart_first_nonempty (tags : Set ℕ) (e : ℕ) :
    ((tagFirst e).points (VertexChart tags)).Nonempty ↔ e ∈ tags := by
  constructor
  · rintro ⟨p,hp⟩
    induction p using OnePoint.rec with
    | infty => exact (chart_root_tag_derivative tags e).mp hp
    | coe p =>
      obtain ⟨r,x⟩ := p
      have eq := ((chart_row_tag_derivative r x e).mp hp).1
      exact eq ▸ r.1.property
  · intro he
    exact ⟨∞,(chart_root_tag_derivative tags e).mpr he⟩

theorem reserve_no_first (j e : ℕ) : (tagFirst e).points (Mixed (2*j)) = ∅ := by
  change derivedSet (privateMark _ _) = ∅
  let := (mixed_stone (2*j)).1
  apply finite_mark_derivative_empty
  rw [mixed_private_mark]
  split <;> simp

theorem witness_anchor_top (T : tree ℕ) (e : ℕ) : (∞ : WitnessSpace T) ∉ (tagAnchor e).points (WitnessSpace T) := by
  change ∞ ∉ derivedSet ((tagFirst e).points (WitnessSpace T))
  rw [infty_in_derived_iff,occupied_locus _ (tagFirst e)]
  intro inf
  apply inf
  apply ((finite_tag_sectors T e).image (Sum.inl : Vertex → WitnessIndex)).subset
  rintro (v|⟨j,n⟩) h
  · exact ⟨v,(chart_first_nonempty _ e).mp h,rfl⟩
  · change ((tagFirst e).points (Mixed (2*j))).Nonempty at h
    rw [reserve_no_first] at h
    obtain ⟨_,hx⟩ := h
    exact False.elim hx

theorem witness_tag_anchors (T : tree ℕ) (e : ℕ) : (tagAnchor e).points (WitnessSpace T) =
    witnessVertex T '' {v | e ∈ sectorTags T v} := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    apply iff_of_false (witness_anchor_top T e)
    rintro ⟨v,_,eq⟩
    exact OnePoint.coe_ne_infty _ eq
  | coe p =>
    rcases p with ⟨v | ⟨j,n⟩,x⟩
    · apply (local_component (fun i => (witnessComponent T i : Type)) (tagAnchor e) (.inl v) x).trans
      change x ∈ (tagAnchor e).points (VertexChart (sectorTags T v)) ↔ _
      rw [tagAnchor_chart]
      by_cases h : e ∈ sectorTags T v
      · rw [ite_eq_left h]
        constructor
        · rintro rfl; exact ⟨v,h,rfl⟩
        · rintro ⟨w,_,eq⟩
          have idx := congrArg Sigma.fst (OnePoint.coe_injective eq)
          obtain rfl : w = v := Sum.inl.inj idx
          exact (Sigma.mk.inj_iff.mp (OnePoint.coe_injective eq)).2.eq.symm
      · rw [ite_eq_right h]
        refine iff_of_false id ?_
        rintro ⟨w,hw,eq⟩
        have idx := congrArg Sigma.fst (OnePoint.coe_injective eq)
        exact h ((Sum.inl.inj idx : w=v) ▸ hw)
    · have empty : (tagAnchor e).points (Mixed (2*j)) = ∅ := by
        change derivedSet ((tagFirst e).points _) = ∅
        rw [reserve_no_first]
        exact finite_mark_derivative_empty finite_empty
      apply iff_of_false
      · intro hp
        have inside := (local_component (fun i => (witnessComponent T i : Type)) (tagAnchor e) (.inr (j,n)) x).mp hp
        exact (Set.ext_iff.mp empty x).mp inside
      · rintro ⟨w,_,eq⟩
        have ix : (Sum.inl w : WitnessIndex) = .inr (j,n) := congrArg Sigma.fst (OnePoint.coe_injective eq)
        cases ix

theorem witness_named_anchors (T : tree ℕ) (t : TagName) :
    (tagAnchor (tagNumber t)).points (WitnessSpace T) = witnessVertex T '' (tagSupport T t : Set Vertex) := by
  rw [witness_tag_anchors]
  exact congrArg (Set.image _) (Set.ext fun v => tagNumber_mem_sector T v t)

theorem witness_infinite_reserve (T : tree ℕ) (j : ℕ) (U : Set (WitnessSpace T)) (hu : U ∈ 𝓝 ∞) :
    ∃ n, range (reserveIn T j n) ⊆ U := by
  obtain ⟨F,hF⟩ := cofinite_components_of_nhds hu
  let f (n : ℕ) : WitnessIndex := .inr (j,n)
  have inf := infinite_range_of_injective (show Function.Injective f from
    fun _ _ h => congrArg Prod.snd (Sum.inr.inj h))
  obtain ⟨_,⟨n,rfl⟩,out⟩ := inf.exists_notMem_finset F
  exact ⟨n,fun _ ⟨x,eq⟩ => eq ▸ hF (f n) out x⟩

end BooleanScott
