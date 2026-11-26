module
public import BooleanScott.ChartTypes

/-! Exact and eventual incidence in actual chart fragments. Ledger counts
are finite in each individual column. In a fragment missing the vertex
their eventual value is precisely its number of retained row roots. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology TopologicalSpace
open scoped OnePoint Classical

def ledgerMarker (e n j : ℕ) : TagRow e n := packetInclusion (RowPacket e n) (.inl (j-n)) ∞

theorem row_ledger_points (e n j : ℕ) (p : TagRow e n) :
    p ∈ privateMark (TagRow e n) (2*j) ↔ n ≤ j ∧ p=ledgerMarker e n j := by
  constructor
  · intro mark
    induction p using OnePoint.rec with
    | infty => exact (row_root_not_private e n _ mark).elim
    | coe p =>
      rcases p with ⟨i,x⟩
      obtain ⟨deg,rfl⟩ := (row_packet_private e n (2*j) i x).mp mark
      cases i with
      | inl i =>
        change 2*(n+i)=2*j at deg
        have eq : j-n=i := by omega
        exact ⟨by omega,congrArg (fun k => packetInclusion (RowPacket e n) (.inl k) ∞) eq.symm⟩
      | inr i => change 2*e+1=2*j at deg; omega
  · rintro ⟨le,rfl⟩
    apply (row_packet_private e n (2*j) (.inl (j-n)) ∞).mpr
    exact ⟨by change 2*(n+(j-n))=2*j; omega,rfl⟩

theorem ledgerMarker_tendsto (e n : ℕ) : Tendsto (ledgerMarker e n) atTop (𝓝 ∞) := by
  let f : ℕ ↪ ℕ ⊕ ℕ := ⟨Sum.inl,Sum.inl_injective⟩
  exact (packetMarkers_tendsto (P := RowPacket e n) f (fun _ => ∞)).comp (tendsto_sub_atTop_nat n)

def eligibleRow {S : Set ℕ} (r : ChartIndex S) (j : ℕ) := r.1.val+r.2 ≤ j
def chartMarker {S : Set ℕ} (r : ChartIndex S) (j : ℕ) : ChartRow r := ledgerMarker r.1.val (r.1.val+r.2) j
def chartRoot {S : Set ℕ} (r : ChartIndex S) : ChartRow r := ∞

theorem component_points_injective {I : Type} (X : I → Type) (p : ∀ i, X i) :
    Function.Injective (fun i => packetInclusion X i (p i)) :=
  fun _ _ h => congrArg Sigma.fst (OnePoint.coe_injective h)

theorem chart_ledger_image {S : Set ℕ} (hn : S.Nonempty) (C : Clopens (VertexChart S)) (j : ℕ) :
    (C : Set (VertexChart S)) ∩ privateMark (VertexChart S) (2*j) =
    (fun r => packetInclusion ChartRow r (chartMarker r j)) '' markedRows chartMarker eligibleRow (C : Set (VertexChart S)) j := by
  ext p
  constructor
  · rintro ⟨inside,mark⟩
    induction p using OnePoint.rec with
    | infty => exact (chart_root_not_private hn _ mark).elim
    | coe p =>
      obtain ⟨r,x⟩ := p
      have localMark := (local_component ChartRow (privateLocus (2*j)) r x).mp mark
      obtain ⟨eligible,rfl⟩ := (row_ledger_points _ _ _ x).mp localMark
      exact ⟨r,⟨eligible,inside⟩,rfl⟩
  · rintro ⟨r,⟨eligible,inside⟩,rfl⟩
    exact ⟨inside,(local_component ChartRow (privateLocus (2*j)) r _).mpr ((row_ledger_points _ _ _ _).mpr ⟨eligible,rfl⟩)⟩

theorem chart_ledger_count {S : Set ℕ} (hn : S.Nonempty) (C : Clopens (VertexChart S)) (j : ℕ) :
    (privateLocus (2*j)).count (spaceType C) = (markedRows chartMarker eligibleRow (C : Set (VertexChart S)) j).encard := by
  rw [LocalLocus.count_clopen]
  change ((C : Set (VertexChart S)) ∩ privateMark _ (2*j)).encard = _
  rw [chart_ledger_image hn,(component_points_injective ChartRow (fun r => chartMarker r j)).encard_image]

theorem chart_ledger_finite {S : Set ℕ} (hn : S.Nonempty) (C : Clopens (VertexChart S)) (j : ℕ) :
    ((C : Set (VertexChart S)) ∩ privateMark (VertexChart S) (2*j)).Finite := by
  rw [chart_ledger_image hn]
  apply Set.Finite.image
  apply (finite_ledger_rows S j).subset
  exact fun _ h => h.1

theorem chart_fragment_ledger {S : Set ℕ} (hn : S.Nonempty) (C : Clopens (VertexChart S)) (away : ∞ ∉ C) :
    (rootRows chartRoot (C : Set (VertexChart S))).Finite ∧
    ∀ᶠ j : ℕ in atTop, (privateLocus (2*j)).count (spaceType C) = (rootRows chartRoot (C : Set (VertexChart S))).encard := by
  obtain ⟨fin,ev⟩ := fragment_markedRows (r := chartRoot) (m := chartMarker) (eligible := eligibleRow)
    (fun r => ledgerMarker_tendsto _ _) (fun r => eventually_ge_atTop (r.1.val+r.2)) C.isClopen away
  refine ⟨fin,?_⟩
  filter_upwards [ev] with j hj
  rw [chart_ledger_count hn,hj]

theorem chart_tag_count {S : Set ℕ} (C : Clopens (VertexChart S)) (e : ℕ) :
    (tagRoot e).count (spaceType C) = {r : ChartIndex S | r ∈ rootRows chartRoot (C : Set (VertexChart S)) ∧ r.1.val=e}.encard := by
  rw [LocalLocus.count_clopen]
  let z (r : ChartIndex S) := packetInclusion ChartRow r (chartRoot r)
  have eq : (C : Set (VertexChart S)) ∩ (tagRoot e).points (VertexChart S) =
      z '' {r : ChartIndex S | r ∈ rootRows chartRoot (C : Set (VertexChart S)) ∧ r.1.val=e} := by
    ext p
    constructor
    · rintro ⟨hc,hr⟩
      induction p using OnePoint.rec with
      | infty => exact (tagRoot_chart_vertex S e hr).elim
      | coe p =>
        obtain ⟨r,x⟩ := p
        obtain ⟨tag,rfl⟩ := (tagRoot_chart_row r e x).mp hr
        exact ⟨r,⟨hc,tag⟩,rfl⟩
    · rintro ⟨r,⟨hc,tag⟩,rfl⟩
      exact ⟨hc,(tagRoot_chart_row r e _).mpr ⟨tag,rfl⟩⟩
  rw [eq,(component_points_injective ChartRow chartRoot).encard_image]

end BooleanScott
