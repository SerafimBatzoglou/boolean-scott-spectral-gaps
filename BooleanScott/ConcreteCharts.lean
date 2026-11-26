module
public import BooleanScott.ConcreteRows

/-! Concrete vertex charts. An allowed tag contributes infinitely many
rows. Their starting columns increase, even when the vertex has infinitely
many incident tags. The odd private marker has its second derivative exactly
at the chart vertex for an allowed tag and nowhere for a missing tag. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

abbrev ChartIndex (tags : Set ℕ) := tags × ℕ
abbrev ChartRow {tags : Set ℕ} (r : ChartIndex tags) := TagRow r.1.val (r.1.val+r.2)
abbrev VertexChart (tags : Set ℕ) := PacketSum (ChartRow (tags := tags))

theorem chart_stone (tags : Set ℕ) : T2Space (VertexChart tags) ∧
    ZeroDimensionalSpace (VertexChart tags) ∧ Countable (Clopens (VertexChart tags)) := by
  let ht (r : ChartIndex tags) : T2Space (ChartRow r) := (row_stone _ _).1
  let hz (r : ChartIndex tags) : ZeroDimensionalSpace (ChartRow r) := (row_stone _ _).2.1
  let hc (r : ChartIndex tags) : Countable (Clopens (ChartRow r)) := (row_stone _ _).2.2
  exact ⟨packetSum_hausdorff _,packetSum_zeroDimensional _,countable_array_clopens⟩

theorem chart_root_not_private {tags : Set ℕ} (nonempty : tags.Nonempty) (j : ℕ) :
    (∞ : VertexChart tags) ∉ privateMark (VertexChart tags) j := by
  rintro ⟨_,_,excl⟩
  apply excl
  rw [derivatives_succ,infty_in_derived_iff]
  obtain ⟨e,he⟩ := nonempty
  let f (n : ℕ) : ChartIndex tags := (⟨e,he⟩,n)
  apply infinite_of_injective_forall_mem (f := f) (fun _ _ h => congrArg Prod.snd h)
  intro n
  exact ⟨∞,(local_component ChartRow (scatteredStage (j+1)) (f n) ∞).mpr (row_root_stage _ _ j)⟩

theorem row_odd_mark_exists (a n e : ℕ) :
    (privateMark (TagRow a n) (2*e+1)).Nonempty ↔ a=e := by
  constructor
  · rintro ⟨p,h⟩
    induction p using OnePoint.rec with
    | infty => exact (row_root_not_private _ _ _ h).elim
    | coe p =>
      obtain ⟨i,x⟩ := p
      have eq := ((row_packet_private a n (2*e+1) i x).mp h).1
      cases i with
      | inl i => change 2*(n+i) = 2*e+1 at eq; omega
      | inr i => change 2*a+1 = 2*e+1 at eq; omega
  · rintro rfl
    exact ⟨_,(row_packet_private a n _ (.inr 0) ∞).mpr ⟨rfl,rfl⟩⟩

theorem infinity_of_tag_rows (tags : Set ℕ) (e : ℕ) : {r : ChartIndex tags | r.1.val=e}.Infinite ↔ e ∈ tags := by
  constructor
  · intro inf
    obtain ⟨r,hr⟩ := inf.nonempty
    exact (hr : r.1.val=e) ▸ r.1.property
  · intro he
    exact infinite_of_injective_forall_mem (f := fun n : ℕ => ((⟨e,he⟩ : tags),n))
      (fun _ _ h => congrArg Prod.snd h) (fun _ => rfl)

theorem occupied_locus {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)] (P : LocalLocus) :
    occupied (P.points (PacketSum X)) = {i | (P.points (X i)).Nonempty} := by
  ext i
  exact exists_congr (local_component X P i)

theorem chart_root_tag_derivative (tags : Set ℕ) (e : ℕ) :
    (∞ : VertexChart tags) ∈ derivedSet (privateMark (VertexChart tags) (2*e+1)) ↔ e ∈ tags := by
  rw [infty_in_derived_iff]
  have occ := occupied_locus (ChartRow (tags := tags)) (privateLocus (2*e+1))
  rw [show occupied (privateMark (VertexChart tags) (2*e+1)) = {r : ChartIndex tags | r.1.val=e} from
    occ.trans (Set.ext (fun r => row_odd_mark_exists r.1.val (r.1.val+r.2) e))]
  exact infinity_of_tag_rows tags e

theorem chart_row_tag_derivative {tags : Set ℕ} (r : ChartIndex tags) (p : ChartRow r) (e : ℕ) :
    packetInclusion ChartRow r p ∈ derivedSet (privateMark (VertexChart tags) (2*e+1)) ↔
      r.1.val = e ∧ p = ∞ := by
  have eq := local_derivative (open_packetInclusion ChartRow r) (privateMark (VertexChart tags) (2*e+1))
  rw [local_privateMark (open_packetInclusion ChartRow r),row_private_derivative] at eq
  apply (Set.ext_iff.mp eq p).trans
  by_cases h : r.1.val = e
  · rw [ite_eq_left (by omega)]
    exact ⟨fun hp => ⟨h,hp⟩,And.right⟩
  · rw [ite_eq_right (by omega)]
    exact iff_of_false id (fun z => h z.1)

theorem chart_second_tag (tags : Set ℕ) (e : ℕ) :
    derivedSet (derivedSet (privateMark (VertexChart tags) (2*e+1))) = if e ∈ tags then {∞} else ∅ := by
  let S := privateMark (VertexChart tags) (2*e+1)
  ext p
  induction p using OnePoint.rec with
  | infty =>
    rw [infty_in_derived_iff]
    have occ : occupied (derivedSet S) = {r : ChartIndex tags | r.1.val=e} := by
      ext r
      exact ⟨fun ⟨x,hx⟩ => ((chart_row_tag_derivative r x e).mp hx).1,fun h =>
        ⟨∞,(chart_row_tag_derivative r ∞ e).mpr ⟨h,rfl⟩⟩⟩
    change (occupied (derivedSet S)).Infinite ↔ _
    rw [occ,infinity_of_tag_rows]
    by_cases h : e ∈ tags <;> simp [h]
  | coe p =>
    obtain ⟨r,x⟩ := p
    have eR := open_packetInclusion ChartRow r
    have eq := (local_derivative eR (derivedSet S)).trans (congrArg derivedSet (local_derivative eR S))
    dsimp only [S] at eq
    rw [local_privateMark eR,row_private_derivative] at eq
    let := (row_stone r.1.val (r.1.val+r.2)).1
    have fin : (if 2*e+1 = 2*r.1.val+1 then ({∞} : Set (ChartRow r)) else ∅).Finite := by split <;> simp
    rw [finite_mark_derivative_empty fin] at eq
    apply iff_of_false (fun hx => (Set.ext_iff.mp eq x).mp hx)
    split
    · exact OnePoint.coe_ne_infty _
    · exact id

/-- The finite-column condition holds without a bound on vertex degree. -/
theorem finite_ledger_rows (tags : Set ℕ) (j : ℕ) :
    {r : ChartIndex tags | r.1.val+r.2 ≤ j}.Finite := by
  let f (r : ChartIndex tags) := (r.1.val,r.2)
  have inj : Function.Injective f := fun r s h => Prod.ext (Subtype.ext (congrArg (Prod.fst (α := ℕ) (β := ℕ)) h)) (congrArg (Prod.snd (α := ℕ) (β := ℕ)) h)
  apply (((finite_le_nat j).prod (finite_le_nat j)).preimage inj.injOn).subset
  intro r hr
  change r.1.val+r.2 ≤ j at hr
  exact ⟨by change r.1.val ≤ j; omega, by change r.2 ≤ j; omega⟩

end BooleanScott
