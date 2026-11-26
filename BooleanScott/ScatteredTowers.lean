module
public import BooleanScott.CompactDerivatives
public import Mathlib.Topology.Category.CompHaus.Basic

/-! Explicit compact scattered packets of every finite Cantor–Bendixson height.
Level zero is a point. At a successor place countably many copies of the
preceding packet in a one-point compactification. -/
@[expose] public section
namespace BooleanScott
open Set Topology
open scoped OnePoint

abbrev Repeated (X : Type) := PacketSum (fun _ : ℕ => X)

noncomputable def tower : ℕ → CompHaus.{0}
  | 0 => CompHaus.of Unit
  | d+1 => by
    let := packetSum_hausdorff (fun _ : ℕ => (tower d : Type))
    exact CompHaus.of (Repeated (tower d))

def isolatedPoints (X : Type) [TopologicalSpace X] : Set X :=
  (derivedSet (univ : Set X))ᶜ

theorem local_isolated {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (e : IsOpenEmbedding f) : f ⁻¹' isolatedPoints Y = isolatedPoints X := by
  rw [isolatedPoints, preimage_compl, local_derivative e, preimage_univ, isolatedPoints]

theorem derivative_packet {I : Type} (X : I → Type) [∀ i, TopologicalSpace (X i)]
    (j : I) (k : ℕ) {p : X j} :
    packetInclusion X j p ∈ derivatives k univ ↔ p ∈ derivatives k univ := by
  have h := local_derivatives (open_packetInclusion X j) k univ
  rw [preimage_univ] at h
  exact Set.ext_iff.mp h p

theorem repeated_root {X : Type} [TopologicalSpace X] [CompactSpace X] (k : ℕ) :
    (∞ : Repeated X) ∈ derivatives (k+1) univ ↔ (derivatives k (univ : Set X)).Nonempty := by
  rw [derivatives_succ]
  rw [infty_in_derived_iff]
  let S := derivatives k (univ : Set (Repeated X))
  have eq (i : ℕ) : i ∈ occupied S ↔ (derivatives k (univ : Set X)).Nonempty :=
    exists_congr (fun _ => derivative_packet (fun _ : ℕ => X) i k)
  constructor
  · intro h
    obtain ⟨i,hi⟩ := h.nonempty
    exact (eq i).mp hi
  · intro h
    have full : occupied S = univ := eq_univ_of_forall (fun i => (eq i).mpr h)
    exact full ▸ infinite_univ

theorem tower_height (d k : ℕ) : (derivatives k (univ : Set (tower d))).Nonempty ↔ k ≤ d := by
  induction d generalizing k with
  | zero =>
    cases k with
    | zero => exact ⟨fun _ => le_rfl,fun _ => ⟨(),mem_univ _⟩⟩
    | succ k =>
      have he (s : Set Unit) : derivedSet s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨y,⟨hy,_⟩,hn⟩ := (accPt_iff_nhds.mp hx) univ Filter.univ_mem
        exact hn (Subsingleton.elim y x)
      rw [derivatives_succ]
      change (derivedSet (derivatives k (univ : Set Unit))).Nonempty ↔ _
      simp [he]
  | succ d ih =>
    cases k with
    | zero => exact ⟨fun _ => Nat.zero_le _,fun _ => ⟨(∞ : Repeated (tower d)),mem_univ _⟩⟩
    | succ k =>
      constructor
      · rintro ⟨p,hp⟩
        change Repeated (tower d) at p
        induction p using OnePoint.rec with
        | infty => exact Nat.succ_le_succ ((ih k).mp ((repeated_root k).mp hp))
        | coe p =>
          have hin := (derivative_packet (fun _ : ℕ => (tower d : Type)) p.1 (k+1)).mp hp
          exact ((ih (k+1)).mp ⟨_,hin⟩).trans (Nat.le_succ _)
      · intro h
        exact ⟨(∞ : Repeated (tower d)),(repeated_root k).mpr ((ih k).mpr (Nat.le_of_succ_le_succ h))⟩

theorem tower_dense_isolated (d : ℕ) : closure (isolatedPoints (tower d)) = univ := by
  induction d with
  | zero =>
    have all : isolatedPoints Unit = univ := by
      apply eq_univ_of_forall
      intro x hx
      obtain ⟨y,_,hne⟩ := (accPt_iff_nhds.mp hx) univ Filter.univ_mem
      exact hne (Subsingleton.elim y x)
    change closure (isolatedPoints Unit) = _
    simp only [all,closure_univ]
    rfl
  | succ d ih =>
    let X (_ : ℕ) : Type := tower d
    let S := isolatedPoints (Repeated (tower d))
    have component (i : ℕ) : packetInclusion X i ⁻¹' closure S = univ := by
      let e := open_packetInclusion X i
      rw [e.isOpenMap.preimage_closure_eq_closure_preimage e.continuous,local_isolated e]
      exact ih
    change closure S = _
    apply eq_univ_of_forall
    intro p
    induction p using OnePoint.rec with
    | coe p => exact (Set.ext_iff.mp (component p.1) p.2).mpr trivial
    | infty =>
      apply isClosed_closure.closure_subset
      apply derivedSet_subset_closure
      apply (infty_in_derived_iff (closure S)).mpr
      have full : occupied (closure S) = univ := by
        apply eq_univ_of_forall
        intro i
        obtain ⟨x,_⟩ := (tower_height d 0).mpr (Nat.zero_le _)
        exact ⟨x,(Set.ext_iff.mp (component i) x).mpr trivial⟩
      exact full ▸ infinite_univ

end BooleanScott
