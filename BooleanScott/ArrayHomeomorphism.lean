module
public import BooleanScott.CompactArrays

/-! Moving finitely many whole packets per row in each direction preserves
the actual compact array up to homeomorphism. The global set of packets
moved, and the number of rows involved, can both be infinite. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology
open scoped OnePoint

variable {I E : Type} (X : E → Type) [∀ e, TopologicalSpace (X e)]

abbrev Row (owner : E → I) (i : I) :=
  OnePoint (Σ e : {j // owner j = i}, X e.val)

abbrev PuncturedArray (owner : E → I) := Σ i, Row X owner i

def movePackets (a b : E → I) : PuncturedArray X a → PuncturedArray X b :=
  fun ⟨i,r⟩ => r.elim ⟨i,∞⟩ fun ⟨e,x⟩ =>
    ⟨b e.val,OnePoint.some ⟨⟨e.val,rfl⟩,x⟩⟩

omit [∀ e, TopologicalSpace (X e)] in
theorem movePackets_leftInverse (a b : E → I) :
    Function.LeftInverse (movePackets X b a) (movePackets X a b) := by
  rintro ⟨i,r⟩
  induction r using OnePoint.rec with
  | infty => rfl
  | coe p =>
    rcases p with ⟨⟨e,he⟩,x⟩
    subst i
    rfl

def FiniteDepartures (a b : E → I) : Prop := ∀ i, {e | a e = i ∧ b e ≠ i}.Finite

theorem continuous_movePackets [∀ e, CompactSpace (X e)] {a b : E → I}
    (h : FiniteDepartures a b) : Continuous (movePackets X a b) := by
  classical
  apply continuous_sigma
  intro i
  apply continuous_iff_continuousAt.mpr
  intro r
  induction r using OnePoint.rec with
  | coe p =>
    apply OnePoint.continuousAt_coe.mpr
    apply Continuous.continuousAt
    apply continuous_sigma
    intro e
    exact continuous_sigmaMk.comp (OnePoint.continuous_coe.comp continuous_sigmaMk)
  | infty =>
    intro U hU
    have hroot : U ∈ 𝓝 (Sigma.mk i (∞ : Row X b i)) := hU
    have hrow := (continuous_sigmaMk (i := i) (σ := Row X b)).continuousAt hroot
    obtain ⟨F,hF⟩ := cofinite_components_of_nhds hrow
    let blocked : Set E := {e | a e = i ∧ b e ≠ i} ∪ Subtype.val '' (F : Set {e // b e = i})
    have hb : blocked.Finite := (h i).union (F.finite_toSet.image _)
    have hs : (Subtype.val ⁻¹' blocked : Set {e // a e = i}).Finite :=
      hb.preimage Subtype.val_injective.injOn
    have in_root : Sigma.mk i (∞ : Row X b i) ∈ U := mem_of_mem_nhds hroot
    apply nhds_of_cofinite_components in_root hs.toFinset
    intro e outside x
    have clear : e.val ∉ blocked := fun bad => outside (hs.mem_toFinset.mpr bad)
    have same : b e.val = i := by
      by_contra hn
      exact clear (Or.inl ⟨e.property,hn⟩)
    let target : {e // b e = i} := ⟨e.val,same⟩
    have ht : target ∉ F := fun hf => clear (Or.inr ⟨target,hf,rfl⟩)
    have hit := hF target ht x
    change Sigma.mk (b e.val) (OnePoint.some ⟨⟨e.val,rfl⟩,x⟩ : Row X b (b e.val)) ∈ U
    change Sigma.mk i (OnePoint.some ⟨⟨e.val,same⟩,x⟩ : Row X b i) ∈ U at hit
    have pack_eq (v : E) (k : I) (hk : b v = k) (y : X v) :
        Sigma.mk (β := Row X b) (b v) (OnePoint.some ⟨⟨v,rfl⟩,y⟩ : Row X b (b v)) =
        Sigma.mk (β := Row X b) k (OnePoint.some ⟨⟨v,hk⟩,y⟩ : Row X b k) := by subst k; rfl
    rw [pack_eq e.val i same x]
    exact hit

def puncturedArrayHomeomorph [∀ e, CompactSpace (X e)] {a b : E → I}
    (forward : FiniteDepartures a b) (inverse : FiniteDepartures b a) :
    PuncturedArray X a ≃ₜ PuncturedArray X b where
  toFun := movePackets X a b
  invFun := movePackets X b a
  left_inv := movePackets_leftInverse X a b
  right_inv := movePackets_leftInverse X b a
  continuous_toFun := continuous_movePackets X forward
  continuous_invFun := continuous_movePackets X inverse

def compactArrayHomeomorph [∀ e, CompactSpace (X e)] {a b : E → I}
    (forward : FiniteDepartures a b) (inverse : FiniteDepartures b a) :
    OnePoint (PuncturedArray X a) ≃ₜ OnePoint (PuncturedArray X b) :=
  (puncturedArrayHomeomorph X forward inverse).onePointCongr

end BooleanScott
