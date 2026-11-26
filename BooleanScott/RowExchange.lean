module
public import BooleanScott.ChartIsolation

/-! A vertex neighborhood can exchange whole incoming and outgoing rows
with the same ledger cutoff whenever both tags occur at the vertex. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace
open scoped Classical OnePoint

def extendLabel {I A : Type} (label : I → A) (a : A) : Option I → A
  | none => a
  | some i => label i

def extraSigma {I : Type} (Y : Option I → Type) [∀ j, TopologicalSpace (Y j)] :
    ((Σ i, Y (some i)) ⊕ Y none) ≃ₜ (Σ j, Y j) where
  toFun := Sum.elim (fun ⟨i,x⟩ => ⟨some i,x⟩) (Sigma.mk none)
  invFun := fun ⟨j,y⟩ => match j with | none => Sum.inr y | some i => Sum.inl ⟨i,y⟩
  left_inv := by rintro (⟨i,y⟩|y) <;> rfl
  right_inv := by rintro ⟨_|i,y⟩ <;> rfl
  continuous_toFun := (continuous_sigma fun _ => continuous_sigmaMk).sumElim continuous_sigmaMk
  continuous_invFun := continuous_sigma fun j => by
    cases j with
    | none => exact continuous_inr
    | some i => exact continuous_inl.comp continuous_sigmaMk

noncomputable def extend_row_chart {I : Type} (tag cut : I → ℕ) (e n : ℕ) :
    (OnePoint (Σ i, TagRow (tag i) (cut i)) ⊕ TagRow e n) ≃ₜ
      OnePoint (Σ j, TagRow (extendLabel tag e j) (extendLabel cut n j)) := by
  let ht (i : I) : T2Space (TagRow (tag i) (cut i)) := (row_stone _ _).1
  let := packetSum_hausdorff (fun i => TagRow (tag i) (cut i))
  let := (row_stone e n).1
  exact (onePoint_withCompact _ _).symm.trans
    (extraSigma (fun j => TagRow (extendLabel tag e j) (extendLabel cut n j))).onePointCongr

theorem extend_fiber_equiv {I : Type} [Countable I] (tag : I → ℕ) (a : ℕ) (many : {i | tag i=a}.Infinite) :
    ∃ f : Option I ≃ I, ∀ j, tag (f j) = extendLabel tag a j := by
  have fibers (e : ℕ) : Nonempty ({j // extendLabel tag a j=e} ≃ {i // tag i=e}) := by
    by_cases eq : a=e
    · subst e
      let := infinite_coe_iff.mpr many
      let add (x : {i // tag i=a}) : {j // extendLabel tag a j=a} := ⟨some x.val,x.property⟩
      let := Infinite.of_injective add (fun x y eq => Subtype.ext (Option.some.inj (congrArg Subtype.val eq)))
      exact nonempty_equiv_of_countable
    · let up (x : {i // tag i=e}) : {j // extendLabel tag a j=e} := ⟨some x.val,x.property⟩
      have sur : Function.Surjective up := by
        rintro ⟨_|i,h⟩
        · exact (eq h).elim
        · exact ⟨⟨i,h⟩,rfl⟩
      exact ⟨(Equiv.ofBijective up ⟨fun x y h => Subtype.ext (Option.some.inj (congrArg Subtype.val h)),sur⟩).symm⟩
  let g e := (fibers e).some
  exact ⟨Equiv.ofFiberEquiv g,Equiv.ofFiberEquiv_map g⟩

theorem exchange_rows {I : Type} [Countable I] (tag cut : I → ℕ)
    (finite : ∀ j, {i | cut i ≤ j}.Finite) (a b n : ℕ)
    (ha : {i | tag i=a}.Infinite) (hb : {i | tag i=b}.Infinite) :
    spaceType (PacketSum (fun i => TagRow (tag i) (cut i))) + spaceType (TagRow a n) =
    spaceType (PacketSum (fun i => TagRow (tag i) (cut i))) + spaceType (TagRow b n) := by
  obtain ⟨src,hs⟩ := extend_fiber_equiv tag a ha
  obtain ⟨dst,hd⟩ := extend_fiber_equiv tag b hb
  let f := src.trans dst.symm
  let k := extendLabel cut n
  have tags (j : Option I) : extendLabel tag b (f j) = extendLabel tag a j := by
    rw [← hd,show dst (f j) = src j from dst.apply_symm_apply _,hs]
  have fin (j : ℕ) : {p | k p ≤ j}.Finite := by
    apply (((finite j).image some).insert none).subset
    rintro (_|i) hi
    · exact Or.inl rfl
    · exact Or.inr ⟨i,hi,rfl⟩
  obtain ⟨h⟩ := match_row_arrays (extendLabel tag a) k (k ∘ f) fin
    (fun j => (fin j).preimage f.injective.injOn) (fun j => congrArg ENat.toNat
      (encard_preimage_of_bijective f.bijective {p | k p ≤ j}).symm)
  have sameTag (u v l : ℕ) (eq : u=v) : TagRow u l ≃ₜ TagRow v l := by subst v; exact Homeomorph.refl _
  let move := sigmaFamilyCongr (X := fun j => TagRow (extendLabel tag a j) (k (f j)))
    (Y := fun j => TagRow (extendLabel tag b j) (k j)) f (fun j => sameTag _ _ _ (tags j).symm)
  apply (spaceType_eq_iff _ _).mpr
  exact ⟨((extend_row_chart tag cut a n).trans (h.trans move).onePointCongr).trans (extend_row_chart tag cut b n).symm⟩

theorem infinite_retained_tag {S : Set ℕ} (C : Clopens (VertexChart S)) (center : ∞ ∈ C)
    {e : ℕ} (he : e ∈ S) : {r : retainedRows C | r.val.1.val=e}.Infinite := by
  obtain ⟨F,out⟩ := cofinite_components_of_nhds (C.isClopen.isOpen.mem_nhds center)
  have inf := ((infinity_of_tag_rows S e).mpr he).sdiff F.finite_toSet

  intro fin
  apply inf
  apply ((finite_image_iff (f := Subtype.val) Subtype.val_injective.injOn).mpr fin).subset
  rintro r ⟨tag,good⟩
  exact ⟨⟨r,out r good ∞⟩,tag,rfl⟩

theorem vertex_row_exchange {S : Set ℕ} (C : Clopens (VertexChart S)) (center : ∞ ∈ C) {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (n : ℕ) :
    spaceType C + spaceType (TagRow a n) = spaceType C + spaceType (TagRow b n) := by
  classical
  let := (chart_stone S).1
  obtain ⟨d⟩ := chart_tail_spec C
  have eq := exchange_rows (fun r : retainedRows C => r.val.1.val) d.cut d.finite_cut a b n
    (infinite_retained_tag C center ha) (infinite_retained_tag C center hb)
  have core := d.core_type
  rw [show decide (∞ ∈ C) = true from decide_eq_true center] at core
  rw [split_subclopen d.core_subset,core]
  calc
    _ = (spaceType (PacketSum (fun r : retainedRows C => TagRow r.val.1.val (d.cut r))) + spaceType (TagRow a n)) +
          spaceType (C \ d.core : Clopens (VertexChart S)) := by ac_rfl
    _ = _ := by rw [eq]; ac_rfl

end BooleanScott
