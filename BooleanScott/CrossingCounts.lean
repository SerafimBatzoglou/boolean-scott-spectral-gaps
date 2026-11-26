module
public import BooleanScott.ShiftedSectors
public import BooleanScott.Conservation

/-! The signed counts in two crossing sectors form one finitely supported
integer vector. Its total is forced by the eventual ledger counts in the
differences and by finite cancellation in their common clopen. -/
@[expose] public section
namespace BooleanScott
open Set Filter TopologicalSpace Descriptive
open scoped Classical

def pointsInside {X : Type} [TopologicalSpace X] (P : LocalLocus) (C : Clopens X) : Set (P.points X) :=
  {x | x.val ∈ C}

theorem pointsInside_count {X : Type} [TopologicalSpace X] (P : LocalLocus) (C : Clopens X) :
    (pointsInside P C).encard = P.count (spaceType C) := by
  rw [P.count_clopen,← (Subtype.val_injective (p := fun x => x ∈ P.points X)).encard_image]
  exact congrArg Set.encard (show Subtype.val '' pointsInside P C = (C : Set X) ∩ P.points X from
    Set.ext (fun x => ⟨fun ⟨y,hy,eq⟩ => eq ▸ ⟨hy,y.property⟩,fun ⟨hc,hp⟩ => ⟨⟨x,hp⟩,hc,rfl⟩⟩))

theorem signed_root_count {X : Type} [TopologicalSpace X] (A B : Clopens X) (e m n : ℕ)
    (ha : (tagRoot e).count (spaceType (A \ B : Clopens X)) = (m : ℕ∞))
    (hb : (tagRoot e).count (spaceType (B \ A : Clopens X)) = (n : ℕ∞)) :
    netChange (pointsInside (tagRoot e) A) (pointsInside (tagRoot e) B) = (m : ℤ) - n := by
  change ((pointsInside (tagRoot e) (A \ B)).ncard : ℤ) - (pointsInside (tagRoot e) (B \ A)).ncard = _
  rw [ncard_def,ncard_def,pointsInside_count,pointsInside_count,ha,hb,ENat.toNat_natCast,ENat.toNat_natCast]

theorem finite_root_differences {X : Type} [TopologicalSpace X] (A B : Clopens X)
    (hA : HasLedgerBalance (spaceType (A \ B : Clopens X))) (hB : HasLedgerBalance (spaceType (B \ A : Clopens X))) (e : ℕ) :
    (differenceSupport (pointsInside (tagRoot e) A) (pointsInside (tagRoot e) B)).Finite := by
  obtain ⟨a,ha,_⟩ := hA
  obtain ⟨b,hb,_⟩ := hB
  exact (finite_of_encard_eq_coe ((pointsInside_count (tagRoot e) (A \ B)).trans (ha e))).union
    (finite_of_encard_eq_coe ((pointsInside_count (tagRoot e) (B \ A)).trans (hb e)))

theorem count_split {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (P : LocalLocus) (A B : Clopens X) : P.count (spaceType A) =
    P.count (spaceType (A \ B : Clopens X)) + P.count (spaceType (A ⊓ B : Clopens X)) := by
  have cut : (A \ B) ⊔ (A ⊓ B) = A := by
    ext x
    change (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∈ B) ↔ x ∈ A
    tauto
  have apart : Disjoint ((A \ B : Clopens X) : Set X) ((A ⊓ B : Clopens X) : Set X) :=
    Set.disjoint_left.mpr (fun _ x y => x.2 y.2)
  have h := congrArg (fun V : Clopens X => P.count (spaceType V)) cut.symm
  exact h.trans ((congrArg P.count (clopen_sup_type _ _ apart)).trans (map_add ..))

noncomputable def liftCounts : (ℕ →₀ ℕ) →+ (ℕ →₀ ℤ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

theorem rootTotal_lift (a : ℕ →₀ ℕ) : rootTotal (liftCounts a) = (rootTotal a : ℕ) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg,Nat.cast_add]
  | single i n =>
    change rootTotal (Finsupp.mapRange (Nat.castAddMonoidHom ℤ) (map_zero _) (Finsupp.single i n)) = _
    rw [Finsupp.mapRange_single]
    simp [rootTotal]

theorem crossing_balance {T : tree ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : GuardData T X} {v : Vertex} (A B : Sector G v) (δ : ℕ)
    (changeCount : ∀ j, (privateLocus (2*j)).count (spaceType A.region) =
      (privateLocus (2*j)).count (spaceType B.region) + (δ : ℕ∞)) :
    ∃ d : ℕ →₀ ℤ, (∀ e, d e = netChange (pointsInside (tagRoot e) A.region) (pointsInside (tagRoot e) B.region)) ∧
      rootTotal d = (δ : ℤ) := by
  obtain ⟨a,tagA,lateA⟩ := A.balance (A.region \ B.region) sdiff_le (fun h => h.2 B.center)
  obtain ⟨b,tagB,lateB⟩ := B.balance (B.region \ A.region) sdiff_le (fun h => h.2 A.center)
  refine ⟨liftCounts a - liftCounts b,fun e => (signed_root_count _ _ _ _ _ (tagA e) (tagB e)).symm,?_⟩
  obtain ⟨j,aj,bj⟩ := (lateA.and lateB).exists
  let P := privateLocus (2*j)
  have sa := count_split P A.region B.region
  have sb := count_split P B.region A.region
  rw [inf_comm B.region A.region] at sb
  obtain ⟨m,hm⟩ := B.finite_ledger j
  have bounded : P.count (spaceType (A.region ⊓ B.region : Clopens X)) ≠ ⊤ := by
    intro top
    rw [top,add_top,hm] at sb
    exact ENat.natCast_ne_top _ sb
  obtain ⟨z,hz⟩ := ENat.ne_top_iff_exists.mp bounded
  have eq := changeCount j
  change P.count (spaceType A.region) = P.count (spaceType B.region) + (δ : ℕ∞) at eq
  rw [sa,sb,aj,bj,← hz] at eq
  have arithmetic : (rootTotal a : ℕ)+z = (rootTotal b : ℕ)+z+δ := by exact_mod_cast eq
  rw [map_sub,rootTotal_lift,rootTotal_lift]
  omega

end BooleanScott
