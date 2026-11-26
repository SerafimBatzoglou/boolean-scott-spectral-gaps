module
public import BooleanScott.GuardGeometry
public import BooleanScott.StoneTests

/-! The named anchor clauses, local reserve copies, and finite-or-cofinite
anchor tests in pure Boolean syntax. The ordinals are uniform over a
countable family even when the finite ranks of its individual tags grow. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal Descriptive
open scoped Ordinal Classical

def anchorOf (t : TagName) := tagAnchor (tagNumber t)
def vertexLocus (v : Vertex) := anchorOf (.inl v)

theorem anchor_closed (t : TagName) : ClosedLocus (anchorOf t) :=
  fun X _ _ _ _ => isClosed_derivedSet (derivedSet (privateMark X _))

def Hits (P : LocalLocus) : StonePredicate 1 :=
  fun X _ u => ((u 0 : Set X) ∩ P.points X).Nonempty

theorem FiniteHit.incidence {P : LocalLocus} (h : FiniteHit P) : FiniteTest (Hits P) := by
  obtain ⟨k,φ,pos,lev,t⟩ := h
  refine ⟨k,pos,φ,lev,fun X _ _ _ _ _ v => ?_⟩
  have eq : v = (fun _ => v 0) := funext fun i => congrArg v (Subsingleton.elim i 0)
  exact eq ▸ t X (v 0)

theorem FiniteHit.emptyTest {P : LocalLocus} (h : FiniteHit P) :
    FiniteTest (n := 0) (fun X _ _ => P.points X = ∅) := by
  apply ((h.incidence.substitute (fun _ : Fin 1 => (.one : Term 0))).neg).congr
  intro X _ _ _ _ _ v
  change ¬ ((univ : Set X) ∩ P.points X).Nonempty ↔ _
  rw [univ_inter,not_nonempty_iff_eq_empty]

theorem FiniteHit.globalThreshold {P : LocalLocus} (h : FiniteHit P) (a : ℕ) :
    FiniteTest (n := 0) (fun X _ _ => (a : ℕ∞) ≤ (P.points X).encard) := by
  obtain ⟨k,f⟩ := count_thresholds h
  obtain ⟨φ,hφ,t⟩ := f a
  obtain ⟨ψ,hψ,s⟩ := sigma_as_pi hφ
  refine ⟨k+1,by omega,ψ.substitute (fun _ => .one),by simpa using hψ.substitute (fun _ => (.one : Term 0)),
    fun X _ _ _ _ _ v => ?_⟩
  rw [Formula.holds_substitute,s]
  exact (t X ⊤).trans (by rw [P.count_clopen]; simp)

theorem one_iff_thresholds (a : ℕ∞) : (1 ≤ a ∧ ¬ 2 ≤ a) ↔ a=1 := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n =>
    change ((1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) ∧ ¬ ((2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) ↔ (n : ℕ∞) = ((1 : ℕ) : ℕ∞)
    simp only [Nat.cast_le,Nat.cast_inj]
    omega

theorem singleton_test (t : TagName) : FiniteTest (n := 0) (fun X _ _ => ∃ x, (anchorOf t).points X = {x}) := by
  have h := tagAnchor_finiteHit (tagNumber t)
  apply ((h.globalThreshold 1).and (h.globalThreshold 2).neg).congr
  intro X _ _ _ _ _ v
  exact (one_iff_thresholds _).trans encard_eq_one

theorem different_test (v w : Vertex) : FiniteTest (n := 0) (fun X _ _ =>
    ((vertexLocus v).points X ∩ (vertexLocus w).points X) = ∅) :=
  (finiteHit_closed_intersection (tagAnchor_finiteHit _) (tagAnchor_finiteHit _)
    (anchor_closed (.inl v)) (anchor_closed (.inl w))).emptyTest

theorem endpoint_test (v : Vertex) (i : ℕ) : FiniteTest (n := 0) (fun X _ _ =>
    (anchorOf (.inr (v,i))).points X ⊆ (vertexLocus v).points X ∪ (vertexLocus (v++[i])).points X) := by
  let t := anchorOf (.inr (v,i))
  have h : FiniteHit (t.difference (vertexLocus v)) :=
    finiteHit_difference (tagAnchor_finiteHit _) (tagAnchor_finiteHit _) (anchor_closed _)
  apply (finiteHit_difference h (tagAnchor_finiteHit _) (anchor_closed (.inl (v++[i])))).emptyTest.congr
  intro X _ _ _ _ _ u
  change (t.points X \ (vertexLocus v).points X) \ (vertexLocus (v++[i])).points X = ∅ ↔ _
  rw [eq_empty_iff_forall_notMem]
  change (∀ x, ¬ ((x ∈ t.points X ∧ x ∉ _) ∧ x ∉ _)) ↔ ∀ ⦃x⦄, x ∈ t.points X → x ∈ _ ∨ x ∈ _
  constructor
  · intro h x hx
    by_contra! out
    exact h x ⟨⟨hx,out.1⟩,out.2⟩
  · intro h x hx
    exact (h hx.1.1).elim hx.1.2 hx.2

def NamedClopen (Y : Type) [TopologicalSpace Y] : StonePredicate 1 :=
  fun _ _ u => Nonempty (Y ≃ₜ u 0)

theorem namedClopen_test {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [ZeroDimensionalSpace Y] {σ : Formula 0} {α : Ordinal.{0}} (lev : AtLevel .pi α σ)
    (isolate : ∀ (B : Type) [Countable B] [BooleanAlgebra B], Models (BoolOps.ofAlgebra B) σ ↔ Nonempty (Clopens Y ≃o B)) :
    StoneDef .pi α (NamedClopen Y) := by
  refine ⟨σ.relative 0 Fin.elim0,lev.relative _ _,fun X _ _ _ _ _ u => ?_⟩
  let C := u 0
  have eq : u = (fun _ => C) := funext fun i => congrArg u (Subsingleton.elim i 0)
  apply (show (σ.relative 0 Fin.elim0).Holds _ u ↔ Models (BoolOps.ofAlgebra (Clopens C)) σ from eq ▸ relative_models_clopen C lev).trans
  let := (clopenRestriction C).surjective.countable
  let := clopen_compactSpace C
  exact (isolate (Clopens C)).trans ⟨fun ⟨e⟩ => ⟨homeomorphOfClopens e⟩,fun ⟨g⟩ => ⟨clopensOfHomeomorph g⟩⟩

def ReserveCopy (j : ℕ) : StonePredicate 1 :=
  fun X _ u => ∃ D : Clopens X, D ≤ u 0 ∧ Nonempty (Mixed (2*j) ≃ₜ D)

theorem reserveCopy_test (j : ℕ) : FiniteTest (ReserveCopy j) := by
  obtain ⟨ht,hz,_⟩ := mixed_stone (2*j)
  obtain ⟨k,σ,lev,iso⟩ := mixed_finite_scott (2*j)
  have named := namedClopen_test lev iso
  obtain ⟨φ,l,t⟩ := named.raise (lt_add_one _).le
  obtain ⟨ψ,hψ,s⟩ := below_formula l (by positivity)
  refine ⟨k+1+1+1,by omega,ψ,by simpa using hψ,fun X _ _ _ _ _ u => ?_⟩
  have eq : u = (fun _ => u 0) := funext fun i => congrArg u (Subsingleton.elim i 0)
  exact (show ψ.Holds _ u ↔ _ from eq ▸ s (Clopens X) (u 0)).trans
    (exists_congr (fun D => and_congr_right (fun _ => t X (fun _ => D))))

def FiniteAnchors : StonePredicate 1 := fun X _ u => {v : Vertex | Hits (vertexLocus v) X u}.Finite

theorem finiteAnchors_test : StoneDef .sigma (ω+1) FiniteAnchors := by
  let misses (F : Finset Vertex) (w : {v : Vertex // v ∉ F}) : StonePredicate 1 :=
    fun X _ u => ¬ Hits (vertexLocus w.val) X u
  have each (F : Finset Vertex) (w : {v : Vertex // v ∉ F}) : StoneDef .pi ω (misses F w) :=
    (FiniteTest.neg (FiniteHit.incidence (tagAnchor_finiteHit _))).piOmega
  have all (F : Finset Vertex) := StoneDef.allOf (R := misses F) omega0_pos (each F)
  apply (StoneDef.anyOf all).congr
  intro X _ _ _ _ _ u
  constructor
  · rintro ⟨F,hF⟩
    apply F.finite_toSet.subset
    intro v hv
    by_contra out
    exact hF ⟨v,out⟩ hv
  · intro h
    exact ⟨h.toFinset,fun ⟨v,out⟩ hv => out (h.mem_toFinset.mpr hv)⟩

end BooleanScott
